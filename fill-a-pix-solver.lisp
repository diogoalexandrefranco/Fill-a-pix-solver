(LOAD "exemplos.fas")

;;; ESTRUTURAS ;;;


;Estrutura que define uma restricao
(defstruct (restricao
    (:constructor cria-restricao (variaveis funcao-validacao)))
  variaveis
  funcao-validacao)

;Estrutura que define um PSR
(defstruct (psr
    (:constructor cria-psr (variaveis dominios restricoes 
      &aux (atr-hash (make-hash-table :test 'equal :size (length variaveis)))
      (variaveis-n-atribuidas variaveis)
      (dominios-hash (make-hash-table :test 'equal :size (length variaveis)))
      (envolvidas-hash (make-hash-table :test 'equal :size (length variaveis))))))
 
  variaveis                    ;lista de variaveis
  dominios                     ;lista de dominios
  restricoes                   ;lista de restricoes
  atr-hash                     ;hash-table com as atribuicoes
  variaveis-n-atribuidas       ;lista de variaveis nao atribuidas. esta lista apenas e usada para a funcao resolve-best
  dominios-hash                ;hash-table utilizada no resolve-best para guardar os dominios das variaveis
  envolvidas-hash)             ;hash-table utilizada no resolve-best para guardar informacao sobre variaveis envolvidas umas com as outras
    

;Funcao que dado um psr e uma variavel retorna o valor correspondente
(defun psr-variavel-valor (psr variavel)
  (values (gethash variavel (psr-atr-hash psr))))

;Funcao que retorna uma lista de pares. Cada par corresponde a uma variavel e o seu
;valor correspondente no psr, (caso seja diferente de nil)
(defun psr-atribuicoes (psr)
  (let (atribuicoes)
  (dolist (variavel (psr-variaveis-todas psr) atribuicoes)
    (if (psr-variavel-valor psr variavel)
      (setq atribuicoes (cons (cons variavel (psr-variavel-valor psr variavel)) atribuicoes))))
  (reverse atribuicoes)))

;Funcao que retorna uma lista com todas as variaveis do psr
(defun psr-variaveis-todas (psr)
  (psr-variaveis psr))

;Funcao que retorna uma lista com as variaveis nao atribuidas do psr
(defun psr-variaveis-nao-atribuidas (psr)
 (let (nao-atribuicoes)
  (dolist (variavel (psr-variaveis-todas psr) nao-atribuicoes)
    (if (not (psr-variavel-valor psr variavel))
      (setq nao-atribuicoes (cons variavel nao-atribuicoes))))
  (reverse nao-atribuicoes))) ;deve respeitar a ordem da lista variaveis, ao contrario da funcao psr-atribuicoes

;Funcao que dado um psr e uma variavel retorna o dominio correspondente a essa variavel
(defun psr-variavel-dominio (psr variavel)
  (nth (position variavel (psr-variaveis-todas psr) :test #'equal) (psr-dominios psr)))

;Versao da funcao psr-variavel-dominio que utiliza a hash table de dominios, usada no resolve-best
(defun psr-variavel-dominio-best (psr variavel)
  (gethash variavel (psr-dominios-hash psr)))

;Funcao que dado um psr e uma variavel retorna o conjunto de restricoes correspondentes a essa variavel
(defun psr-variavel-restricoes (psr variavel)     
   (loop for i in (psr-restricoes psr)
   if(member variavel (restricao-variaveis i) :test #'equal)
   collect i))

;Funcao auxiliar que dado um psr e duas variaveis, retorna o conjunto de restricoes nas quais as duas
;variaveis estao simultaneamente envolvidas
(defun psr-variaveis-restricoes-aux (psr variavel1 variavel2)     
   (loop for i in (psr-restricoes psr)
   if(and (member variavel1 (restricao-variaveis i) :test #'equal) 
    (member variavel2 (restricao-variaveis i) :test #'equal))
   collect i))    

;Funcao que dado um psr, uma variavel e um valor, atribui o valor a essa variavel
(defun psr-adiciona-atribuicao! (psr variavel valor)
  (setf (gethash variavel (psr-atr-hash psr)) valor))

;Funcao que dado um psr e uma variavel, remove a atribuicao correspondente a essa variavel
(defun psr-remove-atribuicao! (psr variavel)
  (remhash variavel (psr-atr-hash psr)))

;Funcao que dado um psr, uma variavel e um dominio, altera o dominio da variavel para dominio
;fornecido como argumento
(defun psr-altera-dominio! (psr variavel dominio)
  (setf 
  (nth (position variavel (psr-variaveis-todas psr) :test #'equal) (psr-dominios psr)) dominio))

;Versao da funcao psr-altera-dominio! que utilizada a hash-table de dominios, usada no resolve-best
(defun psr-altera-dominio-best! (psr variavel dominio)
  (setf (gethash variavel (psr-dominios-hash psr)) dominio)) 

;Funcao que verifica se o psr e completo. Se sim retorna T, retornando nil caso contrario
(defun psr-completo-p (psr)
  (if (psr-variaveis-nao-atribuidas psr)
   NIL
   T))

;Funcao que verifica se o psr e consistente. Retorna T ou nil, consoante a consistencia
;bem como o numero de testes de consistencia efectuados.
(defun psr-consistente-p (psr)
  (let ((ntests 0)
		(consistencia t))
	(dolist (res (psr-restricoes psr))
	(incf ntests)
	(if (not (funcall (restricao-funcao-validacao res) psr))
		(progn (setq consistencia nil)(return))))
  (values consistencia ntests)))

;Funcao que dado um psr e uma variavel verifica se essa variavel e consistente, dadas as suas restricoes
(defun psr-variavel-consistente-p (psr variavel)
  (let ((ntests 0)
		(consistencia t))
	(dolist (res (psr-variavel-restricoes psr variavel))
	(incf ntests) 
	(if (not (funcall (restricao-funcao-validacao res) psr))
		(progn (setq consistencia nil) (return))))
  (values consistencia ntests)))

;Funcao que dado um psr, uma variavel e um valor, ira atribuir esse valor a variavel e, seguidamente,
;verificar a consistencia dessa variavel. Por fim, a atribuicao e removida, deixando o psr no seu estado original
(defun psr-atribuicao-consistente-p (psr variavel valor)
  (let ((valor-antigo (psr-variavel-valor psr variavel))
		(valor-existe nil)
		(consistencia) 
		(ntests))
	(if valor-antigo
		(setq valor-existe t))
	(psr-adiciona-atribuicao! psr variavel valor)
	(multiple-value-setq (consistencia ntests) (psr-variavel-consistente-p psr variavel))
	(psr-remove-atribuicao! psr variavel)
	(if valor-existe
		(psr-adiciona-atribuicao! psr variavel valor-antigo))
  (values consistencia ntests)))

;Funcao que dado um psr, duas variaveis e 2 valores, ira tentar a consistencia dessas duas atribuicoes em arco
(defun psr-atribuicoes-consistentes-arco-p(psr variavel1 valor1 variavel2 valor2)
  (let ((valor-antigo1 (psr-variavel-valor psr variavel1))
		(valor-antigo2 (psr-variavel-valor psr variavel2))
		(valor-existe1 nil)
		(valor-existe2 nil)
		(consistencia t) 
		(ntests 0))

	;flags de estado para saber se as vars tem um valor		
	(if valor-antigo1
		(setq valor-existe1 t))

	(if valor-antigo2
		(setq valor-existe2 t))

    ;adiciona as atribuicoes ao psr
    (psr-adiciona-atribuicao! psr variavel1 valor1)
    (psr-adiciona-atribuicao! psr variavel2 valor2)

    (dolist (res (psr-variavel-restricoes psr variavel1))
      (if(member variavel2 (restricao-variaveis res) :test #'equal)
        (progn 
          (incf ntests)
          (if (not (funcall (restricao-funcao-validacao res) psr))
            (progn
              (setf consistencia nil)
              (return))))))

    ;remove as atribuicoes, repoe as restricoes todas ao psr
    (psr-remove-atribuicao! psr variavel1)
    (psr-remove-atribuicao! psr variavel2)
    
    (if valor-existe1
		(psr-adiciona-atribuicao! psr variavel1 valor-antigo1))

    (if valor-existe2
		(psr-adiciona-atribuicao! psr variavel2 valor-antigo2))
  
    (values consistencia ntests)))

;Funcao auxiliar para a conversao de um problema fill-a-pix para psr.
;dado um tabuleiro fill-a-pix, esta funcao ira criar as funcoes de validacao usadas pelas restricoes
(defun cria-funcao-validacao-aux (i j nr-colunas nr-linhas tabuleiro-array lista-variaveis)
  (let ((num-casas)
    (i i)
    (j j))
  ; encontra numero de casas 
  (cond ((and (or (equal i 0) (equal i (- nr-linhas 1))) 
			  (or (equal j 0) (equal j (- nr-colunas 1))))
		(setf num-casas 4))	
	   ((or (or (equal i 0) (equal i (- nr-linhas 1)))
			(or (equal j 0) (equal j (- nr-colunas 1))))
		(setf num-casas 6))	
	   (t (setf num-casas 9)))

  #'(lambda (psr) 
  (let ((num-pretas 0)
		(num-brancas 0))
			(loop for v in lista-variaveis do
						(cond ((equal 0 (psr-variavel-valor psr v)) 
							   (incf num-brancas))
							  ((equal 1 (psr-variavel-valor psr v)) 
							   (incf num-pretas))))
	(if (or(> num-brancas (- num-casas (aref tabuleiro-array i j)))
    (> num-pretas (aref tabuleiro-array i j)))
		nil
		T)))))

;Funcao auxiliar para a conversao de um problema fill-a-pix para psr.
;dado um tabuleiro fill-a-pix, esta funcao ira criar as listas de variaveis usadas para a 
;criacao das restricoes do psr.
(defun cria-lista-variaveis-restricao-aux (i j nr-colunas nr-linhas)
  (let ((lista-variaveis nil))
	  (loop for k from (- i 1) to (+ i 1) do
      (loop for m from (- j 1) to (+ j 1) do
        (if (and (>= k 0) (< k nr-linhas) 
          (>= m 0) (< m nr-colunas))
      (setf lista-variaveis (cons (+ (* k nr-colunas) m) lista-variaveis)))))
   lista-variaveis))

;Funcao que recebe um array fill-a-pix e devolve o psr correspondente.
;Usa as funcoes auxiliares definidas anteriormente, de modo a criar as restricoes do psr
(defun fill-a-pix->psr (tabuleiro-array)
  (let ((nr-linhas (first (array-dimensions tabuleiro-array)))
		(nr-colunas (first (rest (array-dimensions tabuleiro-array))))
		(variaveis) 
		(dominios)
		(lista-restricoes)
    (variaveis-restricao))
    (loop for i from 0 to (- nr-linhas 1) do
      (loop for j from 0 to (- nr-colunas 1) do
        (setf variaveis (cons (+ (* i nr-colunas) j) variaveis))
        (setf dominios (cons (list 0 1) dominios))
        (if (aref tabuleiro-array i j)
          (progn
            (setf variaveis-restricao 
              (cria-lista-variaveis-restricao-aux i j nr-colunas nr-linhas))
            (setf lista-restricoes (cons (cria-restricao variaveis-restricao
             (cria-funcao-validacao-aux i j nr-colunas nr-linhas tabuleiro-array variaveis-restricao))
             lista-restricoes))))))
      (cria-psr (reverse variaveis) (reverse dominios) (reverse lista-restricoes))))

(defun fill-a-pix->psr-best (tabuleiro-array)
  (let ((nr-linhas (first (array-dimensions tabuleiro-array)))
    (nr-colunas (first (rest (array-dimensions tabuleiro-array))))
    (variaveis) 
    (dominios)
    (lista-restricoes)
    (variaveis-restricao))
    (loop for i from 0 to (- nr-linhas 1) do
      (loop for j from 0 to (- nr-colunas 1) do
        (setf variaveis (cons (+ (* i nr-colunas) j) variaveis))
        (setf dominios (cons (list 0 1) dominios))
        (if (aref tabuleiro-array i j)
          (progn
            (setf variaveis-restricao 
              (cria-lista-variaveis-restricao-aux i j nr-colunas nr-linhas))
            (setf lista-restricoes (cons (cria-restricao variaveis-restricao
             (cria-funcao-validacao-aux i j nr-colunas nr-linhas tabuleiro-array variaveis-restricao))
             lista-restricoes))))))
      (cria-psr (reverse variaveis) dominios (reverse lista-restricoes))))

;Funcao que recebe um psr e devolve um tabuleiro fill-a-pix representando as atribuicoes do psr
(defun psr->fill-a-pix (psr l c)
  (let ((lista-atribuicoes)
    (lista-colunas)
    (var))
  (loop for i from 0 to (- l 1) do
	(setf lista-colunas nil)
	(loop for j from 0 to (- c 1) do
		(setf var (+ (* i c) j))
		(setf lista-colunas (cons (psr-variavel-valor psr var) lista-colunas)))
	(setf lista-atribuicoes (cons (reverse lista-colunas) lista-atribuicoes)))
  (make-array (list l c) :initial-contents (reverse lista-atribuicoes))))

;Procura cega com retrocesso. Nao utiliza qualquer heuristica ou mecanismo de inferencia
(defun procura-retrocesso-simples(psr)
  (let ((count 0)
		(var)
		(result_psr)
		(result_count)
		(consistency))
	(if (psr-completo-p psr)
		(return-from procura-retrocesso-simples (values psr count))
	(progn
		(setq var (first (psr-variaveis-nao-atribuidas psr)))
		(dolist (val (psr-variavel-dominio psr var))
			(multiple-value-setq (consistency result_count) 
			(psr-atribuicao-consistente-p psr var val))
			(setq count (+ count result_count))
			(if consistency
				(progn 
					(psr-adiciona-atribuicao! psr var val)
					(multiple-value-setq (result_psr result_count) (procura-retrocesso-simples psr))
					(setq count (+ count result_count))
					(if result_psr
						(return-from procura-retrocesso-simples (values result_psr count))
					(psr-remove-atribuicao! psr var)))))))
 (return-from procura-retrocesso-simples (values nil count))))

;Funcao que recebe um array fill-a-pix e tenta resolve-lo utilizando uma procura cega com retrocesso.
;Em primeiro lugar, o array sera convertido para psr recorrendo a funcao fill-a-pix->psr.
;Em segundo lugar, a funcao ira efectuar uma procura cega com retrocesso.
;Caso seja encontrada uma solucao, o psr correspondente sera convertido num array com a funcao psr->fill-a-pix.
;Caso nao seja encontrada uma solucao, e retornado nil. 
(defun resolve-simples(array)
(let ((nlinhas (first (array-dimensions array)))
	  (ncolunas (nth 1 (array-dimensions array)))
	  (psr-resolvido))

  (setq psr-resolvido (procura-retrocesso-simples (fill-a-pix->psr array)))
  (if psr-resolvido
	(psr->fill-a-pix psr-resolvido nlinhas ncolunas)
     nil)))


;Funcao que dado um psr, devolve uma variavel segundo a heuristica do maior grau.
;Ou seja, e devolvida a variavel nao atribuida que esteja envolvida no maior numero de restricoes
(defun psr-variavel-livre-maior-graux-aux(psr)
  (let ((lista-variaveis-grau)
		(grau))
	(dolist (var (psr-variaveis-nao-atribuidas psr))
		(setf grau (grau-de-variavel psr var))
		(setf lista-variaveis-grau (cons (cons var grau) lista-variaveis-grau)))
	(setf lista-variaveis-grau (sort lista-variaveis-grau #'list-sort-aux))
	(first (first lista-variaveis-grau))))

;Procura com retrocesso, utilizando a heuristica do maior grau como criterio de selecao da proxima variavel a ser atribuida
(defun procura-retrocesso-grau(psr)
  (let ((count 0)
		(var)
		(result_psr)
		(result_count)
		(consistency))
	(if (psr-completo-p psr)
		(return-from procura-retrocesso-grau (values psr count))
	(progn
		(setq var (psr-variavel-livre-maior-graux-aux psr))
		(dolist (val (psr-variavel-dominio psr var))
			(multiple-value-setq (consistency result_count) 
			(psr-atribuicao-consistente-p psr var val))
			(setq count (+ count result_count))
			(if consistency
				(progn 
					(psr-adiciona-atribuicao! psr var val)
					(multiple-value-setq (result_psr result_count)
					(procura-retrocesso-grau psr))
					(setq count (+ count result_count))
					(if result_psr
						(return-from procura-retrocesso-grau (values result_psr count))
						(psr-remove-atribuicao! psr var)))))))
 (return-from procura-retrocesso-grau (values nil count))))

;Funcao auxiliar que sera usada como comparador para ordenar as listas de grau
(defun list-sort-aux (a b)
  (cond ((null a) (not (null b)))
        ((null b) nil)
        ((< (rest a) (rest b)) nil)
        ((> (rest a) (rest b)) t)
        (t t)))


;Funcao que devolve o nr de restricoes em que var esta envolvido
;com outras variaveis nao atribuidas
(defun grau-de-variavel (psr var)
  (let ((grau 0)
		(deve-incrementar-grau))
	  (dolist (r (psr-variavel-restricoes psr var))
		(setf deve-incrementar-grau nil)
		(dolist (v (restricao-variaveis r))
		  (if (and (not (equal v var))
			(not (psr-variavel-valor psr v)))
		  (progn 
			(setf deve-incrementar-grau t)
			(return))))
		(if deve-incrementar-grau
		  (incf grau)))
	  grau))

;Heuristica minimum remaining values.
;escolhe a variavel com o dominio mais pequeno, em caso de empate,
;escolhe a variavel que aparece primeiro na lista de variaveis nao atribuidas
(defun MRV (psr)
  (let ((selected-var)
		(dominio-mais-pequeno nil)
		(tamanho-dominio)
		(variaveis-livres (psr-variaveis-nao-atribuidas psr)))
    (setf dominio-mais-pequeno (length (psr-variavel-dominio psr (first variaveis-livres))))
    (setf selected-var (first variaveis-livres))
    (dolist (var variaveis-livres)
      (setf tamanho-dominio (length (psr-variavel-dominio psr var)))
      (if (< tamanho-dominio dominio-mais-pequeno)
        (progn 
          (setf dominio-mais-pequeno tamanho-dominio)
          (setf selected-var var))))
    selected-var))
		
;devolve T se v1 e v2 estiverem envolvidas em alguma restricao, nil caso contrario
(defun envolvidas-em-restricao (psr v1 v2)
   (dolist (r (psr-variavel-restricoes psr v2)) 
     (dolist (v (restricao-variaveis r)) 
       (if (equal v v1)  
         (return-from envolvidas-em-restricao T)))) 
   nil) 

;retorna uma lista de arcos (sem arcos repetidos)
;que correspondem as variaveis ainda nao atribuidas que estao 
;envolvidas numa restricao com var 
(defun arcos-vizinhos-nao-atribuidos (psr var)
  (let ((vars-nao-atribuidas (psr-variaveis-nao-atribuidas psr)) 
		(lista-de-arcos))
    (dolist (v vars-nao-atribuidas)
      (if (not (equal v var))
        (if (envolvidas-em-restricao psr v var)
          (setf lista-de-arcos (cons (cons v var) lista-de-arcos)))))
    (reverse lista-de-arcos)))

;Funcao que dado um psr, duas variaveis e um conjunto de inferencias,
;ira continuar o processo de inferencias, atraves de atribuicoes consistentes em arco.
;Retorna o numero de testes de consistencia efectuados bem como um booleano que sera T caso
;algum dominio tenha sido alterado e nil caso contrario.
(defun revise (psr x y inferencias)
  (let ((testesTotais 0)
		(testes 0)
		(consistency)
		(revised nil)
		(dominio-x)
		(novo-dominio-x)
		(dominio-y)
		(foundConsistentValue))

    (if (gethash x inferencias)
      (setf dominio-x (gethash x inferencias))
      (setf dominio-x (psr-variavel-dominio psr x)))
    (setf novo-dominio-x dominio-x)
    (if (psr-variavel-valor psr y)
      (setf dominio-y (list (psr-variavel-valor psr y)))
      (if (gethash y inferencias)
        (setf dominio-y (gethash y inferencias))
        (setf dominio-y (psr-variavel-dominio psr y))))
    (dolist (vx dominio-x)
      (setf foundConsistentValue nil)
      (dolist (vy dominio-y)
        (multiple-value-setq (consistency testes)
          (psr-atribuicoes-consistentes-arco-p psr x vx y vy))
        (setf testesTotais (+ testesTotais testes))
        (if consistency
          (progn
            (setf foundConsistentValue t)
            (return))))
      (if (not foundConsistentValue)
        (progn
          (setf revised t)
          (setf novo-dominio-x (remove vx novo-dominio-x :test #'equal)))))

    (if revised
      (progn
      (setf (gethash x inferencias) novo-dominio-x)))

    (return-from revise (values revised testesTotais)))) 

;Funcao usada pela procura-retrocesso-fc-mrv.
;Recorrendo a funcao revise, ira efectuar inferencia apenas para a variavel recebido como argumento
;Retorna o conjunto de inferencias bem como o numero de testes de consistencia efectuados
(defun forward-checking (psr var)
  (let ((testesTotais 0)
		(testes 0)
		(revised)
		(inferencias (make-hash-table :test 'equal :size (length (psr-variaveis-todas psr))))
		(lista-arcos (arcos-vizinhos-nao-atribuidos psr var)))
    (loop for arco in lista-arcos do
      (multiple-value-setq (revised testes)
        (revise psr (first arco) (rest arco) inferencias))
        (setf testesTotais (+ testesTotais testes))
        (if revised
          (if (not (gethash (first arco) inferencias))
            (return-from forward-checking (values nil testesTotais))
            )))
    (return-from forward-checking (values inferencias testesTotais))))

;Funcao auxiliar que ira alterar dominios do psr de acordo com as inferencias recebidas como argumento
(defun psr-adiciona-inferencias! (psr inferencias)
  (let ((old-domains (make-hash-table :test 'equal :size (length (psr-variaveis-todas psr)))))
    (dolist (var (psr-variaveis-todas psr))
      (if (gethash var inferencias)
        (progn
          (setf (gethash var old-domains) (psr-variavel-dominio psr var))
          (psr-altera-dominio! psr var (gethash var inferencias)))))
    old-domains))

;altera os dominios do psr (versao utilizada no resolve-best, onde os dominios sao uma hash-table)
(defun psr-adiciona-inferencias-best! (psr inferencias)
  (let ((old-domains (make-hash-table :test 'equal :size (length (psr-variaveis-todas psr)))))
    (dolist (var (psr-variaveis-todas psr))
      (if (gethash var inferencias)
        (progn
          (setf (gethash var old-domains) (psr-variavel-dominio-best psr var))
          (psr-altera-dominio-best! psr var (gethash var inferencias)))))
    old-domains))

 ;coloca os dominios antigos no psr	
(defun psr-remove-inferencias! (psr old-domains)
  (dolist (var (psr-variaveis-todas psr))
    (if (gethash var old-domains)
		(psr-altera-dominio! psr var (gethash var old-domains)))))

;coloca os dominios antigos no psr (versao utilizada no resolve-best, onde os dominios sao uma hash-table)
(defun psr-remove-inferencias-best! (psr old-domains)
  (dolist (var (psr-variaveis-todas psr))
    (if (gethash var old-domains)
    (psr-altera-dominio-best! psr var (gethash var old-domains)))))

;Procura com retrocesso e forward checking que utiliza a heuristica minimum remaining values.
(defun procura-retrocesso-fc-mrv (psr)
  (let ((testesTotais 0)
		(var)
		(result_psr)
		(result_count)
		(consistency)
		(inferencias)
		(old-domains))
      (if (psr-completo-p psr)
      (return-from procura-retrocesso-fc-mrv (values psr testesTotais))
	  (progn
		(setq var (MRV psr))
		(loop for val in (psr-variavel-dominio psr var) do
		  (multiple-value-setq (consistency result_count) 
			(psr-atribuicao-consistente-p psr var val))
		  (setq testesTotais (+ testesTotais result_count))
		  (if consistency
			(progn 
		(psr-adiciona-atribuicao! psr var val)
		(multiple-value-setq (inferencias result_count)
		  (forward-checking psr var))
		(setq testesTotais (+ testesTotais result_count))
		(if inferencias
		  (progn
			(setf old-domains (psr-adiciona-inferencias! psr inferencias))
			(multiple-value-setq (result_psr result_count) 
			  (procura-retrocesso-fc-mrv psr))
			(setq testesTotais (+ testesTotais result_count))
			(if result_psr
			  (return-from procura-retrocesso-fc-mrv
				(values result_psr testesTotais)))
			(psr-remove-inferencias! psr old-domains)))
		(psr-remove-atribuicao! psr var))))))
		(return-from procura-retrocesso-fc-mrv (values nil testesTotais))))

;Funcao auxiliar que dado um par e uma lista de pares, remove todas as ocorrencia desse par na lista
(defun remove-par-de-lista (par lista)
  (if (null lista)
    ()
    (if (and (equal (first par) (first (first lista)))
      (equal (rest par) (rest (first lista))))
      (remove-par-de-lista par (rest lista))
      (cons (first lista) (remove-par-de-lista par (rest lista))))))

;Funcao auxiliar que dadas duas listas de pares, adiciona os pares da lista novos ao final de lista 
(defun adiciona-pares-a-lista (novos lista)
  (let ((result (reverse lista)))
  (loop for par in novos do
    (if (not (member par result :test #'equal))
      (setf result (cons par result))))
  (reverse result)))

;Funcao responsavel pelo processo de inferencia para a procura mac-mrv.
;Retorna o conjunto de inferencia obtidas bem como o numero de testes de consistencia efectuados.
(defun MAC (psr var)
  (let ((testesTotais 0)
    (testes 0)
    (revised)
    (inferencias (make-hash-table :test 'equal :size (length (psr-variaveis-todas psr))))
    (lista-arcos (arcos-vizinhos-nao-atribuidos psr var))
    (novos-arcos)
    (arco))
    (loop do
      (if (null lista-arcos) (return))
      (setf arco (first lista-arcos))
      (multiple-value-setq (revised testes)
        (revise psr (first arco) (rest arco) inferencias))
        (setf testesTotais (+ testesTotais testes))
        (if revised
          (progn 
            (if (not (gethash (first arco) inferencias))
            (return-from MAC (values nil testesTotais)))
            (setf novos-arcos (arcos-vizinhos-nao-atribuidos psr (first arco)))
            (setf novos-arcos (remove-par-de-lista 
              (cons (rest arco) (first arco)) novos-arcos))
            (setf lista-arcos (adiciona-pares-a-lista novos-arcos lista-arcos))))
        (setf lista-arcos (remove-par-de-lista arco lista-arcos)))
    (return-from MAC (values inferencias testesTotais))))

;Procura maintain-arc-consistencia que utiliza a heuristica minimum remaining values
(defun procura-retrocesso-mac-mrv (psr)
  (let ((testesTotais 0)(var)(result_psr)
		(result_count)(consistency)
		(inferencias)
		(old-domains))
		(if (psr-completo-p psr)
      (return-from procura-retrocesso-mac-mrv (values psr testesTotais))
  (progn
    (setq var (MRV psr))
    (dolist (val (psr-variavel-dominio psr var))
      (multiple-value-setq (consistency result_count) 
        (psr-atribuicao-consistente-p psr var val))
      (setq testesTotais (+ testesTotais result_count))
      (if consistency
        (progn 
    (psr-adiciona-atribuicao! psr var val)
    (multiple-value-setq (inferencias result_count)
      (MAC psr var))
    (setq testesTotais (+ testesTotais result_count))
    (if inferencias
      (progn
        (setf old-domains (psr-adiciona-inferencias! psr inferencias))
        (multiple-value-setq (result_psr result_count) 
          (procura-retrocesso-mac-mrv psr))
        (setq testesTotais (+ testesTotais result_count))
        (if result_psr
          (return-from procura-retrocesso-mac-mrv
            (values result_psr testesTotais)))
        (psr-remove-inferencias! psr old-domains)))
    (psr-remove-atribuicao! psr var))))))
    (return-from procura-retrocesso-mac-mrv (values nil testesTotais))))

;Funcao que recebe um array fill-a-pix e tenta resolve-lo utilizando uma procura mac optimizada. 
;Em primeiro lugar, o array sera convertido para psr recorrendo a funcao fill-a-pix->psr-best.
;Em segundo lugar, a funcao ira efectuar uma procura cega com retrocesso.
;Caso seja encontrada uma solucao, o psr correspondente sera convertido num array com a funcao psr->fill-a-pix.
(defun resolve-best (array)
	(let ((nlinhas (first (array-dimensions array)))
		  (ncolunas (nth 1 (array-dimensions array)))
		  (psr-resolvido))
     (setq psr-resolvido (procura-best (fill-a-pix->psr-best array)))
	 (if psr-resolvido
	 (psr->fill-a-pix psr-resolvido nlinhas ncolunas)
	 nil)))

;Funcao que recebe um array fill-a-pix e tenta resolve-lo utilizando uma procura com retrocesso, forward checking e com a heuristica mrv. 
;Em primeiro lugar, o array sera convertido para psr recorrendo a funcao fill-a-pix->psr.
;Em segundo lugar, a funcao ira efectuar uma procura cega com retrocesso.
;Caso seja encontrada uma solucao, o psr correspondente sera convertido num array com a funcao psr->fill-a-pix.
(defun resolve-fc-mrv (array)
	(let ((nlinhas (first (array-dimensions array)))
		  (ncolunas (nth 1 (array-dimensions array)))
	      (psr-resolvido))
	 (setq psr-resolvido (procura-retrocesso-fc-mrv (fill-a-pix->psr array)))
	 (if psr-resolvido
	 (psr->fill-a-pix psr-resolvido nlinhas ncolunas)
	 nil)))

;Funcao que recebe um array fill-a-pix e tenta resolve-lo utilizando uma procura com retrocesso, consistencia de arcos e com a heuristica mrv. 
;Em primeiro lugar, o array sera convertido para psr recorrendo a funcao fill-a-pix->psr.
;Em segundo lugar, a funcao ira efectuar uma procura cega com retrocesso.
;Caso seja encontrada uma solucao, o psr correspondente sera convertido num array com a funcao psr->fill-a-pix.
(defun resolve-mac-mrv (array)
	(let ((nlinhas (first (array-dimensions array)))
		  (ncolunas (nth 1 (array-dimensions array)))
	      (psr-resolvido))
	  (setq psr-resolvido (procura-retrocesso-mac-mrv (fill-a-pix->psr array)))
	  (if psr-resolvido
	  (psr->fill-a-pix psr-resolvido nlinhas ncolunas)
	  nil)))

;Funcao que recebe um array fill-a-pix e tenta resolve-lo utilizando uma procura com retrocesso, com a heuristica do maior grau. 
;Em primeiro lugar, o array sera convertido para psr recorrendo a funcao fill-a-pix->psr.
;Em segundo lugar, a funcao ira efectuar uma procura cega com retrocesso.
;Caso seja encontrada uma solucao, o psr correspondente sera convertido num array com a funcao psr->fill-a-pix.
(defun resolve-grau (array)
	(let ((nlinhas (first (array-dimensions array)))
		  (ncolunas (nth 1 (array-dimensions array)))
          (psr-resolvido))
     (setq psr-resolvido (procura-retrocesso-grau (fill-a-pix->psr array)))
     (if psr-resolvido
     (psr->fill-a-pix psr-resolvido nlinhas ncolunas)
     nil)))

;Funcao de procura utilizada por resolve-best.
;Prepara uma lista de pares, sendo cada par uma variavel do psr e o seu grau correspondente.
;Esta lista sera ordenada por grau.
;Chama a funcao make-domains-consistent, a qual ira aplicar inferencia ainda antes da procura comecar.
;Chama a funcao procura-best-aux que ira efectuar a procura, resolvendo o psr
(defun procura-best (psr)
  (let ((grau) 
		(lista-grau nil))
    
    ;cria lista estatica com graus das variaveis
    (loop for var in (psr-variaveis-todas psr) do
      (setf grau (length (psr-variavel-restricoes psr var)))
      (setf lista-grau (cons (cons var grau) lista-grau)))
    (setf lista-grau (sort lista-grau #'list-sort-aux))
   
    ;coloca dominios na hash respectiva   
    (loop for v in (psr-variaveis-todas psr) do
      (setf (gethash v (psr-dominios-hash psr)) 
        (psr-variavel-dominio psr v)))

    ;corta os dominios que for possivel cortar imediatamente
    (make-domains-consistent psr)

    ;preenche a hash table envolvidas, com informacao sobre que variaveis estao envolvidas numa relacao com outras
    (loop for r in (psr-restricoes psr) do
      (loop for v1 in (restricao-variaveis r) do
        (loop for v2 in (restricao-variaveis r) do
          (if (and (not (equal v2 v1))
            (not (member v2 (gethash v1 (psr-envolvidas-hash psr)) :test #'equal)))
          (setf (gethash v1 (psr-envolvidas-hash psr))
            (cons v2 (gethash v1 (psr-envolvidas-hash psr))))))))

    (procura-best-aux psr lista-grau)))

;Funcao utilizada por procura-best.
;Ira efectuar inferencia ainda antes da procura comecar, por exemplo para 9s e 0s, em que o valor das variaveis ja pode ser determinado a partida.
(defun make-domains-consistent (psr)
  (let ((restricoes nil)
		(new-domain-0)
		(new-domain-1))
   (loop for var in (psr-variaveis-todas psr) do 
    (setf restricoes (psr-variavel-restricoes psr var))
    (loop for val from 0 to 1 do 
      (psr-adiciona-atribuicao! psr var val)
      (setf new-domain-0 nil)
      (setf new-domain-1 nil)
      (dolist (r restricoes)
       (if (not (funcall (restricao-funcao-validacao r) psr))
          (progn
			(if (equal val 0)
			      (setf new-domain-1 t)
			      (setf new-domain-0 t))
          (return))))
      (psr-remove-atribuicao! psr var)
      (if new-domain-0
        (progn
          (psr-altera-dominio-best! psr var (list 0))
          (psr-adiciona-atribuicao! psr var 0)))
      (if new-domain-1
        (progn
          (psr-altera-dominio-best! psr var (list 1))
          (psr-adiciona-atribuicao! psr var 1)))))))

;escolhe a variavel com o dominio mais pequeno. em caso de empate, a de maior grau
(defun escolhe-var-best (psr lista-grau)
	(let ((selected-vars nil)
		  (dominio-mais-pequeno nil)
		  (tamanho-dominio)
      (variaveis-livres (psr-variaveis-n-atribuidas psr)))
    (setf dominio-mais-pequeno (length (psr-variavel-dominio-best psr (first variaveis-livres))))
    (dolist (var variaveis-livres)
      (setf tamanho-dominio (length (psr-variavel-dominio-best psr var)))
      (if (< tamanho-dominio dominio-mais-pequeno)
        (progn 
          (setf dominio-mais-pequeno tamanho-dominio)
          (setf selected-vars (list var)))
        (if (equal tamanho-dominio dominio-mais-pequeno)
          (setf selected-vars (cons var selected-vars)))))
    ;devolve a variavel da lista selected-vars que aparecer primeiro na lista-grau
    (dolist (par lista-grau)
      (if (member (first par) selected-vars :test #'equal)
        (return-from escolhe-var-best (first par))))))

;Procura mac optimizada, que utiliza a heuristica minimum remaining values e a heuristica do maior grau como criterio de desempate.
;Procura utilizada por resolve-best
(defun procura-best-aux (psr lista-grau)
  (let ((var)
		(result_psr)
		(consistency)
		(inferencias)
		(old-domains))
    (if (not (psr-variaveis-n-atribuidas psr))
      (return-from procura-best-aux psr)
	  (progn
		(setq var (escolhe-var-best psr lista-grau))
		(dolist (val (psr-variavel-dominio-best psr var))
		  (setf consistency (psr-atribuicao-consistente-p-best psr var val))
		  (if consistency
			(progn 
				(psr-adiciona-atribuicao! psr var val)
				(setf (psr-variaveis-n-atribuidas psr) 
					(remove var (psr-variaveis-n-atribuidas psr) :test #'equal))
				(setf inferencias (MAC-best psr var))
				(if inferencias
					(progn
						(setf old-domains (psr-adiciona-inferencias-best! psr inferencias))
						(setf result_psr (procura-best-aux psr lista-grau))
						(if result_psr
							(return-from procura-best-aux result_psr))
						(psr-remove-inferencias-best! psr old-domains)))
				(psr-remove-atribuicao! psr var)
				(setf (psr-variaveis-n-atribuidas psr) (cons var (psr-variaveis-n-atribuidas psr))))))))
  (return-from procura-best-aux nil)))

;Versao optimizada para fill-a-pix da funcao MAC, anteriormente definida
(defun MAC-best (psr var)
  (let ((revised)
		(inferencias (make-hash-table :test 'equal :size (length (psr-variaveis-n-atribuidas psr))))
		(lista-arcos (arcos-vizinhos-nao-atribuidos-best psr var))
		(novos-arcos)
		(arco))
    (loop do
      (if (null lista-arcos) (return))
      (setf arco (first lista-arcos))
      (setf revised
        (revise-best psr (first arco) (rest arco) inferencias))
        (if revised
          (progn 
            (if (not (gethash (first arco) inferencias))
            (return-from MAC-best nil))
            (setf novos-arcos (arcos-vizinhos-nao-atribuidos-best psr (first arco)))
            (setf novos-arcos (remove-par-de-lista 
              (cons (rest arco) (first arco)) novos-arcos))
            (setf lista-arcos (adiciona-pares-a-lista novos-arcos lista-arcos))))
        (setf lista-arcos (remove-par-de-lista arco lista-arcos)))
    (return-from MAC-best inferencias)))

;Versao optimizada para fill-a-pix da funcao revise, anteriormente definida
(defun revise-best (psr x y inferencias)
  (let ((consistency)
		(revised nil)
		(dominio-x)
		(novo-dominio-x)
		(dominio-y)
		(foundConsistentValue))

    (if (gethash x inferencias)
      (setf dominio-x (gethash x inferencias))
      (setf dominio-x (psr-variavel-dominio-best psr x)))
    (setf novo-dominio-x dominio-x)
    (if (psr-variavel-valor psr y)
      (setf dominio-y (list (psr-variavel-valor psr y)))
      (if (gethash y inferencias)
        (setf dominio-y (gethash y inferencias))
        (setf dominio-y (psr-variavel-dominio-best psr y))))
    (dolist (vx dominio-x)
      (setf foundConsistentValue nil)
      (dolist (vy dominio-y)
        (setf consistency
          (psr-atribuicoes-consistentes-arco-p-best psr x vx y vy))
        (if consistency
          (progn
            (setf foundConsistentValue t)
            (return))))
      (if (not foundConsistentValue)
        (progn
          (setf revised t)
          (setf novo-dominio-x (remove vx novo-dominio-x :test #'equal)))))

    (if revised
      (progn
		(setf (gethash x inferencias) novo-dominio-x)))

    (return-from revise-best revised)))

;retorna uma lista de arcos (sem arcos repetidos)
;que correspondem as variaveis ainda nao atribuidas que estao 
;envolvidas numa restricao com var
(defun arcos-vizinhos-nao-atribuidos-best (psr var)
  (let ((lista-de-arcos nil))
    (dolist (v (gethash var (psr-envolvidas-hash psr)))
        (if (not (psr-variavel-valor psr v))
        (setf lista-de-arcos (cons (cons v var) lista-de-arcos))))
    lista-de-arcos))

;versao do psr-variavel-consistente-p utilizada no resolve-best, que nao contabiliza
;os testes de consistencia
(defun psr-variavel-consistente-p-best (psr variavel)
	(dolist (res (psr-variavel-restricoes psr variavel))
	 (if (not (funcall (restricao-funcao-validacao res) psr))
		(return-from psr-variavel-consistente-p-best nil)))
  T)

;versao do psr-atribuicao-consistente-p utilizada no resolve-best, que nao contabiliza
;os testes de consistencia
(defun psr-atribuicao-consistente-p-best (psr variavel valor)
  (let ((valor-antigo (psr-variavel-valor psr variavel))
		(consistencia))
	(psr-adiciona-atribuicao! psr variavel valor)
	(setf consistencia (psr-variavel-consistente-p-best psr variavel))
	(if valor-antigo
		(psr-adiciona-atribuicao! psr variavel valor-antigo)
		(psr-remove-atribuicao! psr variavel))
  consistencia))

;versao do psr-atribuicoes-consistentes-arco-p utilizada no resolve-best, que nao contabiliza
;os testes de consistencia
(defun psr-atribuicoes-consistentes-arco-p-best(psr variavel1 valor1 variavel2 valor2)
  (let ((valor-antigo1 (psr-variavel-valor psr variavel1))
		(valor-antigo2 (psr-variavel-valor psr variavel2))
		(consistencia t))

    ;adiciona as atribuicoes ao psr
    (psr-adiciona-atribuicao! psr variavel1 valor1)
    (psr-adiciona-atribuicao! psr variavel2 valor2)

    (dolist (res (psr-variavel-restricoes psr variavel1))
      (if(member variavel2 (restricao-variaveis res) :test #'equal)
        (progn 
          (if (not (funcall (restricao-funcao-validacao res) psr))
            (progn
              (setf consistencia nil)
              (return))))))

    (psr-remove-atribuicao! psr variavel2)
    (if valor-antigo1
		  (psr-adiciona-atribuicao! psr variavel1 valor-antigo1)
		  (psr-remove-atribuicao! psr variavel1))
    (if valor-antigo2
		  (psr-adiciona-atribuicao! psr variavel2 valor-antigo2)
		  (psr-remove-atribuicao! psr variavel2))
    consistencia))