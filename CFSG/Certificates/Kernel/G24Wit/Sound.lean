module

public import Certificates.Data.Kernel.G24Wit.K
public import CFSG.Certificates.Kernel.Misc.G24P0Sound

public section

namespace CFSG.KC.G24Wit

open CFSG.Fischer CFSG.LieType.Multipliers.G24 CFSG.KC.Misc.Spec CFSG.KC.Misc.G24
open CFSG.Quasithin.St84.G24Wit CFSG.Quasithin.St84.G24Ident CFSG.Quasithin.St84.G24Pc
  CFSG.Quasithin.St84.G24DC

def Sh (X : Array (Array F4)) (a : Nat) : Prop :=
  ∃ M : Matrix (Fin 14) (Fin 14) F4, X = ofMat M ∧ blowMat M = pkMat 28 a

theorem sh_one : Sh one14 oneK := ⟨1, rfl, by rw [blowMat_one, oneK, pkMat_oneF2]⟩

theorem Sh.mul {A B : Array (Array F4)} {a b : Nat} (hA : Sh A a) (hB : Sh B b) :
    Sh (mulArr 14 A B) (mulF2 28 a b) := by
  obtain ⟨M, rfl, hM⟩ := hA
  obtain ⟨N, rfl, hN⟩ := hB
  refine ⟨M * N, ?_, ?_⟩
  · rw [mulArr_eq_ofMat, toMat_ofMat, toMat_ofMat]
  · rw [blowMat_mul, hM, hN, pkMat_mulF2]

theorem Sh.eq {X Y : Array (Array F4)} {a b : Nat} (hX : Sh X a) (hY : Sh Y b) (h : a = b) :
    X = Y := by
  obtain ⟨M, rfl, hM⟩ := hX
  obtain ⟨N, rfl, hN⟩ := hY
  subst h
  rw [blowMat_injective (hM.trans hN.symm)]

theorem Sh.beq {X Y : Array (Array F4)} {a b : Nat} (hX : Sh X a) (hY : Sh Y b)
    (h : Nat.beq a b = true) : X = Y :=
  hX.eq hY (Nat.eq_of_beq_eq_true h)

theorem sh_getD {α : Type} (L : List α) (f : α → Array (Array F4)) (fK : α → Nat)
    (h : ∀ x ∈ L, Sh (f x) (fK x)) (i : Nat) :
    Sh ((L.map f).toArray.getD i one14) (getK (L.map fK) i) := by
  unfold getK
  by_cases hi : i < L.length
  · have e1 : (L.map f).toArray.getD i one14 = f L[i] := by simp [Array.getD, hi]
    have e2 : (L.map fK).getD i oneK = fK L[i] := by simp [List.getD_eq_getElem?_getD, hi]
    rw [e1, e2]
    exact h _ (List.getElem_mem hi)
  · have e1 : (L.map f).toArray.getD i one14 = one14 := by simp [Array.getD, hi]
    have e2 : (L.map fK).getD i oneK = oneK := by simp [List.getD_eq_getElem?_getD, hi]
    rw [e1, e2]
    exact sh_one

theorem sh_list_eq {α β : Type} (L₁ : List α) (L₂ : List β) (f₁ : α → Array (Array F4))
    (f₂ : β → Array (Array F4)) (g₁ : α → Nat) (g₂ : β → Nat)
    (h₁ : ∀ x ∈ L₁, Sh (f₁ x) (g₁ x)) (h₂ : ∀ x ∈ L₂, Sh (f₂ x) (g₂ x))
    (h : L₁.map g₁ = L₂.map g₂) : L₁.map f₁ = L₂.map f₂ := by
  induction L₁ generalizing L₂ with
  | nil =>
    cases L₂ with
    | nil => rfl
    | cons y L₂ => simp at h
  | cons x L₁ ih =>
    cases L₂ with
    | nil => simp at h
    | cons y L₂ =>
      simp only [List.map_cons, List.cons.injEq] at h ⊢
      exact ⟨(h₁ x (by simp)).eq (h₂ y (by simp)) h.1,
        ih L₂ (fun z hz => h₁ z (by simp [hz])) (fun z hz => h₂ z (by simp [hz])) h.2⟩

theorem sh_word {GR : List (List (List Nat))} {Gb : List Nat} {RS XS YS : List (List Nat)}
    {PS : List (List (List Nat × List Nat))} {XL YL : List (List (List Nat))}
    (hG : genRows = GR.map (List.map strOf)) (h : g24F4K GR Gb RS PS XS YS XL YL = true)
    (w : Word) : Sh (wordArr w) (wK Gb w) := by
  have e0 : wordArrOf (genArrsOf genRows) w = wordArr w := by
    simp only [wordArrOf, genArrsOf, wordArr, genArr, genArrs]
  have e1 : one14 = ofMat (1 : Matrix (Fin 14) (Fin 14) F4) := by
    unfold one14
    rfl
  have e : wordArr w = ofMat (g24Mat GR w) := by
    rw [g24Mat, ← hG, e0]
    unfold wordArr
    rw [e1, foldr_mulArr, toMat_ofMat]
  have eL : (encL : Fin 6 × Bool → Nat) = fun l => 2 * l.1.val + if l.2 then 1 else 0 := by
    funext l
    simp only [encL]
  have eK : wK Gb w = wordF4 Gb (encG w) := by
    rw [wK, encG, eL]
  refine ⟨_, e, ?_⟩
  rw [eK]
  exact (g24F4_word h w).symm

theorem evalP_nil {n : Nat} (G : Array Mat) : evalP G ([] : List (Fin n)) = one14 :=
  List.foldr_nil

theorem evalPK_nil {n : Nat} (g : List Nat) : evalPK g ([] : List (Fin n)) = oneK :=
  List.foldr_nil

theorem evalP_cons {n : Nat} (G : Array Mat) (l : Fin n) (w : List (Fin n)) :
    evalP G (l :: w) = mulArr 14 (G.getD l.val one14) (evalP G w) :=
  List.foldr_cons

theorem evalPK_cons {n : Nat} (g : List Nat) (l : Fin n) (w : List (Fin n)) :
    evalPK g (l :: w) = mulF2 28 (getK g l.val) (evalPK g w) :=
  List.foldr_cons

theorem sh_evalP {n : Nat} {G : Array Mat} {g : List Nat}
    (hG : ∀ i, Sh (G.getD i one14) (getK g i)) (w : List (Fin n)) :
    Sh (evalP G w) (evalPK g w) := by
  induction w with
  | nil =>
    rw [evalP_nil, evalPK_nil]
    exact sh_one
  | cons l w ih =>
    rw [evalP_cons, evalPK_cons]
    exact (hG l.val).mul ih

theorem sh_foldlInv {n : Nat} {G : Array Mat} {g : List Nat}
    (hG : ∀ i, Sh (G.getD i one14) (getK g i)) (w : List (Fin n)) :
    ∀ {A : Mat} {a : Nat}, Sh A a →
      Sh (w.foldl (fun A l => mulArr 14 (G.getD l.val one14) A) A)
        (w.foldl (fun A l => mulF2 28 (getK g l.val) A) a) := by
  induction w with
  | nil =>
    intro A a h
    rw [List.foldl_nil, List.foldl_nil]
    exact h
  | cons l w ih =>
    intro A a h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih ((hG l.val).mul h)

theorem sh_evalPInv {n : Nat} {G : Array Mat} {g : List Nat}
    (hG : ∀ i, Sh (G.getD i one14) (getK g i)) (w : List (Fin n)) :
    Sh (evalPInv G w) (evalPInvK g w) :=
  sh_foldlInv hG w sh_one

theorem evalL_nil {n : Nat} (G : Array Mat × Array Mat) :
    evalL G ([] : List (Fin n × Bool)) = one14 :=
  List.foldr_nil

theorem evalLK_nil {n : Nat} (g : List Nat × List Nat) :
    evalLK g ([] : List (Fin n × Bool)) = oneK :=
  List.foldr_nil

theorem evalL_cons {n : Nat} (G : Array Mat × Array Mat) (i : Fin n) (b : Bool)
    (w : List (Fin n × Bool)) :
    evalL G ((i, b) :: w) =
      mulArr 14 (if b then G.1.getD i.val one14 else G.2.getD i.val one14) (evalL G w) :=
  List.foldr_cons

theorem evalLK_cons {n : Nat} (g : List Nat × List Nat) (i : Fin n) (b : Bool)
    (w : List (Fin n × Bool)) :
    evalLK g ((i, b) :: w) =
      mulF2 28 (if b then getK g.1 i.val else getK g.2 i.val) (evalLK g w) :=
  List.foldr_cons

theorem sh_evalL {n : Nat} {G : Array Mat × Array Mat} {g : List Nat × List Nat}
    (h₁ : ∀ i, Sh (G.1.getD i one14) (getK g.1 i)) (h₂ : ∀ i, Sh (G.2.getD i one14) (getK g.2 i))
    (w : List (Fin n × Bool)) : Sh (evalL G w) (evalLK g w) := by
  induction w with
  | nil =>
    rw [evalL_nil, evalLK_nil]
    exact sh_one
  | cons l w ih =>
    obtain ⟨i, b⟩ := l
    rw [evalL_cons, evalLK_cons]
    cases b
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      exact (h₂ i.val).mul ih
    · rw [if_pos rfl, if_pos rfl]
      exact (h₁ i.val).mul ih

theorem sh_mats {Gb : List Nat} (hw : ∀ w, Sh (wordArr w) (wK Gb w)) (ws : List Word) :
    (∀ i, Sh ((matsOf ws).1.getD i one14) (getK (matsK Gb ws).1 i)) ∧
      (∀ i, Sh ((matsOf ws).2.getD i one14) (getK (matsK Gb ws).2 i)) :=
  ⟨sh_getD ws wordArr (wK Gb) (fun w _ => hw w),
    sh_getD ws (fun w => wordArr w.reverse) (fun w => wK Gb w.reverse) (fun w _ => hw _)⟩

def ShN (A : Native.Mat) (a : Nat) : Prop := blowMat (Code.decode A) = pkMat 28 a

theorem shN_one : ShN Native.oneM oneK := by
  rw [ShN, Code.decode_oneM, blowMat_one, oneK, pkMat_oneF2]

theorem ShN.mul {A B : Native.Mat} {a b : Nat} (hA : ShN A a) (hB : ShN B b) :
    ShN (Native.mulN A B) (mulF2 28 a b) := by
  unfold ShN at *
  rw [Code.decode_mulN, blowMat_mul, hA, hB, pkMat_mulF2]

theorem ShN.sh {A : Native.Mat} {a : Nat} (h : ShN A a) : Sh (Code.decMat A) a :=
  ⟨Code.decode A, rfl, h⟩

theorem decode_eq_digMat (A : Native.Mat) : Code.decode A = digMat (digsN A) := by
  ext i j
  have e : ((digsN A).getD i.val []).getD j.val 0 =
      Native.rowVal (A.getD i.val Native.zeroRow) j.val := by
    simp [digsN, List.getD_eq_getElem?_getD, i.isLt, j.isLt]
  simp only [Code.decode, digMat, Matrix.of_apply, Code.decCode, e]

theorem shN_base (A : Native.Mat) (h : shape4 (digsN A) = true) : ShN A (decK A) := by
  rw [ShN, decode_eq_digMat, decK, pkMat_blow14 h]

theorem shN_foldl {g : Array Native.Mat} {gK : List Nat}
    (hg : ∀ i, ShN (g.getD i Native.oneM) (getK gK i)) (w : List (Fin 4)) :
    ∀ {A : Native.Mat} {a : Nat}, ShN A a →
      ShN (w.foldl (fun acc l => Native.mulN acc (g.getD l.val Native.oneM)) A)
        (w.foldl (fun acc l => mulF2 28 acc (getK gK l.val)) a) := by
  induction w with
  | nil =>
    intro A a h
    rw [List.foldl_nil, List.foldl_nil]
    exact h
  | cons l w ih =>
    intro A a h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (h.mul (hg l.val))

theorem shN_evalF {g : Array Native.Mat} {gK : List Nat}
    (hg : ∀ i, ShN (g.getD i Native.oneM) (getK gK i)) (w : List (Fin 4)) :
    ShN (Native.evalF g w) (evalFK gK w) :=
  shN_foldl hg w shN_one

theorem shN_getD {P : Native.Mat → Nat → Prop} (g : Array Native.Mat) (fK : Native.Mat → Nat)
    (h1 : P Native.oneM oneK) (h : ∀ A ∈ g.toList, P A (fK A)) (i : Nat) :
    P (g.getD i Native.oneM) (getK (g.toList.map fK) i) := by
  unfold getK
  by_cases hi : i < g.size
  · have e1 : g.getD i Native.oneM = g[i] := by simp [Array.getD, hi]
    have e2 : (g.toList.map fK).getD i oneK = fK g[i] := by
      simp [List.getD_eq_getElem?_getD, hi]
    rw [e1, e2]
    exact h _ (by simp)
  · have e1 : g.getD i Native.oneM = Native.oneM := by simp [Array.getD, hi]
    have e2 : (g.toList.map fK).getD i oneK = oneK := by
      simp [List.getD_eq_getElem?_getD, hi]
    rw [e1, e2]
    exact h1

local instance (priority := high) decEqF4 : DecidableEq F4 := fun a b =>
  decidable_of_iff (a.code = b.code) (by cases a; cases b; simp)

def frobH : F4 →+* F4 where
  toFun x := x * x
  map_one' := by decide
  map_mul' := by decide
  map_zero' := by decide
  map_add' := by decide

theorem frobArr_ofMat (M : Matrix (Fin 14) (Fin 14) F4) :
    frobArr (ofMat M) = ofMat (M.map frobH) := by
  simp [frobArr, ofMat, Function.comp_def]
  exact fun _ _ => rfl

theorem decCode_frob (r : Native.Row) (j : Nat) :
    Code.decCode (Native.rowVal (frobRow r) j) =
      frobH (Code.decCode (Native.rowVal r j)) := by
  unfold frobRow Native.rowVal
  simp only [Nat.testBit_xor]
  cases r.1.testBit j <;> cases r.2.testBit j <;> decide

theorem getD_frobN (A : Native.Mat) (i : Nat) :
    (frobN A).getD i Native.zeroRow = frobRow (A.getD i Native.zeroRow) := by
  unfold frobN
  by_cases hi : i < A.size
  · simp [Array.getD, hi]
  · simp [Array.getD, hi]
    rfl

theorem decode_frobN (A : Native.Mat) : Code.decode (frobN A) = (Code.decode A).map frobH := by
  ext i j
  rw [Code.decode, Matrix.map_apply, Code.decode, Matrix.of_apply, Matrix.of_apply, getD_frobN,
    decCode_frob]

def ShF (A : Native.Mat) (a : Nat) : Prop := blowMat ((Code.decode A).map frobH) = pkMat 28 a

theorem shF_one : ShF Native.oneM oneK := by
  rw [ShF, Code.decode_oneM, Matrix.map_one frobH (map_zero frobH) (map_one frobH), blowMat_one,
    oneK, pkMat_oneF2]

theorem ShF.mul {A B : Native.Mat} {a b : Nat} (hA : ShF A a) (hB : ShF B b) :
    ShF (Native.mulN A B) (mulF2 28 a b) := by
  unfold ShF at *
  rw [Code.decode_mulN, Matrix.map_mul, blowMat_mul, hA, hB, pkMat_mulF2]

theorem ShF.sh {A : Native.Mat} {a : Nat} (h : ShF A a) : Sh (frobArr (Code.decMat A)) a :=
  ⟨_, frobArr_ofMat (Code.decode A), h⟩

theorem shF_base (A : Native.Mat) (h : shape4 (digsN (frobN A)) = true) :
    ShF A (decK (frobN A)) := by
  rw [ShF, ← decode_frobN]
  exact shN_base _ h

theorem shF_foldl {g : Array Native.Mat} {gK : List Nat}
    (hg : ∀ i, ShF (g.getD i Native.oneM) (getK gK i)) (w : List (Fin 4)) :
    ∀ {A : Native.Mat} {a : Nat}, ShF A a →
      ShF (w.foldl (fun acc l => Native.mulN acc (g.getD l.val Native.oneM)) A)
        (w.foldl (fun acc l => mulF2 28 acc (getK gK l.val)) a) := by
  induction w with
  | nil =>
    intro A a h
    rw [List.foldl_nil, List.foldl_nil]
    exact h
  | cons l w ih =>
    intro A a h
    rw [List.foldl_cons, List.foldl_cons]
    exact ih (h.mul (hg l.val))

theorem shF_evalF {g : Array Native.Mat} {gK : List Nat}
    (hg : ∀ i, ShF (g.getD i Native.oneM) (getK gK i)) (w : List (Fin 4)) :
    ShF (Native.evalF g w) (evalFK gK w) :=
  shF_foldl hg w shF_one

theorem wImg_getD (i : Nat) : (wImg ()).getD i #[] =
    ((Native.wWords.getD i []).map fun w => Code.decMat (Native.evalF (Native.gBN ()) w)).toArray := by
  unfold wImg Native.wImgN
  generalize Native.gBN () = g
  generalize Native.wWords = W
  by_cases hi : i < W.length
  · simp [Array.getD, hi, List.getD_eq_getElem?_getD, Function.comp_def]
  · simp [Array.getD, hi, List.getD_eq_getElem?_getD]

theorem gB_eq : gB = ((Native.gBN ()).toList.map Code.decMat).toArray := by
  unfold gB
  generalize Native.gBN () = g
  cases g
  simp

theorem cocImgs_fst (P2 A2 : Array Mat × Array Mat) (D : List (List (Fin 10))) :
    (cocImgs P2 A2 D).1 = ((List.range 3).map fun t =>
      mulArr 14 (evalP P2.1 (D.getD t [])) (A2.1.getD t one14)).toArray := rfl

theorem cocImgs_snd (P2 A2 : Array Mat × Array Mat) (D : List (List (Fin 10))) :
    (cocImgs P2 A2 D).2 = ((List.range 3).map fun t =>
      mulArr 14 (A2.2.getD t one14) (evalPInv P2.2 (D.getD t []))).toArray := rfl

theorem cocK_fst (P2 A2 : List Nat × List Nat) (D : List (List (Fin 10))) :
    (cocK P2 A2 D).1 = (List.range 3).map fun t =>
      mulF2 28 (evalPK P2.1 (D.getD t [])) (getK A2.1 t) := rfl

theorem cocK_snd (P2 A2 : List Nat × List Nat) (D : List (List (Fin 10))) :
    (cocK P2 A2 D).2 = (List.range 3).map fun t =>
      mulF2 28 (getK A2.2 t) (evalPInvK P2.2 (D.getD t [])) := rfl

theorem sh_coc {P2 A2 : Array Mat × Array Mat} {P2K A2K : List Nat × List Nat}
    (hp1 : ∀ i, Sh (P2.1.getD i one14) (getK P2K.1 i))
    (hp2 : ∀ i, Sh (P2.2.getD i one14) (getK P2K.2 i))
    (ha1 : ∀ i, Sh (A2.1.getD i one14) (getK A2K.1 i))
    (ha2 : ∀ i, Sh (A2.2.getD i one14) (getK A2K.2 i)) (D : List (List (Fin 10))) :
    (∀ t, Sh ((cocImgs P2 A2 D).1.getD t one14) (getK (cocK P2K A2K D).1 t)) ∧
      (∀ t, Sh ((cocImgs P2 A2 D).2.getD t one14) (getK (cocK P2K A2K D).2 t)) := by
  rw [cocImgs_fst, cocImgs_snd, cocK_fst, cocK_snd]
  exact ⟨sh_getD _ _ _ fun t _ => (sh_evalP hp1 _).mul (ha1 t),
    sh_getD _ _ _ fun t _ => (ha2 t).mul (sh_evalPInv hp2 _)⟩

theorem sh_mapGetD {α : Type} (L : List α) (F : α → Array Mat × Array Mat)
    (FK : α → List Nat × List Nat) (h : ∀ x i, Sh ((F x).1.getD i one14) (getK (FK x).1 i))
    (s i : Nat) :
    Sh (((L.map F).getD s (#[], #[])).1.getD i one14) (getK ((L.map FK).getD s ([], [])).1 i) := by
  by_cases hs : s < L.length
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map, List.getElem?_eq_getElem hs, Option.map_some, Option.map_some,
      Option.getD_some, Option.getD_some]
    exact h _ i
  · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_map, List.getElem?_eq_none (by omega), Option.map_none, Option.map_none,
      Option.getD_none, Option.getD_none]
    have e1 : (#[] : Array Mat).getD i one14 = one14 := by simp [Array.getD]
    have e2 : getK [] i = oneK := by simp [getK]
    rw [e1, e2]
    exact sh_one

theorem witCheck_of_witK {GR : List (List (List Nat))} {Gb : List Nat} {RS XS YS : List (List Nat)}
    {PS : List (List (List Nat × List Nat))} {XL YL : List (List (List Nat))}
    (hG : genRows = GR.map (List.map strOf)) (h44 : g24F4K GR Gb RS PS XS YS XL YL = true)
    (h : witK Gb = true) : witCheck () = true := by
  have hw := sh_word hG h44
  simp only [witK, Bool.and_eq_true, List.all_eq_true, and_assoc] at h
  obtain ⟨hshape, hA, hB, hC, hD, hE, hF, hH, hw0, hw1, hw3, hw8, -⟩ := h
  have hgN : ∀ i, ShN ((Native.gBN ()).getD i Native.oneM) (getK gbK i) :=
    shN_getD (P := ShN) _ decK shN_one fun A hA => shN_base A (hshape A hA).1
  have hgF : ∀ i, ShF ((Native.gBN ()).getD i Native.oneM) (getK gbFK i) :=
    shN_getD (P := ShF) _ (fun A => decK (frobN A)) shF_one
      fun A hA => shF_base A (hshape A hA).2
  have hrow : ∀ i, ∀ w ∈ Native.wWords.getD i [],
      Sh (Code.decMat (Native.evalF (Native.gBN ()) w)) (evalFK gbK w) :=
    fun _ w _ => (shN_evalF hgN w).sh
  have hrowF : ∀ i, ∀ w ∈ Native.wWords.getD i [],
      Sh (frobArr (Code.decMat (Native.evalF (Native.gBN ()) w))) (evalFK gbFK w) :=
    fun _ w _ => (shF_evalF hgF w).sh
  have hW : ∀ i k, Sh (((wImg ()).getD i #[]).getD k one14) (getK (wRowK gbK i) k) := by
    intro i k
    rw [wImg_getD]
    exact sh_getD _ _ _ (hrow i) k
  have hgB : ∀ k, Sh (gB.getD k one14) (getK gbK k) := by
    intro k
    rw [gB_eq]
    exact sh_getD _ _ _ (fun A hA => (shN_base A (hshape A hA).1).sh) k
  have hgBF : ∀ A ∈ (Native.gBN ()).toList, Sh (frobArr (Code.decMat A)) (decK (frobN A)) :=
    fun A hA => (shF_base A (hshape A hA).2).sh
  obtain ⟨p1a, p1b⟩ := sh_mats hw pc1
  obtain ⟨p2a, p2b⟩ := sh_mats hw pc2
  obtain ⟨a1a, a1b⟩ := sh_mats hw [a1, b1, k1]
  obtain ⟨a2a, a2b⟩ := sh_mats hw [a2, b2, k2]
  have bea : ∀ j, Sh ((e1Q.map (evalP (matsOf pc1).1)).toArray.getD j one14)
      (getK (e1Q.map (evalPK (matsK Gb pc1).1)) j) :=
    sh_getD _ _ _ fun w _ => sh_evalP p1a w
  have beb : ∀ j, Sh ((e1Q.map (evalPInv (matsOf pc1).2)).toArray.getD j one14)
      (getK (e1Q.map (evalPInvK (matsK Gb pc1).2)) j) :=
    sh_getD _ _ _ fun w _ => sh_evalPInv p1b w
  have ala : ∀ t, Sh ((e1A.map (evalL (matsOf [a1, b1, k1]))).toArray.getD t one14)
      (getK (e1A.map (evalLK (matsK Gb [a1, b1, k1]))) t) :=
    sh_getD _ _ _ fun w _ => sh_evalL (G := (_, _)) (g := (_, _)) a1a a1b w
  have alb : ∀ t, Sh ((e1A.map fun w => evalL (matsOf [a1, b1, k1]) (invW w)).toArray.getD t one14)
      (getK (e1A.map fun w => evalLK (matsK Gb [a1, b1, k1]) (invW w)) t) :=
    sh_getD _ _ _ fun w _ => sh_evalL (G := (_, _)) (g := (_, _)) a1a a1b (invW w)
  have hcs : ∀ D,
      (∀ t, Sh ((cocImgs (matsOf pc2) (matsOf [a2, b2, k2]) D).1.getD t one14)
        (getK (cocK (matsK Gb pc2) (matsK Gb [a2, b2, k2]) D).1 t)) ∧
      (∀ t, Sh ((cocImgs (matsOf pc2) (matsOf [a2, b2, k2]) D).2.getD t one14)
        (getK (cocK (matsK Gb pc2) (matsK Gb [a2, b2, k2]) D).2 t)) :=
    sh_coc p2a p2b a2a a2b
  have hcsg : ∀ s i,
      Sh (((e2Coc.map (cocImgs (matsOf pc2) (matsOf [a2, b2, k2]))).getD s (#[], #[])).1.getD i
        one14) (getK ((e2Coc.map (cocK (matsK Gb pc2) (matsK Gb [a2, b2, k2]))).getD s
          ([], [])).1 i) :=
    sh_mapGetD e2Coc _ _ fun D => (hcs D).1
  simp only [witCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    exact (sh_evalL (G := (_, _)) (g := (_, _)) bea beb r).beq sh_one (hA r hr)
  · intro j hj
    exact (sh_evalP bea _).beq (p1a j) (hB j hj)
  · intro r hr
    exact (sh_evalL (G := (_, _)) (g := (_, _)) ala alb r).beq sh_one (hC r hr)
  · intro t ht j hj
    obtain ⟨h1, h2⟩ := hD t ht j hj
    exact ⟨(((a1a t).mul (p1a j)).mul (a1b t)).beq (sh_evalP p1a _) h1,
      (sh_evalP bea _).beq (((ala t).mul (bea j)).mul (alb t)) h2⟩
  · intro k hk
    obtain ⟨h1, h2⟩ := hE k hk
    exact ⟨(hgB k).beq ((sh_evalP p1a _).mul (sh_evalP a1a _)) h1,
      (hW 2 k).beq ((sh_evalP bea _).mul (sh_evalP ala _)) h2⟩
  · intro c hc r hr
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hc
    exact (sh_evalL (G := (_, _)) (g := (_, _)) (hcs D).1 (hcs D).2 r).beq sh_one
      (hF _ (List.mem_map_of_mem hD) r hr)
  · decide
  · intro k hk
    obtain ⟨h1, h2⟩ := hH k hk
    exact ⟨(hgB k).beq ((sh_evalP p2a _).mul (sh_evalP a2a _)) h1,
      fun s hs => (hW (4 + s) k).beq ((sh_evalP p2a _).mul (sh_evalP (hcsg s) _)) (h2 s hs)⟩
  · rw [wImg_getD, gB_eq]
    exact congrArg List.toArray (sh_list_eq _ _ _ _ _ _ (hrow 0)
      (fun A hA => (shN_base A (hshape A hA).1).sh) (beq_iff_eq.1 hw0))
  · rw [wImg_getD, gB_eq, List.map_toArray, List.map_map]
    exact congrArg List.toArray (sh_list_eq _ _ _ (fun A => frobArr (Code.decMat A)) _ _ (hrow 1)
      hgBF (beq_iff_eq.1 hw1))
  · rw [wImg_getD 3, wImg_getD 2, List.map_toArray, List.map_map]
    exact congrArg List.toArray (sh_list_eq _ _ _
      (fun w => frobArr (Code.decMat (Native.evalF (Native.gBN ()) w))) _ _ (hrow 3) (hrowF 2)
      (beq_iff_eq.1 hw3))
  · intro s hs
    rw [wImg_getD (8 + s), wImg_getD (4 + s), List.map_toArray, List.map_map]
    exact congrArg List.toArray (sh_list_eq _ _ _
      (fun w => frobArr (Code.decMat (Native.evalF (Native.gBN ()) w))) _ _ (hrow (8 + s))
      (hrowF (4 + s)) (beq_iff_eq.1 (hw8 s hs)))
  · decide

end CFSG.KC.G24Wit
