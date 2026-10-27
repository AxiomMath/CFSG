module

public import Certificates.Data.Kernel.Misc.YamakiBicom
public import Certificates.Data.YamakiG3
public import CFSG.Certificates.Kernel.Sp62Pk.Sound

public section

namespace CFSG.KC.YamakiBicom

open CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.KD.YamakiBicom CFSG.KC.Misc.Spec Matrix
open CFSG.KD.Sp62 (MULF)
open CFSG.KC.Sp62 (MULF_lt pkMat_MULF pkMat_inj)

theorem bcPk_xor (a b : ℕ) : pkMat 6 (a ^^^ b) = pkMat 6 a + pkMat 6 b := by
  ext i j
  simp only [pkMat, Matrix.of_apply, Matrix.add_apply, Nat.testBit_xor]
  cases a.testBit (6 * i.val + j.val) <;> cases b.testBit (6 * i.val + j.val) <;> decide

theorem bcPk_zero : pkMat 6 0 = 0 := by
  ext i j
  simp [pkMat]

theorem bcComm_iff (X g : ℕ) :
    bcComm X g = true ↔ pkMat 6 X * pkMat 6 g = pkMat 6 g * pkMat 6 X := by
  unfold bcComm
  simp only [Nat.beq_eq]
  constructor
  · intro h
    rw [← pkMat_MULF, ← pkMat_MULF, h]
  · intro h
    exact pkMat_inj (MULF_lt _ _) (MULF_lt _ _) (by rw [pkMat_MULF, pkMat_MULF, h])

theorem bcAll_cons (X g : ℕ) (gs : List ℕ) :
    bcAll X (g :: gs) = (bcComm X g && bcAll X gs) := rfl

theorem bcAll_iff (X : ℕ) (gs : List ℕ) :
    bcAll X gs = true ↔ ∀ g ∈ gs, bcComm X g = true := by
  induction gs with
  | nil => exact ⟨fun _ g hg => absurd hg List.not_mem_nil, fun _ => rfl⟩
  | cons g gs ih => simp [bcAll_cons, ih]

theorem bcQ_sound {gs : List ℕ} {g8 X : ℕ} (h : bcQ gs g8 X = true)
    (hall : ∀ g ∈ gs, pkMat 6 X * pkMat 6 g = pkMat 6 g * pkMat 6 X) :
    pkMat 6 X * pkMat 6 g8 = pkMat 6 g8 * pkMat 6 X := by
  have hA : bcAll X gs = true := (bcAll_iff X gs).2 fun g hg => (bcComm_iff X g).2 (hall g hg)
  have e : bcQ gs g8 X = bcComm X g8 := by
    unfold bcQ
    rw [hA]
    rfl
  rw [e] at h
  exact (bcComm_iff X g8).1 h

@[expose] def bcSel : List Bool → List ℕ → ℕ
  | f :: fl, b :: bs => (if f then b else 0) ^^^ bcSel fl bs
  | _, _ => 0

theorem bcSel_cons (f : Bool) (fl : List Bool) (b : ℕ) (bs : List ℕ) :
    bcSel (f :: fl) (b :: bs) = (if f then b else 0) ^^^ bcSel fl bs := rfl

theorem bcSel_nil_left (bs : List ℕ) : bcSel [] bs = 0 := by
  cases bs <;> rfl

theorem bcSel_nil_right (fl : List Bool) : bcSel fl [] = 0 := by
  cases fl <;> rfl

theorem bcChk_cons (gs : List ℕ) (g8 b : ℕ) (bs : List ℕ) (acc : ℕ) :
    bcChk gs g8 (b :: bs) acc =
      (bcChk gs g8 bs acc && bcChk gs g8 bs (Nat.xor acc b)) := rfl

theorem bcChk_sel {gs : List ℕ} {g8 : ℕ} : ∀ (bs : List ℕ) (acc : ℕ),
    bcChk gs g8 bs acc = true → ∀ fl : List Bool, bcQ gs g8 (acc ^^^ bcSel fl bs) = true
  | [], acc, h, fl => by
    rw [bcSel_nil_right, Nat.xor_zero]
    exact h
  | b :: bs, acc, h, fl => by
    rw [bcChk_cons, Bool.and_eq_true] at h
    cases fl with
    | nil =>
      have h0 := bcChk_sel bs acc h.1 []
      rw [bcSel_nil_left] at h0 ⊢
      exact h0
    | cons f fl =>
      rw [bcSel_cons]
      cases f with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_xor]
        exact bcChk_sel bs acc h.1 fl
      | true =>
        simp only [↓reduceIte]
        rw [← Nat.xor_assoc]
        exact bcChk_sel bs (acc ^^^ b) h.2 fl

theorem wordVec_add (w : List (Fin 12)) (u v : Fin 3 ⊕ Fin 3 → ZMod 2) :
    bicomWordVec w (u + v) = bicomWordVec w u + bicomWordVec w v := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [bicomWordVec, List.foldr_cons] at ih ⊢
    rw [ih, Matrix.mulVec_add]

theorem wordVec_zero (w : List (Fin 12)) : bicomWordVec w 0 = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [bicomWordVec, List.foldr_cons] at ih ⊢
    rw [ih, Matrix.mulVec_zero]

theorem termsVec_add (y z : Fin 2 → Fin 3 ⊕ Fin 3 → ZMod 2) (l : List (Fin 2 × List (Fin 12))) :
    bicomTermsVec (y + z) l = bicomTermsVec y l + bicomTermsVec z l := by
  induction l with
  | nil => simp [bicomTermsVec]
  | cons t l ih =>
    simp only [bicomTermsVec, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Pi.add_apply, wordVec_add]
    abel

theorem termsVec_zero (l : List (Fin 2 × List (Fin 12))) : bicomTermsVec 0 l = 0 := by
  induction l with
  | nil => simp [bicomTermsVec]
  | cons t l ih =>
    simp only [bicomTermsVec, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, Pi.zero_apply, wordVec_zero, add_zero]

theorem bicomMat_add (y z : Fin 2 → Fin 3 ⊕ Fin 3 → ZMod 2) :
    bicomMat (y + z) = bicomMat y + bicomMat z := by
  ext r j
  simp only [bicomMat, Matrix.of_apply, Matrix.add_apply, termsVec_add, Pi.add_apply]

theorem bicomMat_zero : bicomMat 0 = 0 := by
  ext r j
  simp only [bicomMat, Matrix.of_apply, termsVec_zero, Pi.zero_apply, Matrix.zero_apply]

theorem bicomMat_listSum (l : List (Fin 2 → Fin 3 ⊕ Fin 3 → ZMod 2)) :
    bicomMat l.sum = (l.map bicomMat).sum := by
  induction l with
  | nil => simpa using bicomMat_zero
  | cons y l ih => rw [List.sum_cons, bicomMat_add, ih, List.map_cons, List.sum_cons]

theorem decomp (y : Fin 2 → Fin 3 ⊕ Fin 3 → ZMod 2) :
    y = (bcIdx.map fun p => Pi.single p.1 (Pi.single p.2 (y p.1 p.2))).sum := by
  funext k a
  fin_cases k <;> rcases a with a | a <;> fin_cases a <;> simp [bcIdx, Pi.single_apply]

theorem term_eq (k : Fin 2) (a : Fin 3 ⊕ Fin 3) (c : ZMod 2) :
    bicomMat (Pi.single k (Pi.single a c)) =
      if c = 1 then bicomMat (Pi.single k (Pi.single a 1)) else 0 := by
  have hc : c = 0 ∨ c = 1 := by
    revert c
    decide
  rcases hc with rfl | rfl
  · simp [bicomMat_zero]
  · simp

local notation "eF" => (finSumFinEquiv : Fin 3 ⊕ Fin 3 ≃ Fin (3 + 3))

theorem sub_add (A B : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    (A + B).submatrix eF eF = A.submatrix eF eF + B.submatrix eF eF := by
  ext i j
  simp

theorem sub_zero' : (0 : Matrix (Fin 6) (Fin 6) (ZMod 2)).submatrix eF eF = 0 := by
  ext i j
  simp

theorem sub_inj {A B : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (h : A.submatrix eF eF = B.submatrix eF eF) : A = B := by
  ext i j
  have := congrFun (congrFun h (Equiv.symm eF i)) (Equiv.symm eF j)
  simpa using this

theorem sub_comm (A B : Matrix (Fin 6) (Fin 6) (ZMod 2)) :
    A.submatrix eF eF * B.submatrix eF eF = B.submatrix eF eF * A.submatrix eF eF ↔
      A * B = B * A := by
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  exact ⟨fun h => sub_inj h, fun h => by rw [h]⟩

theorem sum_sel (y : Fin 2 → Fin 3 ⊕ Fin 3 → ZMod 2) :
    ∀ (l : List (Fin 2 × (Fin 3 ⊕ Fin 3))) (bs : List ℕ), l.length = bs.length →
    (∀ q ∈ List.zip l bs, bicomMat (Pi.single q.1.1 (Pi.single q.1.2 1)) =
      (pkMat 6 q.2).submatrix finSumFinEquiv finSumFinEquiv) →
    ((l.map fun p => Pi.single p.1 (Pi.single p.2 (y p.1 p.2))).map bicomMat).sum =
      (pkMat 6 (bcSel (l.map fun p => decide (y p.1 p.2 = 1)) bs)).submatrix
        finSumFinEquiv finSumFinEquiv
  | [], [], _, _ => by
    rw [List.map_nil, List.map_nil, List.sum_nil, List.map_nil, bcSel_nil_left, bcPk_zero,
      sub_zero']
  | p :: l, b :: bs, hlen, hB => by
    have hb := hB (p, b) (by simp)
    have ih := sum_sel y l bs (by simpa using hlen) (fun q hq => hB q (List.mem_cons_of_mem _ hq))
    rw [List.map_cons, List.map_cons, List.sum_cons, ih, List.map_cons, bcSel_cons, bcPk_xor,
      sub_add, term_eq]
    by_cases h1 : y p.1 p.2 = 1
    · simp only [h1, ↓reduceIte, decide_true]
      rw [hb]
    · simp only [h1, ↓reduceIte, decide_false, Bool.false_eq_true, bcPk_zero, sub_zero']
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

theorem forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, R a b
  | _, _, .nil, _, hb => absurd hb List.not_mem_nil
  | _, _, .cons (a := a) h t, b, hb => by
    rcases List.mem_cons.1 hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨a', ha', h'⟩ := forall₂_mem t b hb
      exact ⟨a', List.mem_cons_of_mem _ ha', h'⟩

theorem bicomCommute_of {gs bs : List ℕ} {g8 : ℕ} (hlen : bcIdx.length = bs.length)
    (hB : ∀ q ∈ List.zip bcIdx bs, bicomMat (Pi.single q.1.1 (Pi.single q.1.2 1)) =
      (pkMat 6 q.2).submatrix finSumFinEquiv finSumFinEquiv)
    (hG : List.Forall₂ (fun i g => yamakiMat6 i = pkMat 6 g) bicomLetters gs)
    (h8 : yamakiMat6 8 = pkMat 6 g8) (hc : bcChk gs g8 bs 0 = true) : BicomCommute := by
  intro y₁ y₂ hcomm
  generalize ![y₁, y₂] = y at hcomm ⊢
  have hX : bicomMat y = (pkMat 6 (bcSel (bcIdx.map fun p => decide (y p.1 p.2 = 1)) bs)).submatrix
      finSumFinEquiv finSumFinEquiv := by
    conv_lhs => rw [decomp y]
    rw [bicomMat_listSum]
    exact sum_sel y bcIdx bs hlen hB
  have hq := bcChk_sel bs 0 hc (bcIdx.map fun p => decide (y p.1 p.2 = 1))
  rw [Nat.zero_xor] at hq
  generalize bcSel (bcIdx.map fun p => decide (y p.1 p.2 = 1)) bs = X at hX hq
  have hall : ∀ g ∈ gs, pkMat 6 X * pkMat 6 g = pkMat 6 g * pkMat 6 X := by
    intro g hg
    obtain ⟨i, hi, hig⟩ := forall₂_mem hG g hg
    have h := hcomm i hi
    have hy : yamakiMat i = (pkMat 6 g).submatrix finSumFinEquiv finSumFinEquiv := by
      unfold yamakiMat
      rw [hig]
    rw [hX, hy] at h
    exact (sub_comm _ _).1 h
  have hy8 : yamakiMat 8 = (pkMat 6 g8).submatrix finSumFinEquiv finSumFinEquiv := by
    unfold yamakiMat
    rw [h8]
  rw [hX, hy8]
  exact (sub_comm _ _).2 (bcQ_sound hq hall)

end CFSG.KC.YamakiBicom
