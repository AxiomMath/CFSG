module

public import Certificates.Data.Kernel.Sp43KOrb
public import CFSG.Certificates.Kernel.Sp43KGrp
public import CFSG.LocalAnalysis.AGL81I.Section3.Sp43.Closure

public section

namespace CFSG.KC.Sp43K

open CFSG.Sp43 Subgroup

theorem ofT_inv_of_mulT {n n' : ℕ} (hn : InG n) (hn' : InG n') (h : mulT n n' = oneT) :
    ofT n' = (ofT n)⁻¹ := by
  have : ofT n * ofT n' = 1 := by rw [← ofT_mulT hn hn', h, ofT_oneT]
  exact eq_inv_of_mul_eq_one_right this

theorem inG_conjT {n n' c : ℕ} (hn : InG n) (hn' : InG n') (hc : InG c) : InG (conjT n n' c) :=
  inG_mulT (inG_mulT hn hc) hn'

theorem ofT_conjT {n n' c : ℕ} (hn : InG n) (hn' : InG n') (hc : InG c) (h : mulT n n' = oneT) :
    ofT (conjT n n' c) = ofT n * ofT c * (ofT n)⁻¹ := by
  unfold conjT
  rw [ofT_mulT (inG_mulT hn hc) hn', ofT_mulT hn hc, ofT_inv_of_mulT hn hn' h]

theorem mem_normalizer_sub2T {a b n n' : ℕ} (ha : InG a) (hb : InG b) (hn : InG n)
    (hn' : InG n') (h : mulT n n' = oneT) (h1 : ofT (conjT n n' a) ∈ sub2T a b)
    (h2 : ofT (conjT n n' b) ∈ sub2T a b) : ofT n ∈ normalizer (sub2T a b : Set G) := by
  apply mem_normalizer_of_conj (s := {ofT a, ofT b})
  rintro k (rfl | rfl)
  · rw [← ofT_conjT hn hn' ha h]
    exact h1
  · rw [← ofT_conjT hn hn' hb h]
    exact h2

theorem wordGo_mem {a b : ℕ} (ha : InG a) (hb : InG b) {H : Subgroup G} (haH : ofT a ∈ H)
    (hbH : ofT b ∈ H) :
    ∀ (w : List ℕ) (acc : ℕ), InG acc → ofT acc ∈ H →
      InG (wordGo a b w acc) ∧ ofT (wordGo a b w acc) ∈ H
  | [], _, h1, h2 => ⟨h1, h2⟩
  | l :: w, acc, h1, h2 => by
    have e : wordGo a b (l :: w) acc = wordGo a b w (mulT acc (genT a b l)) := rfl
    have hg : InG (genT a b l) ∧ ofT (genT a b l) ∈ H := by
      unfold genT
      split
      · exact ⟨ha, haH⟩
      · exact ⟨hb, hbH⟩
    rw [e]
    refine wordGo_mem ha hb haH hbH w _ (inG_mulT h1 hg.1) ?_
    rw [ofT_mulT h1 hg.1]
    exact H.mul_mem h2 hg.2

theorem wordT_mem {a b : ℕ} (ha : InG a) (hb : InG b) (w : List ℕ) :
    InG (wordT a b w) ∧ ofT (wordT a b w) ∈ sub2T a b :=
  wordGo_mem ha hb (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) w
    oneT inG_oneT (by rw [ofT_oneT]; exact Subgroup.one_mem _)

@[expose] def minusT : ℕ := oneT <<< 16

theorem toMT_minusT : toMT minusT = -1 := by
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;> decide

theorem okT_minusT : okT minusT = true := by decide

theorem coe_ofT_minusT (h : InG minusT) :
    ((ofT minusT : G) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3)) = -1 := by
  rw [coe_ofT h, toMT_minusT]

theorem minusT_center (h : InG minusT) : ofT minusT ∈ center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  rw [MulMemClass.coe_mul, MulMemClass.coe_mul, coe_ofT_minusT h, mul_neg_one, neg_one_mul]

theorem minusT_ne_one (h : InG minusT) : ofT minusT ≠ 1 := by
  intro e
  have := congrArg (fun x : G => (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3))) e
  simp only [coe_ofT_minusT h, OneMemClass.coe_one] at this
  have h2 := congrFun (congrFun this (.inl 0)) (.inl 0)
  simp only [Matrix.neg_apply, Matrix.one_apply_eq] at h2
  exact absurd h2 (by decide)

theorem minusT_sq (h : InG minusT) : ofT minusT ^ 2 = 1 := by
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, coe_ofT_minusT h, OneMemClass.coe_one, neg_one_sq]

end CFSG.KC.Sp43K

end
