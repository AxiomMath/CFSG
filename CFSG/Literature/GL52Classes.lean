module

public import CFSG.Literature.GL52Local
public import CFSG.Literature.GL52LocalS

public section

namespace CFSG.Literature.GL52

open CFSG CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native

theorem fixCount_conj (g x : G) : fixCount (g * x * g⁻¹) = fixCount x := by
  unfold fixCount
  refine Finset.card_bij (fun i _ => glPerm g⁻¹ i) (fun i hi => ?_) (fun i _ j _ h => ?_)
    (fun j hj => ⟨glPerm g j, ?_, ?_⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_inv,
      Equiv.Perm.mul_apply] at hi ⊢
    have := congrArg (glPerm g).symm hi
    simpa [Equiv.Perm.inv_def] using this
  · exact (glPerm g⁻¹).injective h
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_mul, map_inv,
      Equiv.Perm.mul_apply] at hj ⊢
    simp [hj]
  · simp

theorem card_split (P Q : G → Prop) :
    Nat.card {x : G // P x} = Nat.card {x : G // P x ∧ Q x} + Nat.card {x : G // P x ∧ ¬ Q x} := by
  classical
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Finset.card_filter_add_card_filter_not (p := Q) (s := Finset.univ.filter P),
    Finset.filter_filter, Finset.filter_filter]

theorem empty_of_card_zero {P : G → Prop} (h : Nat.card {x : G // P x} = 0) (x : G) :
    ¬ P x := by
  intro hx
  have : Nonempty {x : G // P x} := ⟨⟨x, hx⟩⟩
  have := Nat.card_pos (α := {x : G // P x})
  omega

theorem card_class (x : G) (n : ℕ) (hn : Nat.card (Subgroup.centralizer {x}) = n) (m : ℕ)
    (hm : m * n = 9999360) : Nat.card {y : G // IsConj x y} = m := by
  have h := card_isConj_mul_card_centralizer x
  rw [hn, card_G_eq, ← hm] at h
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · rw [h0] at hm; omega
    · exact h0
  exact Nat.eq_of_mul_eq_mul_right hn0 h

theorem order_three_fixCount
    {x : G} (hx : orderOf x = 3) : fixCount x = 1 ∨ fixCount x = 7 := by
  by_contra hne
  push Not at hne
  have h1 := card_split (fun y => orderOf y = 3) (fun y => fixCount y = 1)
  have h2 := card_split (fun y => orderOf y = 3 ∧ ¬ fixCount y = 1) (fun y => fixCount y = 7)
  have e1 : Nat.card {x : G // orderOf x = 3 ∧ fixCount x = 1} = 55552 := by
    simpa using card_order_three_fix 1 (Or.inl rfl)
  have e2 : Nat.card {x : G // orderOf x = 3 ∧ fixCount x = 7} = 19840 := by
    simpa using card_order_three_fix 7 (Or.inr rfl)
  rw [card_order_three] at h1
  have e2' : Nat.card {y : G // (orderOf y = 3 ∧ ¬ fixCount y = 1) ∧ fixCount y = 7} = 19840 := by
    rw [← e2]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by
      constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨h, by rw [h']; norm_num⟩, h'⟩)
  have hz : Nat.card {y : G // (orderOf y = 3 ∧ ¬ fixCount y = 1) ∧ ¬ fixCount y = 7} = 0 := by
    omega
  exact empty_of_card_zero hz x ⟨⟨hx, hne.1⟩, hne.2⟩

theorem isConj_tau1
    {x : G} (hx : orderOf x = 3) (hf : fixCount x = 1) : IsConj glTau1 x :=
  isConj_of_card_le glTau1 (fun y => orderOf y = 3 ∧ fixCount y = 1) ⟨orderOf_tau1, fixCount_tau1⟩
    (fun g y hy => ⟨(orderOf_conj g y).trans hy.1, (fixCount_conj g y).trans hy.2⟩)
    (by rw [card_class glTau1 180 card_centralizer_tau1 55552 (by norm_num),
      card_order_three_fix 1 (Or.inl rfl)]; simp) x ⟨hx, hf⟩

theorem isConj_tau2
    {x : G} (hx : orderOf x = 3) (hf : fixCount x = 7) : IsConj glTau2 x :=
  isConj_of_card_le glTau2 (fun y => orderOf y = 3 ∧ fixCount y = 7) ⟨orderOf_tau2, fixCount_tau2⟩
    (fun g y hy => ⟨(orderOf_conj g y).trans hy.1, (fixCount_conj g y).trans hy.2⟩)
    (by rw [card_class glTau2 504 card_centralizer_tau2 19840 (by norm_num),
      card_order_three_fix 7 (Or.inr rfl)]; simp) x ⟨hx, hf⟩

end CFSG.Literature.GL52
