module

public import Certificates.Data.Kernel.ONanSmall.EdgeK
public import Mathlib.Tactic.Group

public section

namespace CFSG.KC.ONanSmall

open CFSG.ClassicalInvolution.Q3.TA3.Check

variable {M : Type*} [Group M] [DecidableEq M]

theorem conj_comm_iff (g r t : M) :
    g * r * g⁻¹ * t = t * (g * r * g⁻¹) ↔ r * (g⁻¹ * t * g) = g⁻¹ * t * g * r := by
  have e1 : g⁻¹ * (g * r * g⁻¹ * t) * g = r * (g⁻¹ * t * g) := by group
  have e2 : g⁻¹ * (t * (g * r * g⁻¹)) * g = g⁻¹ * t * g * r := by group
  constructor
  · intro h
    rw [← e1, ← e2, h]
  · intro h
    have : g⁻¹ * (g * r * g⁻¹ * t) * g = g⁻¹ * (t * (g * r * g⁻¹)) * g := by rw [e1, e2, h]
    exact mul_left_cancel (mul_right_cancel this)

theorem conj_eq_iff (g r t : M) : g * r * g⁻¹ = t ↔ r = g⁻¹ * t * g := by
  constructor
  · intro h
    rw [← h]
    group
  · intro h
    rw [h]
    group

theorem edgelessB_of_edgeK {L K : List M} {t a b : M} (hK : ∀ g ∈ L, g⁻¹ * t * g ∈ K)
    (h : edgeK K t a b = true) : edgelessB L t a b = true := by
  unfold edgelessB
  unfold edgeK at h
  rw [List.all_eq_true] at h ⊢
  intro g hg
  have hs := h _ (hK g hg)
  simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, List.all_eq_false,
    decide_eq_false_iff_not, memB, List.any_eq_true, decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨r, hr, hne⟩ | ⟨r, hr, he⟩
  · exact Or.inl ⟨r, hr, fun e => hne ((conj_comm_iff g r t).1 e)⟩
  · exact Or.inr ⟨r, hr, (conj_eq_iff g r t).2 he⟩

theorem pairsV_of_pairsVK {B : ℕ} {LN L K : List M} {e3b : Bool} {t : M} {C : List M}
    (hK : ∀ g ∈ L, g⁻¹ * t * g ∈ K) (h : pairsVK B LN K e3b t C = true) :
    pairsV B LN L e3b t C = true := by
  unfold pairsVK at h
  unfold pairsV
  rw [List.all_eq_true] at h ⊢
  intro a ha
  have h := h a ha
  rw [List.all_eq_true] at h ⊢
  intro b hb
  have hab := h b hb
  have key := @edgelessB_of_edgeK _ _ _ L K t a b hK
  have mono : ∀ P x y z : Bool, (x = true → y = true) → (P || (x && z)) = true →
      (P || (y && z)) = true := by decide
  exact mono _ _ _ _ key hab

end CFSG.KC.ONanSmall
