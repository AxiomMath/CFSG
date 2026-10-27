module

public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.OddStandard.SmallF3.FritzII

private def fzlCover (a b g : Equiv.Perm (Fin 4)) : Prop :=
  g = 1 ∨ g = a ∨ g = a ^ 2 ∨ g = b ∨ g = a * b ∨ g = a ^ 2 * b

private instance (a b g : Equiv.Perm (Fin 4)) : Decidable (fzlCover a b g) := by
  unfold fzlCover; infer_instance

private def fzlPair (a b : Equiv.Perm (Fin 4)) : Prop :=
  a 0 = 0 ∧ b 0 = 0 ∧ a ^ 3 = 1 ∧ a ≠ 1 ∧ b ^ 2 = 1 ∧ b ≠ 1 ∧ b * a * b⁻¹ = a⁻¹

private instance (a b : Equiv.Perm (Fin 4)) : Decidable (fzlPair a b) := by
  unfold fzlPair; infer_instance

private theorem fzl_perm4_cover :
    ∀ a b g : Equiv.Perm (Fin 4), fzlPair a b → g 0 = 0 → fzlCover a b g := by
  decide +kernel

theorem fzl_perm4_eq_top (H : Subgroup (Equiv.Perm (Fin 4)))
    (htrans : ∀ i : Fin 4, ∃ h ∈ H, h 0 = i) {a b : Equiv.Perm (Fin 4)} (ha : a ∈ H)
    (hb : b ∈ H) (ha0 : a 0 = 0) (hb0 : b 0 = 0) (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hb2 : b ^ 2 = 1) (hb1 : b ≠ 1) (hba : b * a * b⁻¹ = a⁻¹) : H = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro σ
  obtain ⟨h, hh, hh0⟩ := htrans (σ 0)
  have hg0 : (h⁻¹ * σ) 0 = 0 := by
    simp [Equiv.Perm.mul_apply, ← hh0]
  have key := fzl_perm4_cover a b (h⁻¹ * σ) ⟨ha0, hb0, ha3, ha1, hb2, hb1, hba⟩ hg0
  have hmem : h⁻¹ * σ ∈ H := by
    rcases key with h1 | h2 | h3 | h4 | h5 | h6
    · rw [h1]; exact H.one_mem
    · rw [h2]; exact ha
    · rw [h3]; exact H.pow_mem ha 2
    · rw [h4]; exact hb
    · rw [h5]; exact H.mul_mem ha hb
    · rw [h6]; exact H.mul_mem (H.pow_mem ha 2) hb
  have : σ = h * (h⁻¹ * σ) := by rw [mul_inv_cancel_left]
  rw [this]
  exact H.mul_mem hh hmem

end CFSG.OddStandard.SmallF3.FritzII
