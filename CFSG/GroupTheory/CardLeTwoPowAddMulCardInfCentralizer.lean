module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

import CFSG.GH74.GLS.IVK.Proofs2.GHInvAutRank

public section

namespace CFSG.GroupTheory

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem card_le_two_pow_add_mul_card_inf_centralizer {K : Type} [Group K] [Finite K]
    (X : Subgroup K) [X.Normal] (hZ : Subgroup.center ↥X = ⊥) {r s : ℕ}
    (hX : ∀ E : Subgroup ↥X, (∀ e ∈ E, e * e = 1) → Nat.card ↥E ≤ 2 ^ r)
    (hOut : ∀ E : Subgroup (Outer ↥X), (∀ e ∈ E, e * e = 1) → Nat.card ↥E ≤ 2 ^ s)
    (A : Subgroup K) (hA : ∀ e ∈ A, e * e = 1) :
    Nat.card ↥A ≤ 2 ^ (r + s) * Nat.card ↥(A ⊓ Subgroup.centralizer (X : Set K)) := by
  let Φ : K →* MulAut ↥X := MulAut.conjNormal
  have hker : Φ.ker = Subgroup.centralizer (X : Set K) := by
    ext g
    rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
    constructor
    · intro hg h hh
      have h1 := congrArg (fun φ : MulAut ↥X => (φ ⟨h, hh⟩ : K)) hg
      simp only [Φ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc h * g = (g * h * g⁻¹) * g := by rw [h1]
        _ = g * h := by group
    · intro hg
      ext ⟨h, hh⟩
      have h1 := hg h hh
      simp only [Φ, MulAut.conjNormal_apply, MulAut.one_apply]
      calc g * h * g⁻¹ = (h * g) * g⁻¹ := by rw [h1]
        _ = h := by group
  have h1 : Nat.card ↥A = Nat.card ↥(A.map Φ) * Nat.card ↥(A ⊓ Φ.ker) := by
    have h := Subgroup.relIndex_mul_card Φ.ker A
    rw [Subgroup.relIndex_ker, inf_comm] at h
    exact h.symm
  have h2 : Nat.card ↥(A.map Φ) ≤ 2 ^ (r + s) :=
    CFSG.GH74.GLS.IVK.GHInv.card_le_two_pow_add_of_aut hZ hX hOut (A.map Φ) (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul, hA a ha, map_one])
  rw [h1, hker]
  exact Nat.mul_le_mul_right _ h2

end CFSG.GroupTheory
