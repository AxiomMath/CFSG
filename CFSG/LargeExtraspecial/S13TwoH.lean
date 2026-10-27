module

public import CFSG.LargeExtraspecial.S13TwoE

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

theorem Hyp13.Fbar_le_Vt (Y : Hyp13 S g K) {g₀ : G} {h₀ : S.M} (hg₀ : g = (h₀ : G) * g₀)
    {x : S.O} (hx : x ∈ Ebar S g K) : Fbar S g K ≤ Vt S g₀ x := by
  intro u hu
  by_cases hu0 : u = 0
  · rw [hu0]; exact zero_mem _
  obtain ⟨m, hm, rfl⟩ := Y.exists_eq_cl_of_mem_Fbar hu hu0
  have hx' := Hyp13.Ebar_le_Lbar_mul (g := g) hm hx
  rw [hg₀, ← mul_assoc, ← Subgroup.coe_mul] at hx' ⊢
  exact cl_mem_Vt hx'

section Three

variable (Y : Hyp13 S g K) {h : S.M} (hg : g₁ = (h : G) * g)
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0)
  (hne : Fbar S g₁ K ≠ Fbar S g K)
include Y hg hperp hne

omit hperp in
theorem hyp10_and_Vt_eq_of_mem_inf {x : S.O} (hx : x ∈ Ebar S g K ⊓ Ebar S g₁ K)
    (hx1 : x ≠ 1) : Hyp10 S g x ∧ Vt S g x = Fbar S g K ⊔ Fbar S g₁ K := by
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  rcases Y.one x hx.1 hx1 with hD | X
  · exfalso
    apply hne
    have hxL : x ∈ S.Lbar ((h : G) * g) := hg ▸ Ebar_le_Lbar hx.2
    have hle : Ebar S g K ≤ S.Lbar g₁ := hg ▸ hD _ (Lbar_mul_mem_Dset hxL)
    have hle' : Ebar S g K ≤ Ebar S g₁ K := fun e he =>
      (mem_Ebar).mpr ⟨hle he, ((mem_Ebar).mp he).2⟩
    have hcard : Nat.card (Ebar S g₁ K) = Nat.card (Ebar S g K) := by
      rw [Y₁.card_Ebar, Y.card_Ebar]
    have heq := Subgroup.eq_of_le_of_card_ge hle' hcard.le
    simp only [Fbar, heq]
  · refine ⟨X, (Submodule.eq_of_le_of_finrank_le (sup_le ?_ ?_) ?_).symm⟩
    · exact Y.Fbar_le_Vt (h₀ := 1) (by simp) hx.1
    · have h1 := Y₁.Fbar_le_Vt (g₀ := g) hg hx.2
      exact h1
    · rw [X.h4, finrank_Dbar Y Y₁ hne]

end Three

section Four

variable (Y : Hyp13 S g K) {h : S.M} (hg : g₁ = (h : G) * g)
include Y hg

theorem conj_mem_Ebar₁ {c : S.O} (hcM : c ∈ S.Mbar)
    (hc : c ∈ ptStab S (Fbar S g K ⊔ Fbar S g₁ K)) {e : S.O} (he : e ∈ Ebar S g₁ K) :
    c * e * c⁻¹ ∈ Ebar S g₁ K := by
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hfix := hc _ (Submodule.mem_sup_right (cl_mem_Fbar Y₁.H))
  have hN : c ∈ normalizer (S.Lbar g₁ : Set S.O) := by
    have := mem_normalizer_of_fix (S := S) Y₁.haQ Y₁.hne (h := 1) hcM (by simpa using hfix)
    simpa using this
  refine (mem_Ebar).mpr ⟨(mem_normalizer_iff.mp hN e).mp (Ebar_le_Lbar he), fun k hk => ?_⟩
  have hk' := Y.normal _ (inv_mem hcM) k hk
  rw [inv_inv] at hk'
  have e1 := ((mem_Ebar).mp he).2 _ hk'
  calc k * (c * e * c⁻¹) = c * ((c⁻¹ * k * c) * e) * c⁻¹ := by group
    _ = c * (e * (c⁻¹ * k * c)) * c⁻¹ := by rw [e1]
    _ = c * e * c⁻¹ * k := by group

end Four

end CFSG.LargeExtraspecial.S13
