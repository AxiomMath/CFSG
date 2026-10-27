module

public import CFSG.LargeExtraspecial.S13TwoK
public import CFSG.LargeExtraspecial.S13TwoJ

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S13

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.S10

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g g₁ : G} {K : Subgroup S.O}

section Four

variable (hCE : CentralExtInput.{u}) (Y : Hyp13 S g K) {h : S.M} (hg : g₁ = (h : G) * g)
  (hperp : ∀ u ∈ Fbar S g K, ∀ v ∈ Fbar S g₁ K, polar S.q u v = 0)
  (hne : Fbar S g₁ K ≠ Fbar S g K) (hbot : Ebar S g K ⊓ Ebar S g₁ K = ⊥)
include hCE Y hg hperp hne hbot

theorem Abar_eq_and_Vt_eq {s : S.O} (X : Hyp10 S g s)
    (hs : s ∈ Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K)) :
    S.Lbar g ⊓ Nbar S g s = Ebar S g K ⊓ ptStab S (Fbar S g K ⊔ Fbar S g₁ K) ∧
      Vt S g s = Fbar S g K ⊔ Fbar S g₁ K := by
  set D := Fbar S g K ⊔ Fbar S g₁ K with hD
  set T₀ := Ebar S g K ⊓ ptStab S D with hT₀
  set A := S.Lbar g ⊓ Nbar S g s with hA
  have Y₁ : Hyp13 S g₁ K := Y.mul hg
  have hg' : g = ((h⁻¹ : S.M) : G) * g₁ := by rw [hg, Subgroup.coe_inv]; group
  have hD' : (Fbar S g₁ K ⊔ Fbar S g K : Submodule (ZMod 2) S.Qt) = D := sup_comm _ _
  have hAE : A ≤ Ebar S g K := Y.Abar_le_Ebar hCE X
  have hcardA : Nat.card A = Nat.card T₀ := by
    have h1 := card_Ebar_eq_two_mul Y hg hperp hne
    rw [← hD, ← hT₀, Y.card_Ebar] at h1
    rw [hA, X.card_Abar]
    have h7 := Y.seven_le
    have e : 2 ^ (S.width - 2) = 2 * 2 ^ (S.width - 3) := by
      rw [show S.width - 2 = (S.width - 3) + 1 by omega, pow_succ]
      ring
    omega
  have hnorm : ∀ y ∈ Ebar S g₁ K ⊓ ptStab S D, ∀ x ∈ A, y * x * y⁻¹ ∈ A := by
    intro y hy x hx
    have hys : y * s = s * y := (comm_T₀_T₁ Y hg hperp hbot hs hy).symm
    have hyM : y ∈ S.Mbar := Hyp13.Ebar_le_Mbar (Subgroup.mem_inf.mp hy).1
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hyM
    have hy' : S.ρ m ∈ ptStab S (Fbar S g₁ K ⊔ Fbar S g K) := by
      rw [hD']; exact (Subgroup.mem_inf.mp hy).2
    have hxE : S.ρ m * x * (S.ρ m)⁻¹ ∈ Ebar S g K :=
      conj_mem_Ebar₁ Y₁ hg' hyM hy' (hAE hx)
    exact Subgroup.mem_inf.mpr ⟨Ebar_le_Lbar hxE,
      conj_mem_Nbar X.haQ hys (Subgroup.mem_inf.mp hx).2⟩
  have hAT : A = T₀ := by
    by_cases hle : A ≤ T₀
    · exact Subgroup.eq_of_le_of_card_ge hle hcardA.ge
    · exfalso
      obtain ⟨x, hxA, hxT⟩ := Set.not_subset.mp hle
      have hTA : T₀ ≤ A := by
        intro w hw
        obtain ⟨y, hy, hyw⟩ := exists_comm_eq Y hg hperp hne hbot (hAE hxA) hxT hw
        rw [← hyw]
        have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
        rw [e]
        exact mul_mem hxA (hnorm y hy _ (inv_mem hxA))
      exact hxT (Subgroup.eq_of_le_of_card_ge hTA hcardA.le ▸ hxA)
  refine ⟨hAT, ?_⟩
  have hle : Vt S g s ≤ fixSub S T₀ := by
    intro v hv x hx
    rw [← hAT] at hx
    exact (Subgroup.mem_inf.mp hx).2.2 v hv
  rw [fixSub_T₀_eq Y hg hperp hne] at hle
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [X.h4, finrank_Dbar Y Y₁ hne])

end Four

end CFSG.LargeExtraspecial.S13
