module

public import CFSG.LargeExtraspecial.S10Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

structure Frame (X : Hyp10 S g t) where
  π : Rbar S g t →* Gm
  φ : Vt S g t ≃ₗ[ZMod 2] M2
  surj : Function.Surjective π
  ker : ∀ r, π r = 1 ↔ (r : S.O) ∈ Nbar S g t
  compat : ∀ r v, φ (resV X.haQ t r v) = act (π r) (φ v)
  base : φ (aV X.ht) = E00
  beta_eq : ∀ v w, beta X.H X.C X.ht X.ht1 X.hVQ v w = pf (φ v) (φ w)
  sing : ∀ v : Vt S g t, v ≠ 0 → (v ∈ orbitOf (RmodN S g t) (aV X.ht) ↔ qf (φ v) = 0)

namespace Hyp10

variable (X : Hyp10 S g t)

theorem exists_frame : Nonempty (Frame X) := by
  obtain ⟨Q, hQ, hpol, hX, hE, hsing⟩ := X.hΩ.exists_form
  have hP : PlusType4 Q := (plusType4_iff hsing).mpr X.plus
  have hQa : Q (aV X.ht) = 0 := (hsing _ (aV_ne_zero X.H X.ht)).mpr ⟨1, one_mem _, rfl⟩
  obtain ⟨φ, hφ, hφa⟩ := exists_isometry_M2_base X.h4 hQ hP (aV_ne_zero X.H X.ht) hQa
  set ψ := psi φ with hψ
  have hψR : ψ.range = RmodN S g t := by rw [hψ, range_psi hφ hQ, hX]
  set e := MonoidHom.ofInjective (psi_injective (φ := φ)) with he
  have hmem : ∀ r, resV X.haQ t r ∈ ψ.range := fun r => by
    rw [hψR, ← range_resV X.haQ t]
    exact ⟨r, rfl⟩
  set π : Rbar S g t →* Gm :=
    e.symm.toMonoidHom.comp ((resV X.haQ t).codRestrict ψ.range hmem) with hπ
  have hψπ : ∀ r, ψ (π r) = resV X.haQ t r := fun r => by
    have h := MonoidHom.ofInjective_apply (psi_injective (φ := φ)) (x := e.symm ⟨_, hmem r⟩)
    rw [← he, MulEquiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨⟨π, φ, fun γ => ?_, fun r => ?_, fun r v => ?_, hφa, fun v w => ?_, fun v hv0 => ?_⟩⟩
  · have h1 : ψ γ ∈ RmodN S g t := hψR ▸ ⟨γ, rfl⟩
    rw [← range_resV X.haQ t] at h1
    obtain ⟨r, hr⟩ := h1
    refine ⟨r, psi_injective (φ := φ) ?_⟩
    rw [hψπ, hr]
  · rw [← resV_eq_one_iff X.haQ, ← hψπ]
    constructor
    · intro h
      rw [h, map_one]
    · intro h
      exact psi_injective (φ := φ) (h.trans (map_one ψ).symm)
  · rw [← hψπ r, hψ, psi_apply, LinearEquiv.apply_symm_apply]
  · rw [← hpol, polarBilin_apply_apply, ← polar_q₀]
    simp only [polar, ← hφ, map_add]
  · rw [← hsing v hv0, ← hφ, q₀_apply]

end Hyp10

namespace Frame

variable {X : Hyp10 S g t} (F : Frame X)
include F

theorem compat' (r : Rbar S g t) {x : S.Qt} (hx : x ∈ Vt S g t) :
    F.φ ⟨((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) x, apply_mem_Vt_of_mem_Rbar X.haQ r.2 hx⟩ =
      act (F.π r) (F.φ ⟨x, hx⟩) :=
  F.compat r ⟨x, hx⟩

theorem card_Rbar : Nat.card (Rbar S g t) = 36 * Nat.card (Nbar S g t) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup F.π.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective F.π F.surj).toEquiv,
    card_Gm] at h1
  have hker : F.π.ker = (Nbar S g t).subgroupOf (Rbar S g t) := by
    ext r
    rw [MonoidHom.mem_ker, mem_subgroupOf, F.ker]
  rw [h1, hker, Nat.card_congr (subgroupOfEquivOfLe (Nbar_le_Rbar (S := S))).toEquiv]

theorem act_E00_of_fix (r : Rbar S g t)
    (hr : ((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) :
    act (F.π r) E00 = E00 := by
  rw [← F.base, ← F.compat]
  congr 1
  exact Subtype.ext hr

end Frame

end CFSG.LargeExtraspecial.S10
