module

public import CFSG.LargeExtraspecial.S9Cent

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S9

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Lbar_apply_mem_clSub (haQ : g * S.z * g⁻¹ ∈ S.QG) {l : S.O} (hl : l ∈ S.Lbar g)
    {p : S.Qt} (hp : p ∈ S.clSub (S.QG ⊓ S.Qa g)) :
    (l : S.Qt ≃ₗ[ZMod 2] S.Qt) p ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  have h1 := Lbar_apply_sub_mem_span' haQ hp hl
  have h2 : (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ≤ S.clSub (S.QG ⊓ S.Qa g) :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (cl_mem_clSub_self haQ)
  have := add_mem (h2 h1) hp
  rwa [sub_add_cancel] at this

theorem commute_Lbar_of_fix_clSub (H : Hyp4 S g) (C : Cons311 S g) {τ : S.O}
    (hτM : τ ∈ S.Mbar)
    (hτa : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (hτP : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g), (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p) :
    ∀ l ∈ S.Lbar g, τ * l = l * τ := by
  have haQ := H.conj_mem
  have hτN : τ ∈ normalizer (S.Lbar g : Set S.O) := by
    have := mem_normalizer_of_fix haQ H.conj_ne (h := 1) hτM (by simpa using hτa)
    simpa using this
  intro l hl
  have hc : τ * l * τ⁻¹ * l⁻¹ ∈ S.Lbar g :=
    mul_mem ((mem_normalizer_iff.mp hτN l).mp hl) (inv_mem hl)
  have hτiP : ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g), ((τ⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p :=
    fun p hp => by
      conv_lhs => rw [← hτP p hp]
      exact inv_apply_apply_O τ p
  have h1 : τ * l * τ⁻¹ * l⁻¹ = 1 := by
    refine C.faithful _ hc fun p hp => ?_
    have hlp := Lbar_apply_mem_clSub haQ (inv_mem hl) hp
    rw [coe_mul_apply, coe_mul_apply, coe_mul_apply, hτiP _ hlp, apply_inv_apply_O, hτP p hp]
  calc τ * l = (τ * l * τ⁻¹ * l⁻¹) * l * τ := by group
    _ = l * τ := by rw [h1, one_mul]

section Cent

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hSp : SpCase H C ht ht1 hVQ) {h : S.M} (hh : S.ρ h ∈ Rbar S g t)
  (hb : (h : G) * g * S.z * ((h : G) * g)⁻¹ ∉ S.Qa g)
include hCE H hNo C ht ht1 hVQ hSp hh hb

theorem commute_Abar_of_fix {τ : S.O} (hτM : τ ∈ S.Mbar) (hτt : τ * t = t * τ)
    (hτV : ∀ v ∈ Vt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v)
    (hτP : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Wt S g t, (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) w = w) :
    ∀ β ∈ S.Lbar g ⊓ Nbar S g t, τ * β = β * τ := by
  obtain ⟨α, hα, hyt, hyR⟩ :=
    exists_Abar_comm_mem_of_fix hCE H hNo C ht ht1 hVQ hSp hh hb hτM hτt hτV hτP
  have hyN := commute_Nbar_of_comm_mem hCE H C ht ht1 hVQ hSp hh hb hNo hyt hyR
  intro β hβ
  have h1 := hyN β hβ.2
  have hαβ : α * β = β * α := Lbar_comm S H.conj_mem hα.1 hβ.1
  calc τ * β = α * (α⁻¹ * τ * β) := by group
    _ = α * (β * (α⁻¹ * τ)) := by rw [h1]
    _ = (α * β) * α⁻¹ * τ := by group
    _ = (β * α) * α⁻¹ * τ := by rw [hαβ]
    _ = β * τ := by group

theorem fix_clSub_of_commute_Abar {τ : S.O} (hτM : τ ∈ S.Mbar)
    (hτa : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (hτA : ∀ β ∈ S.Lbar g ⊓ Nbar S g t, τ * β = β * τ)
    (hint : S.clSub (S.QG ⊓ S.Qa g) ⊓ Vone S g t g ((h : G) * g) ⊓
      commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥) :
    ∀ p ∈ S.clSub (S.QG ⊓ S.Qa g), (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p = p := by
  have haQ := H.conj_mem
  set E : Submodule (ZMod 2) S.Qt :=
    S.clSub (S.QG ⊓ S.Qa g) ⊓ commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) with hEdef
  have hE : E = ⊥ := by
    by_contra hne
    have hA2 : IsPGroup 2 ↥(S.Lbar g ⊓ Nbar S g t) :=
      (isPGroup_Lbar S haQ).to_le inf_le_left
    have hinv : ∀ x ∈ S.Lbar g ⊓ Nbar S g t, ∀ u ∈ E, (x : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ E := by
      rintro x hx u ⟨huP, huC⟩
      exact ⟨Lbar_apply_mem_clSub haQ hx.1 huP,
        S6.apply_mem_commSpace_of_commute (hτA x hx).symm huC⟩
    obtain ⟨u, huE, hu0, hfix⟩ := exists_fixed_of_isPGroup S hA2 hinv hne
    have h1 := pair_one (t := t) hb
    have hfixeq := clSub_inf_Vone_eq hCE H hNo C ht ht1 hVQ hSp h1.1 hh h1.2
    simp only [OneMemClass.coe_one, one_mul] at hfixeq
    have hu1 : u ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vone S g t g ((h : G) * g) := by
      rw [hfixeq]
      exact ⟨huE.1, (mem_fixSub S).mpr hfix⟩
    have hu2 : u ∈ S.clSub (S.QG ⊓ S.Qa g) ⊓ Vone S g t g ((h : G) * g) ⊓
        commSpace (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) := ⟨hu1, huE.2⟩
    rw [hint, Submodule.mem_bot] at hu2
    exact hu0 hu2
  intro p hp
  have hmem : (τ : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p ∈ E :=
    ⟨sub_mem (apply_mem_clSub_of_fix haQ H.conj_ne hτM hτa hp) hp, sub_mem_commSpace _ p⟩
  rw [hE, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem

end Cent

end CFSG.LargeExtraspecial.S9
