module

public import CFSG.ClassicalInvolution.AschTight.S1911FusC

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {K : Subgroup G} {F : Type} [Field F]

noncomputable abbrev slFix (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    (n : Subgroup.normalizer (K : Set G)) : Subgroup SL(2, F) :=
  MonoidHom.eqLocus (slAut K e n).toMonoidHom (MonoidHom.id SL(2, F))

noncomputable def centralizerToFix (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    ↥(K ⊓ Subgroup.centralizer ({a} : Set G)) →* ↥(slFix e ⟨a, haN⟩) :=
  ((slProj K e).comp (Subgroup.inclusion inf_le_left)).codRestrict _ fun c => by
    change slAut K e ⟨a, haN⟩ (slProj K e (Subgroup.inclusion inf_le_left c)) =
      slProj K e (Subgroup.inclusion inf_le_left c)
    rw [slAut_slProj]
    congr 1
    apply Subtype.ext
    rw [normalizerConj_apply_coe]
    have hc := Subgroup.mem_centralizer_singleton_iff.mp c.2.2
    change a * c * a⁻¹ = c
    rw [← hc]
    group

theorem centralizerToFix_surjective (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha2 : a * a = 1) :
    Function.Surjective (centralizerToFix e haN) := by
  rintro ⟨b, hb⟩
  obtain ⟨c, hca, hcb⟩ := exists_mem_centralizer_of_slAut_eq e haN ha2 hb
  exact ⟨⟨c, c.2, hca⟩, Subtype.ext hcb⟩

noncomputable def perfectCoreToFix (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G)) :
    ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) →* ↥(slFix e ⟨a, haN⟩) :=
  ((centralizerToFix e haN).comp (Helpers.perfectResidual _).subtype).comp
    (Subgroup.equivMapOfInjective _ _
      (K ⊓ Subgroup.centralizer ({a} : Set G)).subtype_injective).symm.toMonoidHom

omit [Finite G] in
theorem perfectResidualOf_le (H : Subgroup G) : perfectResidualOf H ≤ H :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem coe_perfectCoreToFix (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F)) {a : G}
    (haN : a ∈ Subgroup.normalizer (K : Set G))
    (x : ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))) :
    ((perfectCoreToFix e haN x : ↥(slFix e ⟨a, haN⟩)) : SL(2, F)) =
      slProj K e ⟨x, (perfectResidualOf_le _ x.2).1⟩ := by
  set y := (Subgroup.equivMapOfInjective _ _
    (K ⊓ Subgroup.centralizer ({a} : Set G)).subtype_injective).symm x with hy
  have hyx : (((y : ↥(K ⊓ Subgroup.centralizer ({a} : Set G))) : G)) = x := by
    have h := congrArg Subtype.val (MulEquiv.apply_symm_apply (Subgroup.equivMapOfInjective _ _
      (K ⊓ Subgroup.centralizer ({a} : Set G)).subtype_injective) x)
    rw [← hy] at h
    exact h
  change slProj K e
    (Subgroup.inclusion inf_le_left (y : ↥(K ⊓ Subgroup.centralizer ({a} : Set G)))) = _
  congr 1
  exact Subtype.ext hyx

theorem nonempty_quotEquiv_perfectResidualOf (e : K ⧸ classicalInvolutionOddCore K ≃* SL(2, F))
    {a : G} (haN : a ∈ Subgroup.normalizer (K : Set G)) (ha2 : a * a = 1)
    (hperf : Group.IsPerfect ↥(slFix e ⟨a, haN⟩))
    (hO : classicalInvolutionOddCore ↥(slFix e ⟨a, haN⟩) = ⊥) :
    Nonempty (↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ⧸
      classicalInvolutionOddCore ↥(perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G))) ≃*
        ↥(slFix e ⟨a, haN⟩)) := by
  have := hperf
  have hsurj : Function.Surjective (perfectCoreToFix e haN) := by
    have hmap := finite_perfectResidual_surjects_to_perfect_image (centralizerToFix e haN)
      (centralizerToFix_surjective e haN ha2)
    intro b
    have hb : b ∈ (Helpers.perfectResidual _).map (centralizerToFix e haN) := by
      rw [hmap]
      trivial
    obtain ⟨y, hy, hyb⟩ := hb
    set E := Subgroup.equivMapOfInjective (Helpers.perfectResidual _)
      (K ⊓ Subgroup.centralizer ({a} : Set G)).subtype
      (K ⊓ Subgroup.centralizer ({a} : Set G)).subtype_injective with hE
    refine ⟨E ⟨y, hy⟩, ?_⟩
    have e1 : perfectCoreToFix e haN (E ⟨y, hy⟩) = centralizerToFix e haN y := by
      change centralizerToFix e haN ((Helpers.perfectResidual _).subtype (E.symm (E ⟨y, hy⟩))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    exact e1.trans hyb
  have hker : Odd (Nat.card (perfectCoreToFix e haN).ker) := by
    have hle : (perfectCoreToFix e haN).ker.map (perfectResidualOf _).subtype ≤ oddCoreOf K := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : perfectCoreToFix e haN x = 1 := hx
      have h1 := congrArg Subtype.val hx'
      rw [coe_perfectCoreToFix] at h1
      exact (slProj_eq_one_iff e _).mp h1
    have hcard : Nat.card ((perfectCoreToFix e haN).ker.map (perfectResidualOf _).subtype) =
        Nat.card (perfectCoreToFix e haN).ker :=
      (Nat.card_congr
        (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv).symm
    rw [← hcard]
    exact (oddCoreOf_odd_natCard K).of_dvd_nat (Subgroup.card_dvd_of_le hle)
  exact nonempty_quotEquiv_of_surjective_of_odd _ hsurj hker hO

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
