module

public import CFSG.LargeExtraspecial.S8ThreeE
public import CFSG.LargeExtraspecial.S8Dim4
public import CFSG.LargeExtraspecial.S8DimB
public import CFSG.LargeExtraspecial.S8Ten

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] CFSG.BenderSuzuki.PFAppendixIII.instFactNatPrimeTwo

namespace CFSG.LargeExtraspecial.S8

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2

universe u

section Lin

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem not_isTypeA_of_minus_two (hq : q.polarBilin.Nondegenerate)
    (hmin : IsMinusType q ⊥ 2) {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0)
    (hpp₁ : polar q p p₁ = 1) {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ pointRadical q p) (hx1 : x ≠ 1) :
    ¬ IsTypeA q x 2 := by
  intro hxa
  obtain ⟨u', hu'K, hu'0, hxu⟩ := exists_eichler_of_mem_pointRadical hq hp0 hp hpp₁ hx hx1
  obtain ⟨-, hpu', hp₁u'⟩ := mem_perp_sup_span_pair.mp hu'K
  have hqu' : q u' = 0 := by
    rcases zmod2_eq_zero_or_eq_one (q u') with h | h
    · exact h
    · rw [hxu] at hxa
      exact absurd hxa (not_isTypeA_eichler hq hp0 hp hpu' h)
  have hli : LinearIndependent (ZMod 2) ![p, u'] := by
    refine (LinearIndependent.pair_iff' hp0).mpr fun a ha => ?_
    have h0 : polar q p₁ (a • p) = 0 := by rw [ha, hp₁u']
    rw [polar_smul_right, polar_comm, hpp₁, smul_eq_mul, mul_one] at h0
    rw [h0, zero_smul] at ha
    exact hu'0 ha.symm
  have hT : ∀ v ∈ Submodule.span (ZMod 2) {p, u'}, q v = 0 := by
    intro v hv
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
    have h0 : q (a • p + b • u') = q (a • p) + q (b • u') + polar q (a • p) (b • u') := by
      rw [polar]; abel
    rw [h0, QuadraticMap.map_smul, QuadraticMap.map_smul, hp, hqu', polar_smul_left,
      polar_smul_right, hpu']
    simp
  have h2 := hmin _ (by rw [perp_bot]; exact le_top) hT
  rw [finrank_span_pair hli] at h2
  omega

end Lin

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable {H : Hyp4 S g} {C : Cons311 S g} {t : S.O} {ht : t ∈ S.Lbar g} {ht1 : t ≠ 1}
  {hVQ : ¬ V S g t ≤ S.Qa g}

theorem finrank_commSpace_add_one_le_of_mem_Abar (D : Std H C ht ht1 hVQ) {α : S.O}
    (hαA : α ∈ S.Lbar g ⊓ Nbar S g t) :
    finrank (ZMod 2) (commSpace (α : S.Qt ≃ₗ[ZMod 2] S.Qt)) + 1 ≤
      2 * finrank (ZMod 2) (Vt S g t) := by
  have haQ := H.conj_mem
  have hle : (Wt S g t).map ((α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤
      S.clSub (S.QG ⊓ S.Qa g) ⊓ Vt S g t := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨apply_sub_mem_clSub_of_mem_Wt C (cl_a_mem_Vt ht) haQ hw hαA.1, D.hN α hαA.2 w hw⟩
  have e1 := finrank_map_add_finrank_inf_ker
    ((α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) (Wt S g t)
  have e2 := LinearMap.finrank_range_add_finrank_ker
    ((α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)
  have i1 := Submodule.finrank_mono hle
  have i2 := Submodule.finrank_mono (inf_le_right : Wt S g t ⊓
    LinearMap.ker ((α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) ≤
      LinearMap.ker ((α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1))
  have e3 := finrank_clSub_inf_Vt H C ht ht1 hVQ
  have e4 := finrank_Wt (S := S) (g := g) (t := t)
  have e5 := finrank_perp S.q_nondegenerate (Vt S g t)
  have e6 : Wt S g t = S2.perp S.q (Vt S g t) := rfl
  rw [← e6] at e5
  change finrank (ZMod 2) (LinearMap.range ((α : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) + 1 ≤ _
  omega

theorem finrank_commSpace_ge_of_minus_two (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) {β : S.O} (hβL : β ∈ S.Lbar g) (hβN : β ∉ Nbar S g t) :
    8 + finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) ≤
      2 * finrank (ZMod 2) (commSpace (β : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
  obtain ⟨ρ, hρ, hD⟩ := timmesfeld_6_1_two hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
  obtain ⟨r, hr⟩ : ∃ r : Rbar S g t, r = ⟨β, Lbar_le_Rbar ht hβL⟩ := ⟨_, rfl⟩
  have heΩ : resV H.conj_mem t r ∈ omegaGroup D.Q D.hQ := by
    rw [← D.hX, ← range_resV H.conj_mem t]; exact ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : omegaGroup D.Q D.hQ,
      (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) = resV H.conj_mem t r := ⟨⟨_, heΩ⟩, rfl⟩
  have h1 := finrank_commWV_eq D hρ r e he
  have hx : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ pointRadical D.Q (aV ht) := by
    rw [he, hr]; exact resV_mem_pointRadical D hβL
  have hx1 : (e : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ≠ 1 := by
    rw [he, hr]
    exact fun h => hβN ((resV_eq_one_iff H.conj_mem _).mp h)
  have hmin' : IsMinusType D.Q ⊥ 2 := fun T _ hT => by
    have := hmin T hT
    rwa [hm2] at this
  have hxa := not_isTypeA_of_minus_two D.hQ hmin' (aV_ne_zero H ht) D.hQa D.polar_aV_bV hx hx1
  have h2 := finrank_eq_two_mul_finrank_commSpace ρ D.hm D.hdim D.hQa D.Q_bV D.polar_aV_bV hD e
    hx hx1 hxa
  have hrβ : (r : S.O) = β := by rw [hr]
  have hQW := finrank_commQW_eq H C ht ht1 hVQ r
  have hrN : (r : S.O) ∉ Nbar S g t := by rw [hrβ]; exact hβN
  have hrL : (r : S.O) ∈ S.Lbar g := by rw [hrβ]; exact hβL
  have hres2 : finrank (ZMod 2) (commSpace (resV H.conj_mem t r)) = 2 := by
    have := finrank_commSpace_resV_eq_two D hrL hrN
    rwa [show (⟨(r : S.O), Lbar_le_Rbar ht hrL⟩ : Rbar S g t) = r from Subtype.ext rfl] at this
  rw [hres2] at hQW
  have hV2 :
      finrank (ZMod 2) ((Vt S g t).map (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) =
        2 := by
    have e2 : (Vt S g t).map (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1) =
        (commSpace (resV H.conj_mem t r)).map (Vt S g t).subtype := by
      ext y
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨resV H.conj_mem t r ⟨v, hv⟩ - ⟨v, hv⟩, sub_mem_commSpace _ _, ?_⟩
        rw [Submodule.subtype_apply, Submodule.coe_sub, coe_resV_apply]
        rfl
      · rintro ⟨_, hz, rfl⟩
        obtain ⟨z, rfl⟩ := mem_commSpace.mp hz
        refine ⟨z, z.2, ?_⟩
        rw [Submodule.subtype_apply, Submodule.coe_sub, coe_resV_apply]
        rfl
    rw [e2, LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (Submodule.injective_subtype _) _).symm]
    exact hres2
  have hrt : (r : S.O) * t = t * (r : S.O) := commute_of_mem_Rbar H.conj_mem r.2
  have hrC : (r : S.O) ∈ CMt S t := mem_CMt.mpr ⟨Rbar_le_Mbar r.2, hrt⟩
  have hfilt := finrank_commSpace_ge (S := S) (g := g) (t := t) (τ := (r : S.O))
    (fun v hv => apply_mem_Vt_of_mem_CMt H.conj_mem hrC hv)
    (fun w hw => apply_mem_Wt_of_commute H C ht ht1 hVQ hrt hw) (Vt_le_Wt H ht1)
  change finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) S.Qt).map
      (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)).map (Wt S g t).mkQ) +
    finrank (ZMod 2) (commWV S g t (r : S.O)) +
    finrank (ZMod 2) ((Vt S g t).map (((r : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt).toLinearMap - 1)) ≤
      _ at hfilt
  rw [hQW, hV2, h1, hrβ] at hfilt
  omega

theorem eight_le_finrank_WV (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) :
    8 ≤ finrank (ZMod 2) ((Wt S g t).map (Vt S g t).mkQ) := by
  have hpos := D.pos_finrank_WV hA7
  have hdvd := timmesfeld_6_1_two_dvd_minus hCE H hNo C ht ht1 hVQ hΩ D.hh D.hb D.hX D.hE
    D.hQa D.polar_aV_bV D.hm D.hdim hmin
  have h4 := finrank_WV_ne_four hCE hNo hΩ D (Or.inr hmin)
  rw [hm2] at hdvd
  obtain ⟨c, hc⟩ := hdvd
  norm_num at hc
  omega

theorem mem_Nbar_of_conj_mem_Lbar_A5 (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {α x : S.O}
    (hαA : α ∈ S.Lbar g ⊓ Nbar S g t) (hxL : x * α * x⁻¹ ∈ S.Lbar g) :
    x * α * x⁻¹ ∈ Nbar S g t := by
  by_contra hN
  have h1 := finrank_commSpace_add_one_le_of_mem_Abar D hαA
  have h2 := finrank_commSpace_ge_of_minus_two hCE hNo hΩ D hm2 hmin hxL hN
  have h3 := eight_le_finrank_WV hCE hNo hΩ D hm2 hmin hA7
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, finrank_commSpace_conj'] at h2
  rw [D.hdim, hm2] at h1
  omega

theorem conj_eq_of_conj_mem_Lbar_A5 (hCE : CentralExtInput.{u}) (hNo : NoA2 S g)
    (hΩ : OmegaCase H C ht ht1 hVQ) (D : Std H C ht ht1 hVQ) (hm2 : D.m = 2)
    (hmin : D.IsMinus) (hA7 : S.Lbar g ⊓ Nbar S g t ≠ zpowers t) {x : S.O}
    (hxM : x ∈ S.Mbar) (hxt : x * t * x⁻¹ ∈ S.Lbar g) : x * t * x⁻¹ = t := by
  have haQ := H.conj_mem
  obtain ⟨n, hnM, hnL, hn⟩ := S5.exists_mem_normalizer_conj H C hxM
    (fun l hl => Lbar_comm S haQ ht hl) (fun l hl => Lbar_comm S haQ hxt hl)
  rw [hn]
  refine conj_eq_of_normalizer_Abar hNo D hnM hnL ?_
  rw [mem_normalizer_iff]
  intro α
  constructor
  · intro hα
    have hL := (mem_normalizer_iff.mp hnL α).mp hα.1
    exact ⟨hL, mem_Nbar_of_conj_mem_Lbar_A5 hCE hNo hΩ D hm2 hmin hA7 hα hL⟩
  · intro hα
    have hnL' := inv_mem hnL
    have hL : n⁻¹ * (n * α * n⁻¹) * n⁻¹⁻¹ ∈ S.Lbar g := (mem_normalizer_iff.mp hnL' _).mp hα.1
    have hN := mem_Nbar_of_conj_mem_Lbar_A5 hCE hNo hΩ D hm2 hmin hA7 hα hL
    rw [show n⁻¹ * (n * α * n⁻¹) * n⁻¹⁻¹ = α by group] at hL hN
    exact ⟨hL, hN⟩

end CFSG.LargeExtraspecial.S8
