module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinFinalRigid
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelA
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelD
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotGraphSpinModelF4

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Universal.Spin (quadPlus)
open CFSG.EvenSmallLie
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)

section Partner

variable {K : Type} [Field K] {G M : Type*} [Group G] [Group M]

theorem exists_partner_of_mem_closure (φA φD : StatedSp 3 K →* G) (FA FD : StatedSp 3 K →* M)
    (hgen : ∀ s ∈ sp4Gens K, ∃ t, φD t = φA s ∧ FA s = FD t) {s : StatedSp 3 K}
    (hs : s ∈ closure (sp4Gens K)) : ∃ t, φD t = φA s ∧ FA s = FD t := by
  induction hs using Subgroup.closure_induction with
  | mem s hs => exact hgen s hs
  | one => exact ⟨1, by rw [map_one, map_one], by rw [map_one, map_one]⟩
  | mul a b _ _ ha hb =>
    obtain ⟨t, ht1, ht2⟩ := ha
    obtain ⟨u, hu1, hu2⟩ := hb
    exact ⟨t * u, by rw [map_mul, map_mul, ht1, hu1], by rw [map_mul, map_mul, ht2, hu2]⟩
  | inv a _ ha =>
    obtain ⟨t, ht1, ht2⟩ := ha
    exact ⟨t⁻¹, by rw [map_inv, map_inv, ht1], by rw [map_inv, map_inv, ht2]⟩

end Partner

theorem exists_ringEquiv_sq_eq {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ ε : K ≃+* K, ∀ c : K, ε c ^ 2 = c :=
  ⟨(frobeniusEquiv K 2).symm, fun c => frobeniusEquiv_symm_pow_p K 2 c⟩

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)

theorem exists_sp4Partner_of_mem_sp4Gens (ε : K ≃+* K) (hε : ∀ c : K, ε c ^ 2 = c)
    {s : StatedSp 3 K} (hs : s ∈ sp4Gens K) :
    ∃ t : StatedSp 3 K,
      spinToE6Sc K (spinIota hK hf t) = graphParamHom K (RingEquiv.refl K) (sp6ToSL6 s) ∧
      (((c3LeviEquiv K s : C3Levi K) : adjointGroup .F4 K),
          graphAutF4 K (c3LeviEquiv K s : C3Levi K)) =
        (graphAutF4 K (c3LeviEquiv K (statedSpCongr ε 3 t) : C3Levi K),
          ((c3LeviEquiv K t : C3Levi K) : adjointGroup .F4 K)) := by
  obtain ⟨c, rfl | rfl | rfl | rfl⟩ := hs
  · refine ⟨Sp.x 3 K (Pi.single 2 1) (c ^ 2), ?_, ?_⟩
    · rw [spinToE6Sc_spinIota_x_single_two_sq, graphParamHom_sp6ToSL6_x_single_one]
    · rw [statedSpCongr_x, map_pow, hε, c3LeviEquiv_x_single_one, c3LeviEquiv_x_single_two,
        c3LeviEquiv_x_single_two]
      exact Prod.ext (graphAutF4_pinnedX_single_one c).symm (graphAutF4_pinnedX_single_two c)
  · refine ⟨Sp.x 3 K (-Pi.single 2 1) (c ^ 2), ?_, ?_⟩
    · rw [spinToE6Sc_spinIota_x_neg_single_two_sq, graphParamHom_sp6ToSL6_x_neg_single_one]
    · rw [statedSpCongr_x, map_pow, hε, c3LeviEquiv_x_neg_single_one,
        c3LeviEquiv_x_neg_single_two, c3LeviEquiv_x_neg_single_two]
      exact Prod.ext (graphAutF4_pinnedX_neg_single_one c).symm
        (graphAutF4_pinnedX_neg_single_two c)
  · refine ⟨Sp.x 3 K (Pi.single 1 1) c, ?_, ?_⟩
    · rw [spinToE6Sc_spinIota_x_single_one, graphParamHom_sp6ToSL6_x_single_two]
    · rw [statedSpCongr_x, c3LeviEquiv_x_single_two, c3LeviEquiv_x_single_one,
        c3LeviEquiv_x_single_one]
      exact Prod.ext ((graphAutF4_pinnedX_single_two (ε c)).trans (by rw [hε])).symm
        (graphAutF4_pinnedX_single_one c)
  · refine ⟨Sp.x 3 K (-Pi.single 1 1) c, ?_, ?_⟩
    · rw [spinToE6Sc_spinIota_x_neg_single_one, graphParamHom_sp6ToSL6_x_neg_single_two]
    · rw [statedSpCongr_x, c3LeviEquiv_x_neg_single_two, c3LeviEquiv_x_neg_single_one,
        c3LeviEquiv_x_neg_single_one]
      exact Prod.ext ((graphAutF4_pinnedX_neg_single_two (ε c)).trans (by rw [hε])).symm
        (graphAutF4_pinnedX_neg_single_one c)

theorem exists_sp4Partner (ε : K ≃+* K) (hε : ∀ c : K, ε c ^ 2 = c) {s : StatedSp 3 K}
    (hs : s ∈ closure (sp4Gens K)) :
    ∃ t : StatedSp 3 K,
      spinToE6Sc K (spinIota hK hf t) = graphParamHom K (RingEquiv.refl K) (sp6ToSL6 s) ∧
      (((c3LeviEquiv K s : C3Levi K) : adjointGroup .F4 K),
          graphAutF4 K (c3LeviEquiv K s : C3Levi K)) =
        (graphAutF4 K (c3LeviEquiv K (statedSpCongr ε 3 t) : C3Levi K),
          ((c3LeviEquiv K t : C3Levi K) : adjointGroup .F4 K)) :=
  exists_partner_of_mem_closure ((graphParamHom K (RingEquiv.refl K)).comp sp6ToSL6)
    ((spinToE6Sc K).comp (spinIota hK hf))
    (((C3Levi K).subtype.comp (c3LeviEquiv K).toMonoidHom).prod
      ((graphAutF4 K).toMonoidHom.comp ((C3Levi K).subtype.comp (c3LeviEquiv K).toMonoidHom)))
    (((graphAutF4 K).toMonoidHom.comp ((C3Levi K).subtype.comp
      ((c3LeviEquiv K).toMonoidHom.comp (statedSpCongr ε 3).toMonoidHom))).prod
      ((C3Levi K).subtype.comp (c3LeviEquiv K).toMonoidHom))
    (fun _ hs => exists_sp4Partner_of_mem_sp4Gens hK hf ε hε hs) hs

end Model

section Holds

theorem e6RowSp4ModelInput_holds : E6RowSp4ModelInput := by
  intro K _ _ _ _ f hK hf
  obtain ⟨ε, hε⟩ := exists_ringEquiv_sq_eq (K := K)
  have hinj : Function.Injective fun s : StatedSp 3 K => spinToE6Sc K (spinIota hK hf s) :=
    spinToE6Sc_injective.comp (spinIota_injective hK hf)
  refine ⟨⟨ε, fun x sA sD hx _ hA hD => ?_⟩, ⟨RingEquiv.refl K, fun x sA sD hx _ hA hD => ?_⟩⟩
  · obtain ⟨t, ht, hpair⟩ := exists_sp4Partner hK hf ε hε
      (mem_closure_sp4Gens_of_mem_A3 (hA.symm ▸ hx))
    have htD : t = sD := hinj (ht.trans (hA.trans hD.symm))
    subst htD
    exact (Prod.ext_iff.1 hpair).1
  · obtain ⟨t, ht, hpair⟩ := exists_sp4Partner hK hf ε hε
      (mem_closure_sp4Gens_of_mem_A3 (hA.symm ▸ hx))
    have htD : t = sD := hinj (ht.trans (hA.trans hD.symm))
    subst htD
    rw [statedSpCongr_refl_apply]
    exact (Prod.ext_iff.1 hpair).2

end Holds

section Corollaries

theorem e6GraphRowSpinNormInput_holds : E6GraphRowSpinNormInput :=
  e6GraphRowSpinNormInput_of_sp4Model e6RowSp4ModelInput_holds

end Corollaries

end CFSG.SeitzReduction.F4Pilot
