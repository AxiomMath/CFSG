module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Core5
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Conj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Lift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FGE16Pull
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem fg_exists_sylow_normalE16 {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : IsOm6P K) (hz : centerIn K = ⊥) {B : Subgroup G} (hB : IsElemAb2 B 4) (hBK : B ≤ K)
    (h5 : 5 ∣ Nat.card ↥(K ⊓ normalizer (B : Set G))) :
    ∃ P : Subgroup G, IsSylow2Of P K ∧ IsNormalE16In P B := by
  classical
  obtain ⟨V, _, _, _, Q, hQ, e, hdim, hsgn⟩ := ff_exists_model_six_plus hK
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  have hπ := ff_piOrth_not_mem_omegaGroup_six_plus hQ hdim hsgn
  have hzc : Subgroup.center ↥K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).mp hz
  have hφ : OddCentralCover (ff6mPhi e) := ff6m_phi_cover e (ff6p_odd_center hK)
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (p := 2) (n := 4) hB.2
  set U : Subgroup ↥(omegaProj hQ) := ffImg (ff6mPhi e) B with hUdef
  have hU : IsElemAb2 U 4 := (ff_cover_elemAb2_iff hφ hBK hB2 4).mp hB
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hxK : (x : G) ∈ K := (Subgroup.mem_inf.mp x.2).1
  have hxN : (x : G) ∈ normalizer (B : Set G) := (Subgroup.mem_inf.mp x.2).2
  have hxo : orderOf (x : G) = 5 := by rw [Subgroup.orderOf_coe]; exact hx
  have hl5 : orderOf (⟨x, hxK⟩ : ↥K) = 5 := by
    rw [← Subgroup.orderOf_coe]
    exact hxo
  have hw5 : orderOf (ff6mPhi e ⟨x, hxK⟩) = 5 := by
    rw [orderOf_injective _ (ff6p_phi_injective hQ hzc e), hl5]
  have hwN : ff6mPhi e ⟨x, hxK⟩ ∈ normalizer (U : Set ↥(omegaProj hQ)) :=
    (ff_cover_mem_normalizer_iff hφ hBK hB2 ⟨x, hxK⟩).mp hxN
  obtain ⟨f, hfΩ, hfw, hf5, hf1⟩ := fg_exists_lift_five hQ hπ hw5
  have hB'E : IsElemAb2 (ffLift hQ U) 4 := fg_elemAb2_ffLift hQ hπ hU
  have hfn : ∀ g, g ∈ ffLift hQ U ↔ f * g * f⁻¹ ∈ ffLift hQ U := fun g =>
    fg_mem_ffLift_conj_iff hQ hfΩ (by rw [hfw]; exact hwN) g
  have hB'card : Nat.card ↥(ffLift hQ U) = 16 := by
    rw [hB'E.2]
    norm_num
  haveI : Finite ↥(ffLift hQ U) := Nat.finite_of_card_ne_zero (by rw [hB'card]; norm_num)
  letI : Fintype ↥(ffLift hQ U) := Fintype.ofFinite _
  obtain ⟨b, a, ha, horth, hnone, hsome, hdiag⟩ :=
    fg_frame_E16 (ffLift hQ U) hB'E hdim f hfn hf5 hf1 hQ hsgn
  obtain ⟨γ, fr, hγ⟩ := fg_conj_E16 hQ hdim (ffLift hQ U) (ffLift_le_omega hQ U) hB'card b ha
    horth hnone hsome hdiag
  have hUeq : U = (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ)).toMonoidHom :=
    calc U = ffStar hQ (ffLift hQ U) := (ffStar_ffLift hQ U).symm
      _ = ffStar hQ ((ffB0p fr).map (simAct Q γ).toMonoidHom) := by rw [← hγ]
      _ = (ffB1p hQ fr).map (ffSimOmegaAct hQ h2 (QuotientGroup.mk γ)).toMonoidHom :=
        fg_ffStar_map_simAct hQ h2 γ (ffB0p_le_omega hQ fr)
  have himg : ffImg (ff6mPhi (ffAdapt h2 e (QuotientGroup.mk γ))) B = ffB1p hQ fr :=
    ffImg_ffAdapt h2 e (QuotientGroup.mk γ) B (ffB1p hQ fr) hUeq
  exact fg_pull_sylow_E16 (ff6p_phi_injective hQ hzc (ffAdapt h2 e (QuotientGroup.mk γ)))
    (ff6mPhi_surjective (ffAdapt h2 e (QuotientGroup.mk γ))) (ffP1p_sylow hQ hdim hsgn fr)
    (ffB1p_normalE16 hQ hπ fr) hBK himg

end CFSG.OddStandard.SmallF3.Omega
