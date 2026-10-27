module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaKPField
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.SymThreeSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSp
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphQuasi
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenTwelveSolvSigmaDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma

open CFSG.Open CFSG.AGLEmbedding Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe


theorem normal_of_subnormal_symThree_of_compParab (hGA : GriessAllModelsStatement) {X : Type}
    [Group X] [Finite X] {L J : Subgroup X} (hCP : CompParab L J)
    (hB2 : ¬ IsLieOf ParabCensus.IdxBTwo (↥L ⧸ center ↥L))
    {U : Subgroup (↥J ⧸ CFSG.pCore 2 ↥J)} (hUs : IsSubnormal U ⊤) (hU : Sym.IsSymThree U) :
    U.Normal := by
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  rcases isClassicalTwoOrG2_family_cases hCP.type with h | h | h | h | h | h | h
  · exact (ParabCensus.hasLeviCensus_idxA hGA hCP h).normal_of_subnormal_symThree hUs hU
  · exact (ParabCensus.hasLeviCensus_idxTwistedA hCP h).normal_of_subnormal_symThree hUs hU
  · rcases ParabCensus.isLieOf_idxB_cases h with h | h
    · exact absurd h hB2
    · exact (ParabCensus.hasLeviCensus_idxBBig hZ hCP h).normal_of_subnormal_symThree hUs hU
  · exact (ParabCensus.hasLeviCensus_idxD hZ hCP h).normal_of_subnormal_symThree hUs hU
  · exact (ParabCensus.hasLeviCensus_idxTwistedD hZ hCP h).normal_of_subnormal_symThree hUs hU
  · exact (ParabCensus.hasLeviCensus_idxG2 hGA hCP h).normal_of_subnormal_symThree hUs hU
  · exact ParabCensus.normal_of_subnormal_symThree_small hCP h hUs hU

theorem kFactParabolicSymThreeNormal_of_griess (hGA : GriessAllModelsStatement) :
    KFactParabolicSymThreeNormal := by
  intro A _ _ Y P hY hO hcl hP T hT hT3
  classical
  have hZ : OddCenterRest := oddCenterRest_of_griess hGA
  obtain ⟨hOT, hTs, hTiso⟩ := hatOf_of_mem_cZero hT hT3
  have hY' : CFSG.IsQuasisimple ↥Y :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Y).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥Y).mpr hY)
  refine ⟨?_, fun d hd he => lieField_eq_two_of_subnormal_symThree hY' hP hTs hTiso d hd he⟩
  rcases ParabCensus.parabolic_cases hY hO hcl hP with hPY | ⟨T₂, hT₂, hPeq⟩ | hCP
  ·
    subst P
    exfalso
    have hpc := ParabCensus.pCore_eq_bot_of_pCoreOf_eq_bot hO
    let e : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* ↥Y :=
      (QuotientGroup.quotientMulEquivOfEq hpc).trans QuotientGroup.quotientBot
    have hXs : IsSubnormal ((hatOf Y T).map e.toMonoidHom) ⊤ := by
      have h := hTs.map e.toMonoidHom
      rwa [Subgroup.map_top_of_surjective _ e.surjective] at h
    have hX : Sym.IsSymThree ((hatOf Y T).map e.toMonoidHom) := by
      obtain ⟨e3⟩ := hTiso
      exact ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).symm.trans e3⟩
    exact false_of_subnormal_symThree_of_isQuasisimple hY hX hXs
  ·
    subst P
    exfalso
    have hTP : T₂ ≤ Y ⊓ Subgroup.normalizer (T₂ : Set A) :=
      fun x hx => ⟨hT₂.1 hx, Subgroup.le_normalizer hx⟩
    obtain ⟨hoddO, -⟩ :=
      ParabCensus.odd_relIndex_pCoreOf_of_le_normalizer hT₂ hTP inf_le_left inf_le_right
    have hcard : ¬ 2 ∣ Nat.card
        (↥(Y ⊓ Subgroup.normalizer (T₂ : Set A)) ⧸
          CFSG.pCore 2 ↥(Y ⊓ Subgroup.normalizer (T₂ : Set A))) := by
      rw [← Subgroup.index_eq_card, ParabCensus.index_pCore_eq_relIndex_pCoreOf]
      exact hoddO
    have hdvd : Nat.card (hatOf (Y ⊓ Subgroup.normalizer (T₂ : Set A)) T) ∣
        Nat.card (↥(Y ⊓ Subgroup.normalizer (T₂ : Set A)) ⧸
          CFSG.pCore 2 ↥(Y ⊓ Subgroup.normalizer (T₂ : Set A))) :=
      Subgroup.card_subgroup_dvd_card _
    have h6 : Nat.card (hatOf (Y ⊓ Subgroup.normalizer (T₂ : Set A)) T) = 6 :=
      Sym.card_symThree hTiso
    exact hcard ((show 2 ∣ Nat.card (hatOf (Y ⊓ Subgroup.normalizer (T₂ : Set A)) T) by
      rw [h6]; norm_num).trans hdvd)
  · by_cases hB2 : IsLieOf ParabCensus.IdxBTwo (↥Y ⧸ center ↥Y)
    ·
      intro g hgP
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hgY : g ∈ Subgroup.normalizer (Y : Set A) := Subgroup.le_normalizer (hP.1 hgP)
      have hgN : g ∈ Subgroup.normalizer (P : Set A) := Subgroup.le_normalizer hgP
      have hhat := Sp.hatOf_conj_eq_of_spTwo hZ hY hO hB2 hP hT.le hTs hTiso hgY hgN
      have hT'P : T.map (MulAut.conj g).toMonoidHom ≤ P := by
        rintro _ ⟨t, ht, rfl⟩
        change g * t * g⁻¹ ∈ P
        exact P.mul_mem (P.mul_mem hgP (hT.le ht)) (P.inv_mem hgP)
      have hOT' : pCoreOf 2 P ≤ T.map (MulAut.conj g).toMonoidHom := by
        intro q hq
        have hgq : g⁻¹ * q * g ∈ pCoreOf 2 P := by
          have hmem : g⁻¹ ∈ Subgroup.normalizer (pCoreOf 2 P : Set A) :=
            Subgroup.inv_mem _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hgP)
          simpa using (Subgroup.mem_normalizer_iff.mp hmem q).mp hq
        refine Subgroup.mem_map.mpr ⟨g⁻¹ * q * g, hOT hgq, ?_⟩
        change g * (g⁻¹ * q * g) * g⁻¹ = q
        group
      have hT' : T.map (MulAut.conj g).toMonoidHom = T := by
        calc T.map (MulAut.conj g).toMonoidHom
            = Tower.preHatOf P (hatOf P (T.map (MulAut.conj g).toMonoidHom)) :=
              (preHatOf_hatOf_eq_of_le hT'P hOT').symm
          _ = Tower.preHatOf P (hatOf P T) := by rw [hhat]
          _ = T := preHatOf_hatOf_eq_of_le hT.le hOT
      exact hT'
    ·
      have hB2' : ¬ IsLieOf ParabCensus.IdxBTwo
          (↥(⊤ : Subgroup ↥Y) ⧸ center ↥(⊤ : Subgroup ↥Y)) :=
        ParabCensus.not_isLieOf_quotient_center_top (Q := ↥Y) hB2
      let e : ↥P ≃* ↥(P.subgroupOf Y) := (Subgroup.subgroupOfEquivOfLe hP.1).symm
      obtain ⟨ê⟩ : Nonempty (↥P ⧸ CFSG.pCore 2 ↥P ≃*
        ↥(P.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(P.subgroupOf Y)) :=
        ParabCensus.nonempty_quotient_pCore_of_mulEquiv e
      let U : Subgroup (↥(P.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(P.subgroupOf Y)) :=
        (hatOf P T).map ê.toMonoidHom
      have hUs : IsSubnormal U ⊤ := by
        have h := hTs.map ê.toMonoidHom
        rwa [Subgroup.map_top_of_surjective _ ê.surjective] at h
      have hU : Sym.IsSymThree U := by
        obtain ⟨e3⟩ := hTiso
        exact ⟨(Subgroup.equivMapOfInjective (hatOf P T) ê.toMonoidHom ê.injective).symm.trans e3⟩
      have hUn : U.Normal :=
        normal_of_subnormal_symThree_of_compParab hGA hCP hB2' hUs hU
      have hmap : U.map ê.symm.toMonoidHom = hatOf P T := by
        rw [show U = (hatOf P T).map ê.toMonoidHom from rfl, Subgroup.map_map,
          show ê.symm.toMonoidHom.comp ê.toMonoidHom = MonoidHom.id _ from
            MonoidHom.ext fun x => by simp,
          Subgroup.map_id]
      exact le_normalizer_of_normal_hatOf hT.le hOT
        (hmap ▸ hUn.map ê.symm.toMonoidHom ê.symm.surjective)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.TwelveSigma
