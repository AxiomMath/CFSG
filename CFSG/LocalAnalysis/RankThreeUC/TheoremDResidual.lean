module

public import CFSG.LocalAnalysis.RankThreeUC.TheoremDThompson
import CFSG.LocalAnalysis.RankThreeUC.TheoremDReductions
import CFSG.LocalAnalysis.RankThreeUC.TIModule

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD (StandingGen)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem omegaOneCenterIn_le_uCore (M T : Subgroup G) :
    CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ uCore M T := fun z hz =>
  mem_iSup_of_mem (1 : M) ⟨z, hz, by simp⟩

namespace IsWitnessGen

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem normalizer_le_of_characteristic_global (hS : StandingGen G) (hp : IsWitnessPrime p P)
    (hw : IsWitnessGen p P M) {T C : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hC1 : C ≠ ⊥) (hCT : C ≤ T) (hC : (C.subgroupOf T).Characteristic)
    (h2 : 2 ≤ CFSG.Open.pRank p (normalizer (C : Set G))) : normalizer (T : Set G) ≤ M :=
  hw.normalizer_le_of_two_le_pRank_normalizer hS hp hT hC1 hCT
    (CFSG.RankThree.PartOne.Sec15Final.normalizer_le_normalizer_of_characteristic hCT hC) h2

theorem normalizer_le_of_isTI (hw : IsWitnessGen p P M) {T V : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hV2 : IsPGroup 2 V)
    (hMV : M ≤ normalizer (V : Set G))
    (hZV : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ V)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI V) : normalizer (T : Set G) ≤ M := by
  have hT1 : T ≠ ⊥ := ne_bot_of_isSylowOf_two hw.maxLocal.1 hT
  have hZ1 : CFSG.RankThree.PartOne.omegaOneCenterIn T ≠ ⊥ :=
    CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_ne_bot hT.isPGroup hT1
  have hV1 : V ≠ ⊥ := fun h => hZ1 (le_bot_iff.mp (h ▸ hZV))
  intro n hn
  have hZn : (CFSG.RankThree.PartOne.omegaOneCenterIn T).map (MulAut.conj n).toMonoidHom =
      CFSG.RankThree.PartOne.omegaOneCenterIn T :=
    mem_normalizer_iff_map_conj_eq.mp (normalizer_le_normalizer_omegaOneCenterIn T hn)
  have hZ : CFSG.RankThree.PartOne.omegaOneCenterIn T ≤ V ⊓ V.map (MulAut.conj n).toMonoidHom :=
    le_inf hZV (hZn ▸ map_mono hZV)
  have hne : V ⊓ V.map (MulAut.conj n).toMonoidHom ≠ ⊥ := fun h => hZ1 (le_bot_iff.mp (h ▸ hZ))
  rw [← normalizer_eq_of_isMaxTwoLocal hw.maxLocal hV1 hV2 hMV]
  exact mem_normalizer_iff_map_conj_eq.mpr (map_conj_eq_of_isTI hTI hne)

theorem normalizer_le_of_isTI_uCore (hS : StandingGen G) (hw : IsWitnessGen p P M)
    {T : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hTI : CFSG.CGT.Timmesfeld75.IsTI (uCore M T)) : normalizer (T : Set G) ≤ M :=
  hw.normalizer_le_of_isTI hT
    (elementary_isPGroup 2 _ (uCore_le_and_isElemAbelian hS.charTwo hw.maxLocal.1 hT).2)
    (le_normalizer_uCore M T) (omegaOneCenterIn_le_uCore M T) hTI

end IsWitnessGen

namespace IsWitness

variable {p : ℕ} {P : Sylow p G} {M : Subgroup G}

theorem normalizer_le_of_characteristic_global (hS : Standing G) (hp : p ∈ rankThreeSigmaA G)
    (hw : IsWitness p P M) {T C : Subgroup G} (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hC1 : C ≠ ⊥) (hCT : C ≤ T) (hC : (C.subgroupOf T).Characteristic)
    (h2 : 2 ≤ CFSG.Open.pRank p (normalizer (C : Set G))) : normalizer (T : Set G) ≤ M :=
  IsWitnessGen.normalizer_le_of_characteristic_global hS.toGen
    (IsWitnessPrime.of_mem_sigmaA hS hp P) hw.toGen hT hC1 hCT hC h2

end IsWitness

@[expose] def AGL81ResidualGen (G : Type) [Group G] [Finite G]
    (W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop) : Prop :=
  ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M → ∀ T : Subgroup G,
    CFSG.ABGLocalTools.IsSylowOf 2 T M →
      ¬ thompsonSubgroup T ≤ centralizer (uCore M T : Set G) →
      ¬ CFSG.CGT.Timmesfeld75.IsTI (uCore M T) →
      (∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
        CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1) →
      normalizer (T : Set G) ≤ M

theorem agl81TheoremDGen_of_residualGen (hS : StandingGen G)
    {W : ∀ p : ℕ, Sylow p G → Subgroup G → Prop}
    (hW : ∀ (p : ℕ) (P : Sylow p G) (M : Subgroup G), W p P M →
      IsWitnessPrime p P ∧ IsWitnessGen p P M)
    (hR : AGL81ResidualGen G W) : AGL81TheoremDGen G W := by
  intro p P M hw T hT
  obtain ⟨hp, hw'⟩ := hW p P M hw
  by_cases hJ : thompsonSubgroup T ≤ centralizer (uCore M T : Set G)
  · exact hw'.normalizer_sylow_two_le_of_thompson hS hp hT (le_normalizer_uCore M T)
      (omegaOneCenterIn_le_uCore M T) hJ
  by_cases hTI : CFSG.CGT.Timmesfeld75.IsTI (uCore M T)
  · exact hw'.normalizer_le_of_isTI_uCore hS hT hTI
  by_cases hC : ∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧
      2 ≤ CFSG.Open.pRank p (normalizer (C : Set G))
  · obtain ⟨C, hC1, hCT, hCc, h2⟩ := hC
    exact hw'.normalizer_le_of_characteristic_global hS hp hT hC1 hCT hCc h2
  · refine hR p P M hw T hT hJ hTI fun C hC1 hCT hCc => ?_
    by_contra h
    exact hC ⟨C, hC1, hCT, hCc, by omega⟩

end CFSG.LocalAnalysis.RankThreeUC
