module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatSetup
public import CFSG.CGT.PushingUpLit.SolKNA.Residue

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AschbacherKnownGroup CFSG.Assembly.LowTwoRank
open CFSG.Assembly (InCatalog KProper pCoreOf)
open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome sylowImg STSetting)
open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)
open CFSG.ComponentClassification.StandardRecognition (ClassicalInvolutionTheoremModels)

@[expose] def QuaternionInspection : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R) →
        (CFSG.Blueprint.OddLieType G ∨ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic G .M12) →
        MTOutcome G K R

@[expose] def QuaternionInspectionSporadic : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R) →
        (CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 ∨
          CFSG.Blueprint.NativeSporadic.IsSporadic G .M12) →
        MTOutcome G K R

@[expose] def QuaternionInspectionLie : Prop :=
  ∀ (G : Type) [Group G] [Finite G], KProper InCatalog G → IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) →
    ∀ K : Subgroup G, TightlyEmbedded K →
      IsMaximalTwoLocal (Subgroup.normalizer (K : Set G)) →
      Subgroup.normalizer (K : Set G) ⊓
          Subgroup.centralizer (pCoreOf 2 (Subgroup.normalizer (K : Set G)) : Set G) ≤
        pCoreOf 2 (Subgroup.normalizer (K : Set G)) →
      ∀ R : Sylow 2 K, IsQuaternionTwoGroup (sylowImg R) →
        CFSG.Blueprint.OddLieType G → MTOutcome G K R

theorem quaternionInspection_of_split (hS : QuaternionInspectionSporadic)
    (hL : QuaternionInspectionLie) : QuaternionInspection := by
  intro G _ _ hKP hs hna K hK hM hF R hq h
  rcases h with h | h | h
  · exact hL G hKP hs hna K hK hM hF R hq h
  · exact hS G hKP hs hna K hK hM hF R hq (Or.inl h)
  · exact hS G hKP hs hna K hK hM hF R hq (Or.inr h)

theorem quaternion_of_cit_inspection (hCIT : ClassicalInvolutionTheoremModels)
    (hI : QuaternionInspection) : SolomonTimmesfeldMainQuaternion := by
  intro G _ _ hKP hs hna K hK hM hF R hq
  exact hI G hKP hs hna K hK hM hF R hq
    (oddLie_or_sporadic_of_quaternion hCIT ⟨hs, hna, hK, hM, hF⟩ R hq)

end CFSG.CGT.PushingUpLit.SolKNA
