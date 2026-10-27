module

public import CFSG.HardMathSupport.Solomon.Coordinator.B2LieEvenCases
public import CFSG.HardMathSupport.Solomon.Coordinator.B2SmallSimple
public import CFSG.HardMathSupport.Solomon.Coordinator.B2L34
import CFSG.RankThree.PartOne.SPOR.I613Even
import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic
import CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt

open Subgroup CFSG.Blueprint CFSG.Open
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible StatedClassicalModel StatedLieTag)

theorem card_eq_168_of_psl32 {G : Type} [Group G] (h : StatedClassicalModel G .PSL 3 2 1) :
    Nat.card G = 168 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  have h1 := CFSG.GH74.GLS.IVK.Proofs2.Lemma44bOrd.card_statedProj_statedSL_three_mul (F := K)
  rw [hK] at h1
  norm_num at h1
  rw [Nat.card_congr e.toEquiv]
  omega

theorem commutator_eq_bot_of_evenLieType
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnc : ∃ a b : S, a * b ≠ b * a)
    (hE : EvenLieType S) (β : MulAut S) (hβ : β ^ 2 = 1) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  by_cases hcore : β ≠ 1 → CFSG.oddCore ↥(centralizer ({β} : Set (MulAut S))) = ⊥
  · exact commutator_eq_bot_of_oddCore hnc β hcore
  push_neg at hcore
  obtain ⟨h1, hne⟩ := hcore
  have hord : orderOf β = 2 := orderOf_eq_prime hβ h1
  have hF := CFSG.ComponentClassification.CatLeaf.generalizedFitting_mulAut_eq_range hnc
  let e : S ≃* CFSG.generalizedFitting (MulAut S) :=
    (MonoidHom.ofInjective
      (CFSG.ComponentClassification.CatLeaf.mulAut_conj_injective_of_simple hnc)).trans
      (MulEquiv.subgroupCongr hF.symm)
  have : IsSimpleGroup (CFSG.generalizedFitting (MulAut S)) := e.symm.isSimpleGroup
  have hnonab : ∃ a b : CFSG.generalizedFitting (MulAut S), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnc
    refine ⟨e a, e b, fun h => hab (e.injective ?_)⟩
    rw [map_mul, map_mul, h]
  have hEF : EvenLieType (CFSG.generalizedFitting (MulAut S)) := by
    obtain ⟨t, n, f, hadm, hm⟩ := hE
    exact ⟨t, n, f, hadm, LieModel.of_mulEquiv e hm⟩
  rcases evenLie_unbalanced_cases hnonab hEF hord hne with hA | h321 | h322
  · obtain ⟨eA⟩ := hA
    exact commutator_layer_eq_bot_two le_rfl (e.trans eA) β hβ
  · exact commutator_eq_bot_of_card_168 hnc
      (card_eq_168_of_psl32 (StatedAPI.statedClassicalModel_of_mulEquiv e.symm h321)) β
  · exact commutator_eq_bot_of_psl34 hnc (StatedAPI.statedClassicalModel_of_mulEquiv e.symm h322)
      β hβ

theorem lieEvenCharTwoBp
    (idx : TauCeti.ValidLieTypeIndex) (hchar : idx.1.characteristic = 2) (S : Type) [Group S]
    [Finite S] (hS : IsSimpleGroup S) (hnc : ∃ a b : S, a * b ≠ b * a)
    (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie idx).Group)) (β : MulAut S) (hβ : β ^ 2 = 1) :
    ⁅GLAPLayer 2 (fixSubgroup β), GLAPPrimeCoreOf 2 (fixSubgroup β)⁆ = ⊥ := by
  have := hS
  exact commutator_eq_bot_of_evenLieType hnc
    (CFSG.RankThree.PartOne.SPOR.evenLieType_of_seitzBridge CFSG.RankThree.PartOne.CTP.seitzBridge
      ⟨idx.2, he⟩ hchar) β hβ

end CFSG.HardMathSupport.Solomon.Coordinator.B2FamAlt
