module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcG2Rank
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuousTriality
import CFSG.HardMathSupport.Timmesfeld.CrossChar.TrialityThreeRank

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley (graphFixedRootGroup)


variable {Ω : Type} [Group Ω] [Finite Ω] {S B : Subgroup Ω}

theorem false_of_badExcLie_trialityD4_three (hS : S.Normal) (hperf : ⁅S, S⁆ = S)
    (hB : IsElemAbelian 3 B) (hB4 : 3 ^ 4 ≤ Nat.card B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup 3 S) = 3) (hB81 : Nat.card B ≠ 3 ^ 4)
    {Q : TauCeti.PrimePower} (hQ2 : Q.p ≠ 2) (hQ3 : Q.p ≠ 3)
    (hv : (TauCeti.LieTypeIndex.trialityD4 Q).Valid)
    (e : PSimple 3 S ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 Q, hv⟩).Group) : False := by
  obtain ⟨K, _, _, σ, hK, hσ, ⟨Θ, hΘ⟩, ⟨ec⟩⟩ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.exists_catEquiv_trialityD4 Q hv
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
    have : Finite (Module.End K (RootModule TwistTag.D4.tag K)) := Module.finite_of_finite K
    infer_instance
  have hZ : Subgroup.center ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) = ⊥ :=
    CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective
  have hX : ∀ F : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
      IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 2 := fun F hF =>
    (CFSG.HardMathSupport.Timmesfeld.CrossChar.card_le_nine_of_graphFixedRootGroup_odd Q.prime_p
      hQ2 hQ3 Q.exponent_pos hK hσ F ⟨hF.1, hF.2⟩).trans (by norm_num)
  haveI : IsCyclic (K ≃+* K) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.fieldAut_isCyclic K
  have hrk := pRank_mulAut_le_of_cyclic hZ Nat.prime_three hX Θ hΘ
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) (MulAut.congr (e.trans ec).symm)]
    at hrk
  exact hB81 (le_antisymm
    (card_le_pow_succ_of_pRank_mulAut_le Nat.prime_three hS hperf hB hBC hrk) hB4)

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
