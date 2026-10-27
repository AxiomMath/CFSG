module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.InvolutionClass
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerPermutable
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutionsAction

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape

open CFSG.Open CFSG.QuasithinUnique CFSG.LinearGroups.UnitaryThreeOverNine

abbrev SU33 (K : Type) [Field K] := CFSG.Assembly.LowTwoRank.StatedSU 3 3 K

theorem exists_equiv_statedSU_of_model {N : Type} [Group N]
    (hmod : StatedClassicalModel N .PSU 3 3 1) :
    ∃ (K : Type) (_ : Field K), Nat.card K = 9 ∧ Nonempty (N ≃* ↥(SU33 K)) := by
  obtain ⟨-, K, hKfield, hKfin, hcard, ⟨e⟩⟩ := hmod
  have hK9 : Nat.card K = 9 := by simpa using hcard
  have hbot := statedScalars_subgroupOf_statedSU_eq_bot hK9
  exact ⟨K, hKfield, hK9, ⟨e.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans
    QuotientGroup.quotientBot)⟩⟩

theorem kFactU33SylowPermute : KFactU33SylowPermute := by
  intro N _ _ hs hnc hmod Y hY h2 S hS
  obtain ⟨K, hKfield, hK9, ⟨e⟩⟩ := exists_equiv_statedSU_of_model hmod
  have h := unitaryFieldData_of_card hK9
  refine sylow_permute_of_involution_class hs hnc ?_ ?_ ?_ Y hY h2 S hS
  · rw [Nat.card_congr e.toEquiv]
    exact card_statedSU hK9
  · have h1 : Nat.card {b : N // orderOf b = 2} =
        Nat.card {g : SU33 K // orderOf g = 2} :=
      Nat.card_congr (e.toEquiv.subtypeEquiv (fun b => by
        show orderOf b = 2 ↔ orderOf (e b) = 2
        rw [MulEquiv.orderOf_eq]))
    rw [h1, ← Nat.card_congr (tauLineEquiv h hK9)]
    exact card_nonisoLine hK9
  · intro a b ha hb
    have ha' : orderOf (e a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
    have hb' : orderOf (e b) = 2 := by rw [MulEquiv.orderOf_eq]; exact hb
    obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_of_orderOf_eq_two hK9 ha' hb')
    refine isConj_iff.mpr ⟨e.symm c, e.injective ?_⟩
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc

theorem kFactRankTwoSylowPermute : KFactRankTwoSylowPermute :=
  kFactRankTwoSylowPermute_of_u33 kFactU33SylowPermute

theorem d2L34BetaLayerPermutable_of_sylow_aut (hSyl : D2L34BetaLayerSylow)
    (hAut : D2L34BetaLayerAutImage) : D2L34BetaLayerPermutable :=
  d2L34BetaLayerPermutable_of kFactRankTwoSylowPermute hSyl hAut

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
