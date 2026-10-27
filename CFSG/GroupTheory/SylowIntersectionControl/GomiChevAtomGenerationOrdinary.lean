module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomGenerationSimple
public import CFSG.Milestones.ASVolI.I2
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BNConj

public section

namespace CFSG.GroupTheory

theorem gomiAtomGenerationTop_of_lieModel
    {K : Type} [Group K] [Finite K] {t : CFSG.Open.StatedLieTag} {n f : ℕ} (ht : t ≠ .Tits)
    (hK : CFSG.Blueprint.LieModel K t n 2 f) : GomiAtomGenerationTop K := by
  intro U Q hU hQ
  obtain ⟨B, N, hBN⟩ := CFSG.ASVolI.ChIJK.lieModel_has_splitBNPair Nat.prime_two ht hK
  have hUi : ¬ 2 ∣ U.index := by
    simpa [Subgroup.relIndex_top_right] using (CFSG.ABGLocalTools.isSylowOf_iff.1 hU).2.2
  obtain ⟨B', N', hBN', -, hUB, -⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22k108bn_exists_conj_split hBN hU.isPGroup hUi
  have : (CFSG.GH74.BNPair.cartan B' N').Normal := hBN'.normal_inter
  obtain ⟨S, hS⟩ := CFSG.ASVolI.ChIJK.burnsideI2BN_exists_isBNPair
    (CFSG.ASVolI.ChIJK.burnsideI2BN_toPre hBN')
  exact le_normalizer_sup_sSup_isGomiAtom_of_isBNPair hS hUB (hUB ▸ hQ)

end CFSG.GroupTheory
