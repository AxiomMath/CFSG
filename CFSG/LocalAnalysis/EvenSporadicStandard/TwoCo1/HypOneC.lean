module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOnePerfect
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOnePerfectMat
public import CFSG.Sporadic.Co1Block.TwoCCent
public import Certificates.Certificate24512

public section

namespace CFSG.EvenSporadicStandard.TwoCo1.HypOne

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Block.Native
  CFSG.ComponentClassification.M12Cover

theorem fourClassesLarge_C :
    FourClassesLarge ↥(GA ⊓ Subgroup.centralizer {cG}) := by
  have hrepB := rep_brayElts (bidx := twoCBray) rep_iotaC (centCheck_parts twoC_cent_check).1
  have hBGK : ∀ g ∈ brayEltsG cG twoCD1 twoCBray, g ∈ GA ⊓ Subgroup.centralizer {cG} :=
    fun g hg => twoCE_le (Subgroup.subset_closure hg)
  obtain ⟨P, hPK, hP, hQ⟩ := exists_perfect_of_check hrepB hBGK Certificates.certificate24512
  have hQP : twoCQ ≤ P := by
    rw [twoCQ_eq, Subgroup.closure_le]
    rintro _ ⟨l, hl, rfl⟩
    have hl' : l < twoCQRows.length := by rw [twoCQRows_length]; exact hl
    refine hQ _ ?_ _ (qRep_twoC l hl')
    rw [List.getD_eq_getElem _ _ hl']
    exact List.getElem_mem hl'
  refine fourClassesLarge_of_perfect_le hPK hP fun x hx hxP _ => ?_
  have hxQ := twoC_selfCentralizing x hx fun q hq => (hxP q (hQP hq)).symm
  rw [pow_two]
  exact twoCQ_sq hxQ

end CFSG.EvenSporadicStandard.TwoCo1.HypOne
