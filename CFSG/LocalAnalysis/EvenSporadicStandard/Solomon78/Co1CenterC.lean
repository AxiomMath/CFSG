module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1CenterFilter
public import CFSG.Sporadic.Co1Block.TwoCCent
public import Certificates.Certificate25171
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.CenterAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.HypOneSylow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1.TwoBNative

theorem centerInvAt_cC :
    CenterInvAt cC := by
  have key : ∀ a : GA, (a : GL24) = cG → CenterInvAt a := by
    intro a ha z _ hzc
    have hza : (z : GL24) * cG = cG * z := by
      have := commute_coe_of_central hzc a.2 rfl
      rwa [ha] at this
    have hzK : (z : GL24) ∈ GA ⊓ Subgroup.centralizer {cG} :=
      Subgroup.mem_inf.2 ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2 hza⟩
    have hcomm : ∀ g ∈ GA ⊓ Subgroup.centralizer {cG}, (z : GL24) * g = g * z := by
      intro g hg
      obtain ⟨hgA, hgc⟩ := Subgroup.mem_inf.1 hg
      refine commute_coe_of_central hzc hgA ?_
      rw [ha]
      exact Subgroup.mem_centralizer_singleton_iff.1 hgc
    have hzQ : (z : GL24) ∈ twoCQ :=
      twoC_selfCentralizing _ hzK fun q hq => hcomm q (twoCQ_le hq)
    obtain ⟨i, hi, hp⟩ := exists_point_of_mem_Q qRep_twoC twoC_q_check hzQ
    have hrepB := rep_brayElts (bidx := twoCBray) rep_iotaC (centCheck_parts twoC_cent_check).1
    have hv := TwoCo1.HypOne.validRows_of_gtOK (qCheck_parts twoC_q_check).1 i hi
    have hf : centerFilterOf iotaCRows
        (Native.brayElts (Native.brayRows iotaCRows twoCD1) twoCBray)
        (gtBFS twoCQRows.toArray 2048).pts = true := Certificates.certificate25171
    rcases eq_one_or_of_centerFilter rep_iotaC hrepB hf hi hv hp
        (fun g hg => hcomm g (twoCE_le (Subgroup.subset_closure hg))) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext (h.trans ha.symm))
  exact key cC coe_cC

end CFSG.EvenSporadicStandard.Solomon78
