module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeKFact
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeSetup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeAltTen
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.SevenThreeSmall
import CFSG.RankThree.CentralLift.ClassicalCenterTrivial

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

theorem sevenThreeInput_of_inputs
    (hK34 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K34odd)
    (h711 : CFSG.LocalAnalysis.RankThreeUC.AGL81C.SevenOneOne)
    (hA9 : KFactA9NotInvolvedK34Classical) : SevenThreeInput := by
  intro X _ _ hKX L hLcomp hFstar hO hprankL T Hs hTsyl hTHs hHsQuot _
  obtain ⟨hQ, hCat, hOdd, hrankL⟩ :=
    SevenThree.k34odd_hyps_of_isComponent hKX hLcomp hO hprankL
  obtain ⟨I, hI, f, hf, hfker⟩ :=
    SevenThree.exists_perfect_onto_a9_le_component h711 hKX hLcomp hFstar hHsQuot
  rcases hK34 ↥L hQ hCat hOdd hrankL with hON | ⟨h3Z, hcase⟩
  · exact (SevenThree.false_of_threeCover_onan hON I f hf).elim
  · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hZ : Subgroup.center ↥L = ⊥ :=
      CFSG.RankThree.CentralLift.eq_bot_of_isPGroup_of_not_dvd
        (SevenThree.isPGroup_center_of_isComponent (p := 3) hLcomp hO) h3Z
    let π : ↥L →* (↥L ⧸ Subgroup.center ↥L) := QuotientGroup.mk' (Subgroup.center ↥L)
    have hπker : π.ker = ⊥ :=
      (QuotientGroup.ker_mk' (Subgroup.center ↥L)).trans hZ
    have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hπker
    have hπbij : Function.Bijective π := ⟨hπinj, QuotientGroup.mk'_surjective _⟩
    let eZ : ↥L ≃* (↥L ⧸ Subgroup.center ↥L) := MulEquiv.ofBijective π hπbij
    obtain ⟨I', hI', f', hf', hfker'⟩ :=
      SevenThree.exists_perfect_onto_a9_of_injective π hπinj hI f hf hfker
    rcases hcase with hAlt | hSmall | hClass | hJ3
    · rcases hAlt with h9 | h10 | h11
      · exact Or.inl ⟨eZ.trans h9.some⟩
      · exact (SevenThree.false_of_fstar_alternating_ten hFstar hZ (eZ.trans h10.some)
          hTsyl hTHs hHsQuot).elim
      · exact Or.inr ⟨eZ.trans h11.some⟩
    · rcases hSmall with h227 | hpsp
      · exact (SevenThree.false_of_lieModel_l2_27_or_psp4_3 (Or.inl h227) I' f' hf').elim
      · exact (SevenThree.false_of_lieModel_l2_27_or_psp4_3 (Or.inr hpsp) I' f' hf').elim
    · exact (hA9 (↥L ⧸ Subgroup.center ↥L) hClass I' hI' f' hf' hfker').elim
    · exact (SevenThree.false_of_isSpor_j3 hJ3 I' f' hf').elim

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
