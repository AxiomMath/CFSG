module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.HDescSzFix
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts

public section

namespace CFSG.LocalAnalysis.GLTheoremA.HDesc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA TauCeti


theorem exists_suzuki_index_of_catalog {S : Type} [Group S] (h : catalogIs S fSuzuki) :
    ∃ (m : ℕ) (hv : (LieTypeIndex.suzuki m).Valid),
      Nonempty (S ≃* (CFSGIndex.lie ⟨.suzuki m, hv⟩).Group) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | suzuki m => exact ⟨m, hv, ⟨e⟩⟩
    | _ => exact hi.elim

theorem kDescFam_suzuki_holds (p : ℕ) : KDescFam p fSuzuki := by
  intro hp hp2 Y _ _ K B h hc hcB
  left
  obtain ⟨m, hv, ⟨e⟩⟩ := exists_suzuki_index_of_catalog hc
  haveI : Finite (CFSGIndex.lie ⟨.suzuki m, hv⟩).Group := Finite.of_equiv _ e.toEquiv
  have hS := CFSG.RankThree.PartTwo.Sec4.Census.suzukiModel_of_index m hv
  exact kConcl_of_rankOne hp hp2 h e (outPRankLE1_of_cyclic hp (suzuki_outer_cyclic hS))
    (suzuki_twoLocalRankLE1 hS hp hp2)
    (suzuki_outerFixLayer hS hp hp2) hcB

end CFSG.LocalAnalysis.GLTheoremA.HDesc
