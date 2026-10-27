module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossRankTwoRest
import CFSG.RankThree.PartTwo.Census.Suzuki
public import CFSG.StronglyEmbedded.Catalog.Suzuki

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

theorem i294CrossThreeRankTwoSz_holds : I294CrossThreeRankTwoSz := by
  intro L _ _ _ _ d hd _ e _ hS _ _ _ _
  obtain ⟨i, hv⟩ := d
  cases i with
  | suzuki m =>
    have hm : 1 ≤ m :=
      (TauCeti.LieTypeIndex.inStandardRange_iff _).1 ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have h3 : ¬ 3 ∣ Nat.card L := by
      obtain ⟨e'⟩ := e
      rw [Nat.card_congr
        (e'.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv)).toEquiv]
      exact CFSG.RankThree.PartTwo.Census.not_three_dvd_card_suzukiMatrixGroup hm
    obtain ⟨S, hS'⟩ := hS
    have hcard : Nat.card (S : Subgroup L) = 1 := by
      rcases IsPGroup.card_eq_or_dvd S.isPGroup' with h | h
      · exact h
      · exact (h3 (dvd_trans h (Subgroup.card_subgroup_dvd_card _))).elim
    have hsub : Subsingleton (S : Subgroup L) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact (hS' (IsMulCommutative.of_comm fun a b => by rw [Subsingleton.elim a b])).elim
  | _ => exact (hd : False).elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
