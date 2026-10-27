module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76Rows
public import CFSG.LocalAnalysis.UniquenessCase.UC6K332Lists
import CFSG.LocalAnalysis.UniquenessCase.UC6K332K33
import CFSG.LocalAnalysis.AGL81TheoremCD.Section7.KFact76Conv

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section7

open CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route (K332Rows K33Cover K33Models K34Models
  isQuasisimple_open nonabelian_of_isQuasisimple goodRow_of_pRank_le_one pRank_quot_le_one
  k33_holds goodRow_of_k33Cover isSimpleGroup_of_k33Models goodRow_quot_of_simple
  goodRow_of_k33Models goodRow_of_isSpor goodRow_of_k34Models)

section K332


theorem Conv76.goodRow_quot_of_catalog
    (hR : K332Rows) {L : Type} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hcat : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L))
    (hr3 : CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 3) (hZ3 : IsPGroup 3 (Subgroup.center L)) :
    RonanK432.GoodRow (L ⧸ Subgroup.center L) := by
  have hqo := isQuasisimple_open hq
  have hS : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2.1
  have hnaS := hq.2.2
  have hnaL := nonabelian_of_isQuasisimple hq
  rcases (show CFSG.Open.pRank 3 (⊤ : Subgroup L) ≤ 1 ∨ CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 ∨
      CFSG.Open.pRank 3 (⊤ : Subgroup L) = 3 by omega) with h1 | h2 | h3
  · exact goodRow_of_pRank_le_one hS hnaS hcat (pRank_quot_le_one h1)
  · rcases (k33_holds L hqo hcat hZ3 h2 : K33Cover L ∨ K33Models L) with hc | hm
    · exact goodRow_of_k33Cover hS hnaS hc
    · have hsL := isSimpleGroup_of_k33Models hm
      exact goodRow_quot_of_simple hsL hnaL (goodRow_of_k33Models hR hsL hnaL h2 hm)
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 3) (G := Subgroup.center L)).1 hZ3
    have hodd : Odd (Nat.card (Subgroup.center L)) := by
      rw [hn]
      exact Odd.pow ⟨1, rfl⟩
    rcases (CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.k34odd_holds L hqo hcat hodd h3 :
        CFSG.LocalAnalysis.UniquenessCase.UCK.ThreeCover
            (fun Y _ => CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor Y .ONan) L ∨
          (¬ 3 ∣ Nat.card (Subgroup.center L) ∧ K34Models (L ⧸ Subgroup.center L)))
        with hc | ⟨-, hm⟩
    · exact goodRow_of_isSpor hS hnaS (by decide) hc.2.2
    · exact goodRow_of_k34Models hR hS hnaS hm

theorem rows76RankThree_of_k332Rows (hR : K332Rows) : Rows76RankThree := by
  intro S _ _ _ _ hcat _ hcov
  obtain ⟨L, _, _, hq, hZ3, ⟨e⟩, hr3⟩ := hcov
  have hcatL : CFSG.Open.IsCatalogGroup (L ⧸ Subgroup.center L) := by
    obtain ⟨i, ⟨f⟩⟩ := hcat
    exact ⟨i, ⟨e.trans f⟩⟩
  exact row76_of_goodRow ⟨L, inferInstance, inferInstance, hq, hZ3, ⟨e⟩, hr3⟩
    (RonanK432.GoodRow.of_mulEquiv e (Conv76.goodRow_quot_of_catalog hR hq hcatL hr3 hZ3))

end K332

end CFSG.LocalAnalysis.AGL81TheoremCD.Section7
