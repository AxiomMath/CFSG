module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Steps
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank614L615

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (Prop614Pair exists_isMaxTwoInvariantIn_of_le)
open CFSG.Yardstones.Md8ed6d263d89 (YSPEmptyPlaneLocals)

theorem ysPEmptyPlaneLocals_of_steps (h63 : StepL63) (h617 : StepL617) (hK : StepKGroup) :
    YSPEmptyPlaneLocals := by
  intro G _ _ _ hnonab hKp hchar he hpre hD1 hD2 hFC h57 p P M hp5 hIH hloc hPM x hxP hxo hxC hxS
    H hH hBH hex
  have hglob : Global G := ⟨⟨inferInstance, hnonab, hKp, hchar, he, hpre⟩, hD1, hD2, hFC, h57⟩
  have hS : Situation G p P M := ⟨hglob, hp5, hIH, hloc, hPM⟩
  have hx : Point P M x := ⟨hxP, hxo, hxC, hxS⟩
  obtain ⟨z, hz, -, -, -, hB⟩ := exists_central_generator hS hx
  rw [hB] at hBH hex
  obtain ⟨S, hSHM, hS1, hS2, hBS⟩ := hex
  by_contra hHM
  have hnr : NormalizerRank p P M (zpowers x ⊔ zpowers z) := by
    by_cases hcon : HasPrimeConstraint (G := M) p
    · exact normalizerRank_of_constrained hS hx hz hcon
    · exact h63 G p P M x z hS hx hz hcon
  obtain ⟨S', hSS', hS'⟩ := exists_isMaxTwoInvariantIn_of_le
    (B := zpowers x ⊔ zpowers z) (X := H ⊓ M) (S := S) ⟨hSHM, hS2, hBS⟩
  have hpair : Prop614Pair M (zpowers x ⊔ zpowers z) H S' :=
    ⟨hH, hBH, hHM, hS', ne_bot_of_le_ne_bot hS1 hSS'⟩
  obtain ⟨H₀, S₀, hopt⟩ := exists_optimal hS hx hz hnr ⟨H, S', hpair⟩
  exact hK G p P M x z hS hx hz H₀ S₀ hopt (h617 G p P M x z hS hx hz H₀ S₀ hopt)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
