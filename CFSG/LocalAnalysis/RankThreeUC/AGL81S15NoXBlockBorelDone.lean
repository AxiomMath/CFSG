module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15A3ComponentAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2.GN

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

theorem gnC_le_borelPre {Ls : Subgroup (X ⧸ gnC T)} : gnC T ≤ borelPre T Ls := by
  intro x hx
  rw [borelPre, Subgroup.mem_comap]
  have hx1 : toStar T x = 1 := by
    simpa [toStar] using (QuotientGroup.eq_one_iff (N := gnC T) x).mpr hx
  rw [hx1]
  exact Subgroup.one_mem _

theorem pCoreOf_le_borelPre (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)} :
    pCoreOf 2 (⊤ : Subgroup X) ≤ borelPre T Ls :=
  (pCoreOf_le_gnC hX).trans gnC_le_borelPre

theorem noXBlock_borelPre_done {X : Type} [Group X] [Finite X] {T : Subgroup X}
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (hLI : ∀ x ∈ Subgroup.centralizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) ⊓ Ls, Odd (orderOf x) → ∀ l ∈ Ls, x * l = l * x)
    (Y : Subgroup X) (hY : Y ≤ borelPre T Ls)
    (hsub : CFSG.Open.IsSubnormal Y (borelPre T Ls))
    (hblock : CFSG.AGLEmbedding.InClassXBlock Y) : False := by
  have hQH : pCoreOf 2 (⊤ : Subgroup X) ≤ borelPre T Ls :=
    pCoreOf_le_borelPre hX
  exact noXBlock_borelPre hX hLs hinv hLI
    (fun K hKle hsubK hblockK hKC hKstar hAlt =>
      false_of_isAltType_of_component_action hX hLs hKle hQH
        ⟨hblockK.1, hKle, hsubK⟩ hKC hKstar hAlt)
    Y hY hsub hblock

end CFSG.LocalAnalysis.RankThreeUC.S15

end
