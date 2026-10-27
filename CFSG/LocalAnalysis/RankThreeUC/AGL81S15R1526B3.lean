module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526D
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1526P0a
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open scoped commutatorElement

section Row26M

variable {X : Type} [Group X] [Finite X]

theorem ncard_CY_le_three (hKSML3 : KSML3) {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    (hL3 : ∀ (Ls : Subgroup (X ⧸ gnC T)) (L : Subgroup X), GNYComponent T T₁ T₂ Ls →
      LiftOf T L Ls → IsLThreeOfExp 1 ↥Ls) :
    Set.ncard (CY T T₁ T₂) ≤ 3 := by
  classical
  haveI : Finite (Subgroup X) := Finite.of_injective _ (SetLike.coe_injective (A := Subgroup X))
  have hfin : (CY T T₁ T₂).Finite := Set.toFinite _
  have hmem : ∀ L ∈ hfin.toFinset, L ∈ CY T T₁ T₂ := fun L hL => hfin.mem_toFinset.1 hL
  have hkey : ∀ L ∈ hfin.toFinset, IsC2 L ∧ CFSG.Open.pRank 3 L = 1 ∧
      CFSG.Open.pRank 3 (KFactsPair.centerIn (barO2 L)) ≤ 0 := by
    intro L hL
    obtain ⟨Ls, hLs, hLift⟩ := hmem L hL
    obtain ⟨hbar, hcard⟩ := barO2_isLThree_of_lift hKSML3 hX hLs.1 hLift (hL3 Ls L hLs hLift)
    refine ⟨hLift.1, (pRank_eq_one_of_isLThree hLift.1 hbar).1, ?_⟩
    have h0 := pRank_eq_zero_of_not_dvd_s15 (A := KFactsPair.centerIn (barO2 L)) Nat.prime_three
      (by
        unfold KFactsPair.centerIn
        rw [Subgroup.card_map_of_injective (barO2 L).subtype_injective, hcard]
        norm_num)
    exact h0.le
  have hsum := pRank_sum_le_pRank_sup hfin.toFinset (fun L hL => (hkey L hL).1) Nat.prime_three
    (by norm_num) (s := 0) (fun L hL => (hkey L hL).2.2)
  have hone : ∑ L ∈ hfin.toFinset, CFSG.Open.pRank 3 L = hfin.toFinset.card := by
    rw [Finset.sum_congr rfl (fun L hL => (hkey L hL).2.1)]
    simp
  have hsup : CFSG.Open.pRank 3 (hfin.toFinset.sup id) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt le_top).trans h3
  rw [Set.ncard_eq_toFinset_card _ hfin]
  rw [hone] at hsum
  omega

end Row26M

end CFSG.LocalAnalysis.RankThreeUC.S15
