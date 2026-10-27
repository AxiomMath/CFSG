module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFive
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeKFacts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NineTwelveOneSigmaStrongDefs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.FourteenFiveThreeTwo
import CFSG.Permutation.OrderThreeCentralizer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G]

theorem fourteenFiveThreeAt_of_inputs (h1 : NineFourTwoSigmaGen) (h2 : NineTwelveOneSigmaStrong)
    (hKF1 : KFactNineFourRankOneAut) (hKF2 : KFactNineFourStronglyEmbedded) (M : Subgroup G) :
    FourteenFiveThreeAt M := by
  intro hpre hK hU hL H E Q J h hA hB p hp A hAQ hA3 hrank hMbar
  by_contra hns
  obtain ⟨-, ⟨c⟩⟩ := FourteenFiveThree.exists_ctx hpre hK hU hL h hA hB hMbar
  have hAne : A ≠ ⊥ := by
    rintro rfl
    rw [Subgroup.card_bot] at hA3
    omega
  obtain ⟨a, haA, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one A with hbot | h
    · exact absurd hbot hAne
    · exact h
  have ha_pow : a ^ 3 = 1 := by
    have h := congrArg Subtype.val (pow_card_eq_one' (x := (⟨a, haA⟩ : A)))
    simpa [hA3] using h
  have hord3 : orderOf a = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime ha_pow ha1
  have haQ : a ∈ Q := hAQ haA
  have haKM : a ∈ kSub 3 M H ⊓ M := c.Q_le haQ
  have hzpcard : Nat.card (Subgroup.zpowers a) = 3 := by
    rw [Nat.card_zpowers, hord3]
  have hAeq : A = Subgroup.zpowers a :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA)
      (by rw [hA3, hzpcard])).symm
  have hcentral : Subgroup.centralizer (A : Set G) =
      Subgroup.centralizer ({a} : Set G) := by
    rw [hAeq, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hcentral] at hns hrank
  have hφord : orderOf (c.φ ⟨a, haKM.1⟩) = 3 :=
    c.orderOf_φ (x := ⟨a, haKM.1⟩) (by simpa using hord3)
  have hpermord : orderOf ((c.φ ⟨a, haKM.1⟩ : alternatingGroup (Fin 11)) :
      Equiv.Perm (Fin 11)) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hφord
  rcases CFSG.Permutation.card_support_eq_three_or_six_or_nine hpermord with h3 | h6 | h9
  · have hle := c.pRank_le_one_of_card_support_eq_three h1 hKF2 hp haKM hord3 h3
    omega
  · exact c.false_of_card_support_eq_six h1 h2 hKF1 hKF2 hp haKM hord3 h6 hrank
  · exact c.card_support_ne_nine haKM.1 hord3 hns h9

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
