module

public import CFSG.LocalAnalysis.OddStandard.ResidualAlt
public import CFSG.LocalAnalysis.OddStandard.ChildL34
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.OddStandard

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

@[expose] def AlternatingStandardFormInputW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Blueprint.Catalog G →
      ∀ (L : Subgroup G) (n : ℕ), CFSG.IsStandardSubgroup L →
        8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
        Nonempty (G ≃* alternatingGroup (Fin (n + 4))) ∨ OddLieType G

@[expose] def AltStdRankOneW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), StandardSetting G L →
    ∀ n : ℕ, 8 ≤ n → Nonempty (L ≃* alternatingGroup (Fin n)) →
      ¬ 2 ≤ Open.pRank 2 (centralizer (L : Set G)) →
        Nonempty (G ≃* alternatingGroup (Fin (n + 4))) ∨ OddLieType G

section Branches

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem altStd_quaternionW
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hS : StandardSetting G L) {n : ℕ} (hn : 8 ≤ n) (e : L ≃* alternatingGroup (Fin n))
    (S : Sylow 2 (centralizer (L : Set G))) {r : ℕ} (hr : 3 ≤ r)
    (hq : Nonempty ((S : Subgroup (centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    OddLieType G := by
  have := hS.simple
  have h7L : 7 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    exact Residual.seven_dvd_card_alternatingGroup (by omega)
  have h7 : 7 ∣ Nat.card G := h7L.trans (Subgroup.card_subgroup_dvd_card L)
  rcases ComponentClassification.StandardRecognition.quaternion_standard_recognition hCIT
    hS.nonab hS.isStandardSubgroup S hr hq with h | h | h
  · exact h
  · obtain ⟨eM⟩ : Nonempty (G ≃* NativeSporadic.M11) := h
    have hG : Nat.card G = 7920 :=
      (Nat.card_congr eM.toEquiv).trans Sporadic.Mathieu.card_M11
    rw [hG] at h7
    omega
  · obtain ⟨eM⟩ : Nonempty (G ≃* NativeSporadic.M12) := h
    have hG : Nat.card G = 95040 :=
      (Nat.card_congr eM.toEquiv).trans Sporadic.Mathieu.card_M12
    rw [hG] at h7
    omega

end Branches

theorem alternatingStandardFormInputW_of_rankOne
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (h1 : AltStdRankOneW) : AlternatingStandardFormInputW := by
  intro G _ _ _ hnonab hK L n hL hn e
  have hS : StandardSetting G L :=
    ⟨inferInstance, hnonab, hK, standardComponentIsStandard_of_cfsgStandard hL⟩
  by_cases hrank : 2 ≤ Open.pRank 2 (centralizer (L : Set G))
  · obtain ⟨e'⟩ := e
    exact Or.inl (altStd_rankTwo hRank2 hS hn e' hrank)
  · exact h1 G L hS n hn e hrank

end CFSG.OddStandard
