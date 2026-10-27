module

public import CFSG.LocalAnalysis.OddStandard.Solomon75StdDefs
import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionRank
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.OddStandard.ResidualAlt
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

section Branches

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem seven_dvd_card_of_quotient_alt {n : ℕ} (hn : 7 ≤ n)
    (e : L ⧸ center L ≃* alternatingGroup (Fin n)) : 7 ∣ Nat.card L := by
  have h7 : 7 ∣ Nat.card (L ⧸ center L) := by
    rw [Nat.card_congr e.toEquiv]
    exact Residual.seven_dvd_card_alternatingGroup hn
  exact h7.trans (Subgroup.card_quotient_dvd_card (center L))

theorem altStd_quaternionW'
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hS : StandardSetting G L) (h7L : 7 ∣ Nat.card L)
    (S : Sylow 2 (centralizer (L : Set G))) {r : ℕ} (hr : 3 ≤ r)
    (hq : Nonempty ((S : Subgroup (centralizer (L : Set G))) ≃* QuaternionGroup (2 ^ (r - 2)))) :
    OddLieType G := by
  have := hS.simple
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

theorem altStd_rankTwo'
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (hS : StandardSetting G L) {n : ℕ} (hn : 8 ≤ n)
    (θ : L ⧸ center L ≃* alternatingGroup (Fin n))
    (hrank : 2 ≤ Open.pRank 2 (centralizer (L : Set G))) :
    Nonempty (G ≃* alternatingGroup (Fin (n + 4))) := by
  have hH : ComponentClassification.RankTwoStandard.RankTwoHyp G L :=
    ⟨hS.kProper, hS.standard, hS.not_normal, hrank⟩
  have hXG : ComponentClassification.RankTwoStandard.rankTwoX L ≃* G :=
    (MulEquiv.subgroupCongr hS.normalClosure_eq_top).trans Subgroup.topEquiv
  rcases hRank2 G L hH hS.oddCore_eq_bot n (by omega) ⟨θ⟩ with he | ⟨h5, -⟩ | ⟨h5, -, -⟩
  · exact he.map fun e' => hXG.symm.trans e'
  · omega
  · omega

end Branches

theorem solomon2AnStdW_of_cyclic
    (hRank2 : ComponentClassification.RankTwoStandard.RankTwoAlternatingStandard)
    (hCIT : ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hCyc : Solomon2AnStdCyclic) : Solomon2AnStdW := by
  intro G _ _ L hS n hn hθ hZ
  have := hS.simple
  obtain ⟨θ⟩ := hθ
  obtain ⟨S⟩ : Nonempty (Sylow 2 (centralizer (L : Set G))) := inferInstance
  rcases ComponentClassification.StandardRecognition.standard_centralizer_rank_split
    hS.isStandardSubgroup S with h2 | ⟨hcyc, -⟩ | ⟨r, hr, hq, -⟩
  · exact Or.inl ⟨n + 4, by omega, altStd_rankTwo' hRank2 hS hn θ h2⟩
  · rcases hCyc G L hS.standard n hn ⟨θ⟩ hZ ⟨S, hcyc⟩ with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl (altStd_quaternionW' hCIT hS (seven_dvd_card_of_quotient_alt (by omega) θ)
      S hr hq))

end CFSG.OddStandard.Solomon75
