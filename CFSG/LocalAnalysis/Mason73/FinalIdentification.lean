module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitInputs
public import CFSG.CGT.Stroth77.L4Sylow.Model

public section

namespace CFSG.LocalAnalysis.Mason73

open CFSG.CGT.Stroth77.L4Sylow
open scoped MatrixGroups

theorem not_isSporadic_M11_of_l4Sylow
    {G : Type} [Group G] [Finite G] {n : ℕ} (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* CFSG.CGT.Stroth77.L4Sylow.L4Model n)) :
    ¬ CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 := by
  intro hM11
  obtain ⟨e⟩ := hM11
  obtain ⟨eP⟩ := hP
  have hcardP : Nat.card ↥(P : Subgroup G) = 2 ^ (3 * n + 1) := by
    rw [Nat.card_congr eP.toEquiv, CFSG.CGT.Stroth77.L4Sylow.card_L4Model (by omega)]
  have hdvd : Nat.card ↥(P : Subgroup G) ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card (P : Subgroup G)
  have hG : Nat.card G = 7920 := by
    rw [Nat.card_congr e.toEquiv]
    simpa only [CFSG.Blueprint.NativeSporadic.Carrier] using
      (CFSG.Sporadic.Schreier.m11_card : Nat.card CFSG.Blueprint.NativeSporadic.M11 = 7920)
  have h10 : 2 ^ 10 ∣ Nat.card ↥(P : Subgroup G) := by
    rw [hcardP]
    exact pow_dvd_pow 2 (by omega)
  have hdiv : 2 ^ 10 ∣ 7920 := by
    simpa [hG] using h10.trans hdvd
  norm_num at hdiv

@[expose] def Mason44Conclusion (G : Type) [Group G] : Prop :=
  ∃ z : G, orderOf z = 2 ∧ ∃ J : Subgroup G, z ∈ J ∧
    CFSG.Open.IsSubnormal J (Subgroup.centralizer ({z} : Set G)) ∧
    ∃ P : Sylow 2 J,
      (∃ r : ℕ, 3 ≤ r ∧ Nonempty ((P : Subgroup J) ≃* QuaternionGroup (2 ^ (r - 2)))) ∧
      CFSG.Open.classicalInvolutionWitness J

theorem oddLieType_or_M11_of_mason44
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h44 : Mason44Conclusion G) :
    CFSG.Blueprint.OddLieType G ∨
      CFSG.Blueprint.NativeSporadic.IsSporadic G .M11 := by
  obtain ⟨z, hz, J, hzJ, hsub, P, hquat, hwit⟩ := h44
  let eF : CFSG.Open.genFittingFStar G ≃* G :=
    (MulEquiv.subgroupCongr (CFSG.ComponentClassification.StandardRecognition.genFittingFStar_eq_top_of_isSimpleGroup hnonab)).trans
      Subgroup.topEquiv
  have : IsSimpleGroup (CFSG.Open.genFittingFStar G) := eF.isSimpleGroup
  have hFnonab : ∃ a b : CFSG.Open.genFittingFStar G, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact ⟨eF.symm a, eF.symm b, fun h => hab (by simpa using congrArg eF h)⟩
  rcases (hCIT G hFnonab z hz J hzJ hsub P hquat).1 hwit with h | h
  · exact .inl ((CFSG.ClassicalInvolution.oddLieType_congr eF).1 h)
  · exact .inr ((CFSG.ClassicalInvolution.isSporadic_congr eF).1 h)

@[expose] def L4SylowComparison : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] {n : ℕ}, 3 ≤ n →
    ∀ (P : Sylow 2 G), Nonempty (↥(P : Subgroup G) ≃* CFSG.CGT.Stroth77.L4Sylow.L4Model n) →
    CFSG.Blueprint.OddLieType G → CFSG.OddStandard.HigherRank.YamadaG23.LitPSLU4S G

theorem masonL4_of_mason44_comparison
    (hCIT : CFSG.ComponentClassification.StandardRecognition.ClassicalInvolutionTheoremModels)
    (hSC : L4SylowComparison)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} (hn : 3 ≤ n) (P : Sylow 2 G)
    (hP : Nonempty (↥(P : Subgroup G) ≃* CFSG.CGT.Stroth77.L4Sylow.L4Model n))
    (h44 : Mason44Conclusion G) :
    CFSG.OddStandard.HigherRank.YamadaG23.LitPSLU4S G := by
  rcases oddLieType_or_M11_of_mason44 hCIT hnonab h44 with h | h
  · exact hSC G hn P hP h
  · exact (not_isSporadic_M11_of_l4Sylow hn P hP h).elim

end CFSG.LocalAnalysis.Mason73
