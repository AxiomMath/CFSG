module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Char
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePSetup
public import CFSG.Dihedral.DisconnectedInvolutionGraph.SylowNormalizerControl

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {J : Type} [Group J] [Finite J] {u e : J}

theorem eight_dvd_two_pow_sub_two {n : ℕ} (hn : 5 ≤ n) : 8 ∣ 2 ^ (n - 2) := by
  rw [show n - 2 = 3 + (n - 5) by omega, pow_add]
  exact Dvd.intro _ rfl

theorem PartC.false_of_caseC2 (hperf : Group.IsPerfect J) (T : Sylow 2 (quasiNormalizer u))
    {R P₁ : Subgroup J} (hc : PartC (partCSylow T) R P₁ e u) (hP₁ : ¬ IsCyclic P₁) {y : J}
    (hyT : y ∈ partCSylow T) (hy : y ∉ R ⊔ P₁) (hyy : y * y ∈ P₁) {n : ℕ} (hn : 5 ≤ n)
    (hφ : Nonempty ((P₁ ⊔ Subgroup.zpowers y : Subgroup J) ≃* QuaternionGroup (2 ^ (n - 2)))) :
    False := by
  obtain ⟨φ⟩ := hφ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : NeZero (2 ^ (n - 2)) := ⟨by positivity⟩
  have hN := eight_dvd_two_pow_sub_two hn
  have hnorm : partCSylow T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set J) :=
    Subgroup.map_subtype_le _
  have hNT := hc.normalizer_le_normalizer_zpowers_of_quatGen φ hyT hy hyy hN hnorm
  obtain ⟨S, hS⟩ := CFSG.DisconnectedInvolutionGraph.Helpers.sylow_inheritance_of_normalizer_le
    2 (quasiNormalizer u) T hNT
  exact hc.false_of_labelled φ hperf hyT hy hyy hP₁ hN S hS.symm hnorm hNT

theorem PartC.false_of_caseC2_of_rank (hperf : Group.IsPerfect J)
    (T : Sylow 2 (quasiNormalizer u)) {R P₁ : Subgroup J} (hc : PartC (partCSylow T) R P₁ e u)
    (hrank : 3 ≤ CFSG.Open.pRank 2 (partCSylow T)) {y : J} (hyT : y ∈ partCSylow T)
    (hy : y ∉ R ⊔ P₁) (hyy : y * y ∈ P₁) {n : ℕ} (hn : 5 ≤ n)
    (hφ : Nonempty ((P₁ ⊔ Subgroup.zpowers y : Subgroup J) ≃* QuaternionGroup (2 ^ (n - 2)))) :
    False :=
  hc.false_of_caseC2 hperf T (hc.not_isCyclic_right hrank) hyT hy hyy hn hφ

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
