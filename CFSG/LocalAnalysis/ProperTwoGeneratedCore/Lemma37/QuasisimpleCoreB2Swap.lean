module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB2Basic
public import CFSG.Dihedral.DisconnectedInvolutionGraph.PGroupNormalizerExtension

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem exists_mem_normalizer_not_mem_of_lt_sylow {G : Type} [Group G] [Finite G] {T : Subgroup G}
    (S : Sylow 2 G) (hTS : T ≤ S) (hne : (S : Subgroup G) ≠ T) :
    ∃ x ∈ (S : Subgroup G), x ∈ Subgroup.normalizer (T : Set G) ∧ x ∉ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hTE, -, hES⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.pgroup_strict_normalizer_extension 2 T S
      S.isPGroup' (lt_of_le_of_ne hTS (Ne.symm hne))
  obtain ⟨x, hxE, hxT⟩ := IsConcreteLE.exists_of_lt hTE
  exact ⟨x, (hES hxE).1, (hES hxE).2, hxT⟩

namespace PartC

variable {G : Type} [Group G] {T Q P : Subgroup G} {e u : G}

@[expose] def CaseB2Normalized (T P : Subgroup G) : Prop :=
  ∀ R : Subgroup G, IsPGroup 2 R → T ≤ R → R ≤ Subgroup.normalizer (T : Set G) →
    R ≤ Subgroup.normalizer (P : Set G) → R ≤ T

variable [Finite G]

theorem le_normalizer_right_factor (hc : PartC T Q P e u) : T ≤ Subgroup.normalizer (P : Set G) :=
  fun t ht => mem_normalizer_of_conj_mem fun p hp => hc.normal_right t ht p hp

theorem mem_of_caseB2Normalized (hc : PartC T Q P e u) (hn : CaseB2Normalized T P)
    {S : Subgroup G} (hS : IsPGroup 2 S) (hTS : T ≤ S) {x : G} (hxS : x ∈ S)
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxP : x ∈ Subgroup.normalizer (P : Set G)) :
    x ∈ T := by
  have hRS : T ⊔ Subgroup.zpowers x ≤ S := _root_.sup_le hTS (Subgroup.zpowers_le.mpr hxS)
  refine hn (T ⊔ Subgroup.zpowers x) (hS.to_le hRS) le_sup_left
    (_root_.sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxN))
    (_root_.sup_le hc.le_normalizer_right_factor (Subgroup.zpowers_le.mpr hxP))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

omit [Finite G] in
theorem conj_mem_self_of_mem_normalizer {x : G} (hxN : x ∈ Subgroup.normalizer (T : Set G)) :
    ∀ t ∈ T, x * t * x⁻¹ ∈ T :=
  fun t ht => (Subgroup.mem_normalizer_iff.mp hxN t).mp ht

theorem swap_of_caseB2Normalized (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hn : CaseB2Normalized T P) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hTS : T ≤ S) {x : G} (hxS : x ∈ S)
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxT : x ∉ T) :
    (∀ p ∈ P, x * p * x⁻¹ ∈ Q) ∧ (∀ q ∈ Q, x * q * x⁻¹ ∈ P) := by
  rcases hc.conj_right_or_swap hT φ (conj_mem_self_of_mem_normalizer hxN) with hP | hswap
  · exact (hxT (hc.mem_of_caseB2Normalized hn hS hTS hxS hxN
      (mem_normalizer_of_conj_mem hP))).elim
  · exact hswap

theorem mem_or_inv_mul_mem_of_caseB2Normalized (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hn : CaseB2Normalized T P) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hTS : T ≤ S) {x : G} (hxS : x ∈ S)
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxT : x ∉ T) {s : G} (hsS : s ∈ S)
    (hsN : s ∈ Subgroup.normalizer (T : Set G)) : s ∈ T ∨ x⁻¹ * s ∈ T := by
  by_cases hsT : s ∈ T
  · exact Or.inl hsT
  right
  have hs := hc.swap_of_caseB2Normalized hT φ hn hS hTS hsS hsN hsT
  have hx := hc.swap_of_caseB2Normalized hT φ hn hS hTS (S.inv_mem hxS)
    (Subgroup.inv_mem _ hxN) (fun h => hxT (by simpa using T.inv_mem h))
  refine hc.mem_of_caseB2Normalized hn hS hTS (S.mul_mem (S.inv_mem hxS) hsS)
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hxN) hsN) (mem_normalizer_of_conj_mem fun p hp => ?_)
  have h := hx.2 _ (hs.1 p hp)
  rwa [show x⁻¹ * (s * p * s⁻¹) * x⁻¹⁻¹ = x⁻¹ * s * p * (x⁻¹ * s)⁻¹ by group] at h

theorem mul_self_mem_of_caseB2Normalized (hc : PartC T Q P e u) (hT : T ≤ Q ⊔ P)
    (φ : P ≃* QuaternionGroup 2) (hn : CaseB2Normalized T P) {S : Subgroup G}
    (hS : IsPGroup 2 S) (hTS : T ≤ S) {x : G} (hxS : x ∈ S)
    (hxN : x ∈ Subgroup.normalizer (T : Set G)) (hxT : x ∉ T) : x * x ∈ T := by
  rcases hc.mem_or_inv_mul_mem_of_caseB2Normalized hT φ hn hS hTS hxS hxN hxT
      (S.mul_mem hxS hxS) (Subgroup.mul_mem _ hxN hxN) with h | h
  · exact h
  · rw [inv_mul_cancel_left] at h
    exact (hxT h).elim

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
