module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviLayer

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard
open scoped commutatorElement

variable {K : Type} [Field K] {k : ℕ}
variable {G : Type} [Group G] {A : Subgroup G} {θ : ↥A →* projectiveSL (2 + k) K}
  (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
include hker hθ

theorem nonempty_leviW_equiv [Finite G] [Finite K] (hZ : Odd (Nat.card (center ↥A))) {m : ℕ}
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m) (hk : 1 ≤ k) :
    Nonempty (↥(leviW θ) ≃* SpecialLinearGroup (Fin 2) K) := by
  have h4 : ∃ s : Finset K, s.card = 4 := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset K)) (n := 4)
      (by
        rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm)
    exact ⟨s, hs⟩
  exact nonempty_levLift_equiv_SL2 hker hθ hZ hm hK (commutator_barW h4) (barWEquiv K k hk)

variable (h4 : ∃ s : Finset K, s.card = 4) (hk : 2 ≤ k)
include h4 hk

theorem closure_le_leviL [Finite G] (hZ : Odd (Nat.card (center ↥A))) {S : Set G}
    (hS : ∀ y ∈ S, y ∈ liftSub θ (barL K k) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) : closure S ≤ leviL θ :=
  (closure_le _).mpr fun y hy =>
    mem_levLift_of_pow hker hθ (commutator_barL hk h4) hZ (hS y hy).1 (hS y hy).2.choose_spec

omit hθ h4 hk in
theorem le_centralizer_closure (hZ : Odd (Nat.card (center ↥A))) {S : Set G}
    (hS : ∀ y ∈ S, y ∈ liftSub θ (barL K k) ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) {Y : Subgroup G}
    (hY : ∀ x ∈ Y, ∃ hx : x ∈ A, ∀ l ∈ barL K k, θ ⟨x, hx⟩ * l = l * θ ⟨x, hx⟩) :
    Y ≤ centralizer (closure S : Set G) := by
  rw [le_centralizer_iff, closure_le]
  intro y hy
  obtain ⟨hyL, j, hyj⟩ := hS y hy
  obtain ⟨hyA, hyθ⟩ := mem_liftSub.mp hyL
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro x hx
  obtain ⟨hxA, hxθ⟩ := hY x hx
  exact commute_of_theta_commute hker hZ hxA hyA hyj (hxθ _ hyθ)

theorem isQuasisimple_leviL : CFSG.IsQuasisimple ↥(leviL θ) :=
  isQuasisimple_levLift hker hθ (commutator_barL hk h4) (isQuasisimple_barL hk h4)

theorem open_isQuasisimple_leviL : CFSG.Open.IsQuasisimple ↥(leviL θ) := by
  obtain ⟨hp, hs, -⟩ := isQuasisimple_leviL hker hθ h4 hk
  exact ⟨hp.commutator_eq_top, hs⟩

omit h4 in
theorem odd_card_center_leviL [Finite G] [Finite K] (hZ : Odd (Nat.card (center ↥A))) {m : ℕ}
    (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (h4 : ∃ s : Finset K, s.card = 4) :
    Odd (Nat.card (center ↥(leviL θ))) :=
  odd_card_center_levLift hker hθ (commutator_barL hk h4) hZ (odd_card_center_barL hm hK)

@[expose] noncomputable def leviLQuotEquiv :
    rankTwoQuot (leviL θ) ≃* StatedProj (StatedSL k K) :=
  ((levLiftQuotEquiv hker hθ (commutator_barL hk h4)).trans
    (QuotientGroup.congr (center (barL K k)) (center (SpecialLinearGroup (Fin k) K))
      (barLEquiv K k).symm (Subgroup.map_center_eq _))).trans
    (projectiveSpecialLinearGroupEquivStatedProj k K)

omit h4 in
theorem statedClassicalModel_leviL [Finite K] {m : ℕ} (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (h4 : ∃ s : Finset K, s.card = 4) :
    StatedClassicalModel (rankTwoQuot (leviL θ)) .PSL k 2 m := by
  have hq : 4 ≤ 2 ^ m := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨⟨Nat.prime_two, by omega, hk, fun h => ?_, fun h => ?_⟩, K, inferInstance,
    inferInstance, hK, ⟨leviLQuotEquiv hker hθ h4 hk⟩⟩
  · simp only [Prod.mk.injEq] at h
    omega
  · simp only [Prod.mk.injEq] at h
    have := h.2
    omega

end CFSG.ComponentClassification.RankTwoClassical
