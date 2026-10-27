module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofLeviLayer

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.RankTwoStandard

section Model

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] {H : Subgroup (GL ι K)}
variable {G : Type} [Group G] {A : Subgroup G}

@[expose] noncomputable def quotModelHom (e : rankTwoQuot A ≃* StatedProj H) : ↥A →* StatedProj H :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center ↥A))

variable {e : rankTwoQuot A ≃* StatedProj H}

theorem quotModelHom_surjective : Function.Surjective (quotModelHom e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem ker_quotModelHom : (quotModelHom e).ker = center ↥A := by
  ext x
  rw [MonoidHom.mem_ker, quotModelHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem represents_iff_quotModelHom {x : G} {M : GL ι K} (hM : M ∈ H) :
    Represents e x M ↔ ∃ hx : x ∈ A, quotModelHom e ⟨x, hx⟩ = QuotientGroup.mk ⟨M, hM⟩ := by
  constructor
  · rintro ⟨hx, hM', he⟩
    exact ⟨hx, he⟩
  · rintro ⟨hx, h⟩
    exact ⟨hx, hM, h⟩

end Model

section Gen

variable {G : Type} [Group G] {A : Subgroup G} {P : Type*} [Group P] {θ : ↥A →* P}

theorem closure_le_levLift [Finite G] (hker : θ.ker = center ↥A) (hθ : Function.Surjective θ)
    {S : Subgroup P} (hperf : ⁅S, S⁆ = S) (hZ : Odd (Nat.card (center ↥A))) {T : Set G}
    (hT : ∀ y ∈ T, y ∈ liftSub θ S ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) : closure T ≤ levLift θ S :=
  (closure_le _).mpr fun y hy =>
    mem_levLift_of_pow hker hθ hperf hZ (hT y hy).1 (hT y hy).2.choose_spec

theorem le_centralizer_closure_levLift (hker : θ.ker = center ↥A)
    (hZ : Odd (Nat.card (center ↥A))) {S : Subgroup P} {T : Set G}
    (hT : ∀ y ∈ T, y ∈ liftSub θ S ∧ ∃ j : ℕ, y ^ 2 ^ j = 1) {Y : Subgroup G}
    (hY : ∀ x ∈ Y, ∃ hx : x ∈ A, ∀ l ∈ S, θ ⟨x, hx⟩ * l = l * θ ⟨x, hx⟩) :
    Y ≤ centralizer (closure T : Set G) := by
  rw [le_centralizer_iff, closure_le]
  intro y hy
  obtain ⟨hyL, j, hyj⟩ := hT y hy
  obtain ⟨hyA, hyθ⟩ := mem_liftSub.mp hyL
  rw [SetLike.mem_coe, mem_centralizer_iff]
  intro x hx
  obtain ⟨hxA, hxθ⟩ := hY x hx
  exact commute_of_theta_commute hker hZ hxA hyA hyj (hxθ _ hyθ)

theorem levLift_le_centralizer_levLift (hker : θ.ker = center ↥A) {S S' : Subgroup P}
    (h : ∀ s ∈ S, ∀ s' ∈ S', s * s' = s' * s) :
    levLift θ S ≤ centralizer (levLift θ S' : Set G) := by
  rw [le_centralizer_iff]
  intro x hx
  obtain ⟨hxA, hxθ⟩ := mem_liftSub.mp (levLift_le_liftSub hx)
  have hle := levLift_le_centralizer hker hxA (S := S) fun s hs => (h s hs _ hxθ).symm
  rw [mem_centralizer_iff]
  intro l hl
  exact mem_centralizer_singleton_iff.mp (hle hl)

end Gen

end CFSG.ComponentClassification.RankTwoClassical
