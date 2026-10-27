module

public import CFSG.Blueprint.Catalog
public import CFSG.Blueprint.ChevalleyRootGroups

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley

@[expose] def OmegaGen (p : ℕ) {G : Type*} [Group G] (A : Subgroup G) : Prop :=
  Subgroup.closure {x : G | x ∈ A ∧ x ^ p = 1} = A

theorem omegaGen_map_iff {p : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (A : Subgroup G) : OmegaGen p (A.map f) ↔ OmegaGen p A := by
  have key : f '' {x : G | x ∈ A ∧ x ^ p = 1} = {y : H | y ∈ A.map f ∧ y ^ p = 1} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxA, hxp⟩, rfl⟩
      exact ⟨⟨x, hxA, rfl⟩, by rw [← map_pow, hxp, map_one]⟩
    · rintro ⟨⟨x, hxA, rfl⟩, hy⟩
      refine ⟨x, ⟨hxA, ?_⟩, rfl⟩
      apply hf
      rw [map_pow, map_one]
      exact hy
  unfold OmegaGen
  rw [← key, ← MonoidHom.map_closure]
  exact (Subgroup.map_injective hf).eq_iff

theorem omegaGen_map {p : ℕ} {G H : Type*} [Group G] [Group H] (f : G →* H) {A : Subgroup G}
    (h : OmegaGen p A) : OmegaGen p (A.map f) := by
  unfold OmegaGen at *
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  calc A.map f = (Subgroup.closure {x : G | x ∈ A ∧ x ^ p = 1}).map f := by rw [h]
    _ = Subgroup.closure (f '' {x : G | x ∈ A ∧ x ^ p = 1}) := MonoidHom.map_closure _ _
    _ ≤ _ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, ⟨hxA, hxp⟩, rfl⟩
      exact Subgroup.subset_closure ⟨⟨x, hxA, rfl⟩, by rw [← map_pow, hxp, map_one]⟩

theorem charP_of_natCard_eq_pow {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ n) : CharP F p := by
  have := Fintype.ofFinite F
  have h0 : ((Fintype.card F : ℕ) : F) = 0 := Nat.cast_card_eq_zero F
  rw [← Nat.card_eq_fintype_card, hF, Nat.cast_pow] at h0
  exact (CharP.charP_iff_prime_eq_zero hp).mpr (pow_eq_zero_iff'.mp h0).1

theorem ncard_posRoots_G2 :
    {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α}.ncard = 6 := by
  have h : {α : Fin Tag.G2.rank → ℤ | IsRoot .G2 α ∧ 0 < height α} =
      ↑((rootFinset .G2).filter fun β => 0 < height β) := by
    ext d
    simp [mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

theorem omegaGen_posUnipotent
    {τ : Tag} {K : Type} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p] :
    OmegaGen p (posUnipotent τ K) := by
  unfold OmegaGen
  refine le_antisymm ((Subgroup.closure_le _).2 fun x hx => hx.1) ?_
  show (⨆ α ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}, rootSubgroup τ K α) ≤ _
  refine iSup₂_le fun α hα => ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  have hmem : pinnedX τ K α c ∈ rootSubgroup τ K α := Subgroup.subset_closure ⟨c, rfl⟩
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · exact (le_iSup₂ (f := fun α (_ : α ∈ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}) =>
      rootSubgroup τ K α) α hα) hmem
  · by_cases h1 : pinnedX τ K α c = 1
    · rw [h1, one_pow]
    · have := orderOf_eq_of_mem_rootSubgroup hmem h1
      rw [← this]
      exact pow_orderOf_eq_one _

theorem posUnipotent_le_adjointGroup'
    (τ : Tag) (K : Type) [Field K] : posUnipotent τ K ≤ adjointGroup τ K :=
  iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α

theorem untwisted_of_lieModel_G2 {K : Type} [Group K] {p n : ℕ} (h : LieModel K .G2 0 p n) :
    UntwistedChevalleyModel K .G2 (p ^ n) := by
  rcases h with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact h.2
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem twisted_of_lieModel_D4 {K : Type} [Group K] {p n : ℕ} (h : LieModel K .trialityD4 0 p n) :
    TwistedChevalleyModel K .D4 (p ^ n) := by
  rcases h with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
  · exact absurd h (by decide)
  · exact h.2
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47
