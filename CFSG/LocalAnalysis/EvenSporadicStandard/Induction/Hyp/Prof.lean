module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.CanLoc
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Embed

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

@[expose] def LamProfile (ab : Prop) (b : ℕ) (X : Type*) [Group X] : Prop :=
  Group.IsSolvable X ∧ ElemBound b X ∧ (ab → TwoSubgroupsAbelian X)

theorem LamProfile.of_injective {ab : Prop} {b : ℕ} {X Y : Type*} [Group X] [Group Y]
    (h : LamProfile ab b Y) {f : X →* Y} (hf : Function.Injective f) : LamProfile ab b X := by
  have := h.1
  exact ⟨Group.isSolvable_of_isSolvable_injective hf, h.2.1.of_injective hf,
    fun hab => (h.2.2 hab).of_injective hf⟩

theorem twoSubgroupsAbelian_of_surjective {C Q : Type*} [Group C] [Finite C] [Group Q]
    (h : TwoSubgroupsAbelian C) {π : C →* Q} (hπ : Function.Surjective π) :
    TwoSubgroupsAbelian Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Q := Finite.of_surjective π hπ
  intro R hR x hx y hy
  obtain ⟨S, hS⟩ := hR.exists_le_sylow
  obtain ⟨S₀, rfl⟩ := Sylow.mapSurjective_surjective hπ 2 S
  obtain ⟨a, ha, rfl⟩ := hS hx
  obtain ⟨b, hb, rfl⟩ := hS hy
  have := h (S₀ : Subgroup C) S₀.isPGroup' a ha b hb
  rw [← map_mul, ← map_mul, this]

theorem twoSubgroupsAbelian_of_section {Y X : Type} [Group Y] [Finite Y] [Group X]
    (h : TwoSubgroupsAbelian Y) (hsec : IsSectionOf X Y) : TwoSubgroupsAbelian X := by
  obtain ⟨A, f, hf⟩ := hsec
  exact twoSubgroupsAbelian_of_surjective (h.of_injective A.subtype_injective) hf

theorem forall_sylow_isCyclic {G : Type*} [Group G] [Finite G]
    (h : ∃ P : Sylow 2 G, IsCyclic ↥P) : ∀ Q : Sylow 2 G, IsCyclic ↥Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := h
  intro Q
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have e : (P : Subgroup G) ≃* ((g • P : Sylow 2 G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.equivSMul (MulAut.conj g) _
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

end CFSG.EvenSporadicStandard.Induction.Hyp
