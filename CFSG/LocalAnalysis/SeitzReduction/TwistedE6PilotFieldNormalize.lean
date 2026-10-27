module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCores
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotCentralizerT

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section LevelTwist

variable
  {K : Type} [Field K]

theorem subsystemGroup_le_adjointGroup_E6 (S : Set (Fin TwistTag.E6.tag.rank)) :
    subsystemGroup TwistTag.E6.tag K S ≤ adjointGroup TwistTag.E6.tag K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  · exact Subgroup.subset_closure ⟨i, c, Or.inl rfl⟩
  · exact Subgroup.subset_closure ⟨i, c, Or.inr rfl⟩

theorem twistHom_mem_subsystemGroup {S : Set (Fin TwistTag.E6.tag.rank)}
    (hS : ∀ i ∈ S, TwistTag.E6.perm i ∈ S) (σ : K →+* K) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ subsystemGroup TwistTag.E6.tag K S) :
    twistHom TwistTag.E6 K σ g ∈ subsystemGroup TwistTag.E6.tag K S := by
  refine ((Subgroup.closure_le
    ((subsystemGroup TwistTag.E6.tag K S).comap (twistHom TwistTag.E6 K σ))).2 ?_) hg
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, twistHom_xUnit]
    exact Subgroup.subset_closure ⟨_, hS i hi, σ c, Or.inl rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, twistHom_yUnit]
    exact Subgroup.subset_closure ⟨_, hS i hi, σ c, Or.inr rfl⟩

theorem twistTagE6_perm_perm (i : Fin TwistTag.E6.tag.rank) : TwistTag.E6.perm (TwistTag.E6.perm i) = i := by
  revert i
  decide

theorem twistHom_twistHom_of_mem_subsystemGroup {S : Set (Fin TwistTag.E6.tag.rank)}
    {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ subsystemGroup TwistTag.E6.tag K S) :
    twistHom TwistTag.E6 K σ (twistHom TwistTag.E6 K σ g) = g := by
  have hle : subsystemGroup TwistTag.E6.tag K S ≤
      MonoidHom.eqLocus ((twistHom TwistTag.E6 K σ).comp (twistHom TwistTag.E6 K σ))
        (MonoidHom.id _) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, -, c, rfl | rfl⟩
    · change twistHom TwistTag.E6 K σ (twistHom TwistTag.E6 K σ (xUnit _ K i c)) = xUnit _ K i c
      rw [twistHom_xUnit, twistHom_xUnit, twistTagE6_perm_perm, hσσ]
    · change twistHom TwistTag.E6 K σ (twistHom TwistTag.E6 K σ (yUnit _ K i c)) = yUnit _ K i c
      rw [twistHom_yUnit, twistHom_yUnit, twistTagE6_perm_perm, hσσ]
  exact hle hg

@[expose] noncomputable def levelTwist {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    (S : Set (Fin TwistTag.E6.tag.rank)) (hS : ∀ i ∈ S, TwistTag.E6.perm i ∈ S) :
    MulAut (subsystemGroup TwistTag.E6.tag K S) where
  toFun g := ⟨twistHom TwistTag.E6 K σ g, twistHom_mem_subsystemGroup hS σ g.2⟩
  invFun g := ⟨twistHom TwistTag.E6 K σ g, twistHom_mem_subsystemGroup hS σ g.2⟩
  left_inv g := Subtype.ext (twistHom_twistHom_of_mem_subsystemGroup hσσ g.2)
  right_inv g := Subtype.ext (twistHom_twistHom_of_mem_subsystemGroup hσσ g.2)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)

theorem levelTwist_mul_self {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    {S : Set (Fin TwistTag.E6.tag.rank)} (hS : ∀ i ∈ S, TwistTag.E6.perm i ∈ S) :
    levelTwist hσσ S hS * levelTwist hσσ S hS = 1 :=
  MulEquiv.ext fun g => Subtype.ext (twistHom_twistHom_of_mem_subsystemGroup hσσ g.2)

theorem fixedSubgroup_levelTwist {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c)
    {S : Set (Fin TwistTag.E6.tag.rank)} (hS : ∀ i ∈ S, TwistTag.E6.perm i ∈ S) :
    fixedSubgroup (levelTwist hσσ S hS) =
      (subsystemGroup TwistTag.E6.tag K S ⊓ twistedFixedGroup TwistTag.E6 K σ).subgroupOf
        (subsystemGroup TwistTag.E6.tag K S) := by
  ext g
  rw [mem_subgroupOf, mem_inf, mem_twistedFixedGroup_iff_twistHom]
  constructor
  · intro hg
    have hg' : twistHom TwistTag.E6 K σ g = g := congrArg Subtype.val hg
    exact ⟨g.2, subsystemGroup_le_adjointGroup_E6 S g.2, hg'⟩
  · rintro ⟨-, -, hg⟩
    exact Subtype.ext hg

end LevelTwist

local instance twistedE6PilotFieldNormalizeNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

section Models

variable
  {K : Type} [Field K]

theorem perm_mem_setA (i : Fin TwistTag.E6.tag.rank) (hi : i ∈ E6GraphLevi.setA) :
    TwistTag.E6.perm i ∈ E6GraphLevi.setA := by
  have h : ∀ i : Fin TwistTag.E6.tag.rank, i ≠ 1 → TwistTag.E6.perm i ≠ 1 := by decide
  exact h i hi

theorem perm_mem_setD (i : Fin TwistTag.E6.tag.rank) (hi : i ∈ setD) :
    TwistTag.E6.perm i ∈ setD := by
  have h : ∀ i : Fin TwistTag.E6.tag.rank, (i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4) →
      (TwistTag.E6.perm i = 1 ∨ TwistTag.E6.perm i = 2 ∨ TwistTag.E6.perm i = 3 ∨
        TwistTag.E6.perm i = 4) := by decide
  exact h i hi

@[expose] noncomputable def a5LeviTwist {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) :
    MulAut (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA) :=
  levelTwist hσσ E6GraphLevi.setA perm_mem_setA

@[expose] noncomputable def d4LeviTwist {σ : K →+* K} (hσσ : ∀ c, σ (σ c) = c) :
    MulAut (subsystemGroup TwistTag.E6.tag K setD) :=
  levelTwist hσσ setD perm_mem_setD

variable {f : ℕ}

theorem fixedSubgroup_a5LeviTwist (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    fixedSubgroup (a5LeviTwist (apply_apply_eq hK hσ)) =
      (su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h1, h2, -⟩ := E6GraphLevi.subsystemGroup_inf_eq_map_realize hK hσ
    (E6GraphLevi.two_eq_zero_of_card_sq hf hK)
  rw [a5LeviTwist, fixedSubgroup_levelTwist, h2, ← h1]
  rfl

theorem perfectCore_fixedSubgroup_a5LeviTwist (hf : 1 ≤ f) {k : Type} [Field k] [Algebra k K]
    (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    perfectCore (fixedSubgroup (a5LeviTwist (apply_apply_eq hK hσ))) =
      (su6Levi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA) := by
  have := finite_of_card hK
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  rw [fixedSubgroup_a5LeviTwist hf hK hσ]
  have hP := isPerfect_su6Levi hf hk hK hσ
  refine CFSG.Quasithin.perfectCore_eq_self_of_perfect ?_
  have e := subgroupOfEquivOfLe (su6Levi_le_subsystemGroup σ)
  have : Group.IsPerfect ((su6Levi σ).subgroupOf
      (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.1 this

theorem fixedSubgroup_d4LeviTwist (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    fixedSubgroup (d4LeviTwist (apply_apply_eq hK hσ)) =
      (omegaMinusLevi σ).subgroupOf (subsystemGroup TwistTag.E6.tag K setD) := by
  unfold d4LeviTwist
  refine (fixedSubgroup_levelTwist (apply_apply_eq hK hσ) perm_mem_setD).trans ?_
  rw [omegaMinusLevi_eq_of_card hf hK hσ]

end Models

section Iso

variable
  {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] {σ : K →+* K}

structure FieldNeighbourIso2E6 (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (t : G)
    (X : Subgroup G) (M : Subgroup (ModGL TwistTag.E6.tag K)) (β₀ : MulAut M)
    (D : Subgroup (ModGL TwistTag.E6.tag K)) where
  Φ : M ≃* centralizerPerfectCore X
  fix : ∀ (y : graphFixedRootGroup TwistTag.E6 K σ), (y : ModGL TwistTag.E6.tag K) ∈ D →
    ∀ hyM : (y : ModGL TwistTag.E6.tag K) ∈ M,
      ((Φ ⟨y, hyM⟩ : centralizerPerfectCore X) : G) = ((e.symm y : L) : G)
  twist : ∀ x : M, ((Φ (β₀ x) : centralizerPerfectCore X) : G) = t * (Φ x : G) * t⁻¹

end Iso

end CFSG.SeitzReduction.TwistedE6Pilot
