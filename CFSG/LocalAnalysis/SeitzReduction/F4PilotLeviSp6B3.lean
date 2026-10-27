module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviSp6
public import CFSG.LieType.Chevalley.EvenF4ExceptionalRootLayers

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld.LieEmbed CFSG.LieType.Chevalley
open CFSG.LieType.Ree (ReeTag)

section RootSpan


theorem rootSpan_subgroupOf_eq_closure (τ : Tag) (K : Type) [Field K]
    (S : Set (Fin τ.rank → ℤ)) :
    (rootSpan τ K S).subgroupOf (adjointGroup τ K) =
      closure {g : adjointGroup τ K | ∃ α ∈ S, ∃ c : K, pinnedX τ K α c = g} := by
  apply map_injective (adjointGroup τ K).subtype_injective
  rw [subgroupOf_map_subtype, inf_of_le_left (show rootSpan τ K S ≤ adjointGroup τ K from
      iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α), MonoidHom.map_closure,
    CFSG.LieType.Chevalley.rootSpan_eq_closure K S]
  congr 1
  ext g
  constructor
  · rintro ⟨α, hα, c, rfl⟩
    exact ⟨⟨pinnedX τ K α c, pinnedX_mem_adjointGroup α c⟩, ⟨α, hα, c, rfl⟩, rfl⟩
  · rintro ⟨h, ⟨α, hα, c, hh⟩, rfl⟩
    exact ⟨α, hα, c, hh⟩

end RootSpan

@[expose] def b3LeviRoots : Set (Fin (Tag.rank .F4) → ℤ) :=
  {γ | IsRoot .F4 γ ∧ γ ⟨3, by decide⟩ = 0}

theorem mem_b3LeviRoots {γ : Fin (Tag.rank .F4) → ℤ} :
    γ ∈ b3LeviRoots ↔ IsRoot .F4 γ ∧ γ ⟨3, by decide⟩ = 0 :=
  Iff.rfl

theorem dualRoot_F4_apply_three_eq_zero {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (h : γ ⟨0, by decide⟩ = 0) : ReeTag.F4.dualRoot γ ⟨3, by decide⟩ = 0 := by
  have hp : ReeTag.F4.perm.symm ⟨3, by decide⟩ = ⟨0, by decide⟩ := by decide
  simp only [ReeTag.dualRoot, ReeTag.dualMapInt, hp, h, mul_zero, Int.zero_ediv]

theorem dualRoot_F4_apply_zero_eq_zero {γ : Fin ReeTag.F4.tag.rank → ℤ}
    (h : γ ⟨3, by decide⟩ = 0) : ReeTag.F4.dualRoot γ ⟨0, by decide⟩ = 0 := by
  have hp : ReeTag.F4.perm.symm ⟨0, by decide⟩ = ⟨3, by decide⟩ := by decide
  simp only [ReeTag.dualRoot, ReeTag.dualMapInt, hp, h, mul_zero, Int.zero_ediv]

theorem dualRoot_mem_b3LeviRoots_iff {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ReeTag.F4.dualRoot γ ∈ b3LeviRoots ↔ γ ∈ c3LeviRoots := by
  refine ⟨fun h => ⟨hγ, ?_⟩, fun h =>
    ⟨ReeTag.isRoot_dualRoot (t := .F4) hγ, dualRoot_F4_apply_three_eq_zero h.2⟩⟩
  have h2 := dualRoot_F4_apply_zero_eq_zero (γ := ReeTag.F4.dualRoot γ) h.2
  rw [ReeTag.dualRoot_dualRoot (t := .F4) hγ] at h2
  exact h2

theorem exists_sq_eq_charTwo {K : Type} [Field K] [Finite K] [CharP K 2] (c : K) :
    ∃ d : K, d ^ 2 = c :=
  Finite.surjective_of_injective (CharTwo.sq_injective (R := K)) c

section Levi


variable (K : Type) [Field K]

@[expose] noncomputable def B3Levi : Subgroup ↥(adjointGroup .F4 K) :=
  (rootSpan .F4 K b3LeviRoots).subgroupOf (adjointGroup .F4 K)

variable {K}

theorem mem_B3Levi_iff {g : adjointGroup .F4 K} :
    g ∈ B3Levi K ↔ (g : ModGL .F4 K) ∈ rootSpan .F4 K b3LeviRoots :=
  mem_subgroupOf


variable [Finite K] [CharP K ReeTag.F4.prime]

variable (K) in
noncomputable abbrev graphAutF4 : MulAut (adjointGroup .F4 K) := ReeTag.F4.finiteExceptionalAut K

theorem map_graphAutF4_C3Levi : (C3Levi K).map (graphAutF4 K).toMonoidHom = B3Levi K := by
  have : CharP K 2 := ‹_›
  rw [C3Levi, B3Levi, rootSpan_subgroupOf_eq_closure, rootSpan_subgroupOf_eq_closure,
    MonoidHom.map_closure]
  congr 1
  ext g
  constructor
  · rintro ⟨h, ⟨γ, hγ, c, hh⟩, rfl⟩
    have hh' : h = ⟨pinnedX .F4 K γ c, pinnedX_mem_adjointGroup γ c⟩ := Subtype.ext hh.symm
    subst hh'
    have hb := (dualRoot_mem_b3LeviRoots_iff hγ.1).2 hγ
    have hsl : γ ∈ ReeTag.F4.shortRoots ∪ ReeTag.F4.longRoots := by
      rw [ReeTag.shortRoots_union_longRoots]
      exact hγ.1
    rcases hsl with hs | hl
    · refine ⟨ReeTag.F4.dualRoot γ, hb, c ^ 2, ?_⟩
      have e := finiteExceptionalAut_pinnedX_short (K := K) hs c
      exact (congrArg Subtype.val e).symm
    · refine ⟨ReeTag.F4.dualRoot γ, hb, c, ?_⟩
      have e := finiteExceptionalAut_pinnedX_long (K := K) hl c
      exact (congrArg Subtype.val e).symm
  · rintro ⟨δ, hδ, c, hg⟩
    have hγroot : IsRoot .F4 (ReeTag.F4.dualRoot δ) := ReeTag.isRoot_dualRoot (t := .F4) hδ.1
    have hδγ : ReeTag.F4.dualRoot (ReeTag.F4.dualRoot δ) = δ :=
      ReeTag.dualRoot_dualRoot (t := .F4) hδ.1
    have hγ : ReeTag.F4.dualRoot δ ∈ c3LeviRoots :=
      (dualRoot_mem_b3LeviRoots_iff hγroot).1 (by rw [hδγ]; exact hδ)
    have hsl : ReeTag.F4.dualRoot δ ∈ ReeTag.F4.shortRoots ∪ ReeTag.F4.longRoots := by
      rw [ReeTag.shortRoots_union_longRoots]
      exact hγroot
    rcases hsl with hs | hl
    · obtain ⟨d, rfl⟩ := exists_sq_eq_charTwo c
      refine ⟨⟨pinnedX .F4 K (ReeTag.F4.dualRoot δ) d, pinnedX_mem_adjointGroup _ d⟩,
        ⟨_, hγ, d, rfl⟩, ?_⟩
      have e := finiteExceptionalAut_pinnedX_short (K := K) hs d
      refine e.trans (Subtype.ext ?_)
      change pinnedX .F4 K (ReeTag.F4.dualRoot (ReeTag.F4.dualRoot δ)) (d ^ 2) = (g : ModGL .F4 K)
      rw [hδγ, hg]
    · refine ⟨⟨pinnedX .F4 K (ReeTag.F4.dualRoot δ) c, pinnedX_mem_adjointGroup _ c⟩,
        ⟨_, hγ, c, rfl⟩, ?_⟩
      have e := finiteExceptionalAut_pinnedX_long (K := K) hl c
      refine e.trans (Subtype.ext ?_)
      change pinnedX .F4 K (ReeTag.F4.dualRoot (ReeTag.F4.dualRoot δ)) c = (g : ModGL .F4 K)
      rw [hδγ, hg]

variable (K) in
@[expose] noncomputable def c3LeviEquivB3Levi : ↥(C3Levi K) ≃* ↥(B3Levi K) :=
  ((graphAutF4 K).subgroupMap (C3Levi K)).trans (MulEquiv.subgroupCongr map_graphAutF4_C3Levi)

theorem coe_c3LeviEquivB3Levi (g : C3Levi K) :
    ((c3LeviEquivB3Levi K g : B3Levi K) : adjointGroup .F4 K) = graphAutF4 K g :=
  rfl

end Levi

section Main


variable {K : Type} [Field K]

noncomputable def b3LeviEquiv [Finite K] [CharP K 2] : ↥(StatedSp 3 K) ≃* ↥(B3Levi K) :=
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  (c3LeviEquiv K).trans (c3LeviEquivB3Levi K)

theorem center_B3Levi_eq_bot [Finite K] [CharP K 2] : center (B3Levi K) = ⊥ := by
  rw [← map_center_eq (b3LeviEquiv (K := K)), center_statedSp_eq_bot, Subgroup.map_bot]

theorem isQuasisimple_B3Levi [Finite K] [CharP K 2] : CFSG.IsQuasisimple (B3Levi K) :=
  Unitary.isQuasisimple_of_mulEquiv (b3LeviEquiv (K := K))
    (Symplectic.isQuasisimple 3 K (by norm_num) sp6_field_condition)

theorem isSimpleGroup_B3Levi [Finite K] [CharP K 2] : IsSimpleGroup (B3Levi K) := by
  have : IsSimpleGroup (B3Levi K ⧸ center (B3Levi K)) := (isQuasisimple_B3Levi (K := K)).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq center_B3Levi_eq_bot).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem isQuasisimple_open_B3Levi [Finite K] [CharP K 2] : CFSG.Open.IsQuasisimple (B3Levi K) :=
  ⟨(isQuasisimple_B3Levi (K := K)).1.commutator_eq_top, (isQuasisimple_B3Levi (K := K)).2.1⟩

variable {f : ℕ}

theorem B3Levi_mulEquiv (hK : Nat.card K = 2 ^ f) :
    Nonempty (↥(B3Levi K) ≃* (lieUniversal .PSp 3 2 f Nat.prime_two).K) := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨e⟩ := C3Levi_mulEquiv (K := K) hK
  exact ⟨(c3LeviEquivB3Levi K).symm.trans e⟩

theorem lieModel_B3Levi (hK : Nat.card K = 2 ^ f) :
    CFSG.Blueprint.LieModel (B3Levi K) .PSp 3 2 f := by
  have := finite_of_natCard_eq_two_pow hK
  have := charP_two_of_natCard_eq_two_pow hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  exact CurtisTits.lieModel_of_mulEquiv (c3LeviEquivB3Levi K) (lieModel_C3Levi hK)

end Main

end CFSG.SeitzReduction.F4Pilot
