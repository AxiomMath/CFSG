module

public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3WOdd3
public import CFSG.ClassicalInvolution.Q3.Q3PPBal
public import CFSG.ClassicalInvolution.Q3.Q3PPShapeCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3PP

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Q3.Q3OF
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Q3.Q3W

section Hyps

variable {G : Type} [Group G]

@[expose] def TwinFreeAt (Ω : Set (Subgroup G)) (K₀ : Subgroup G) (z₀ : G) : Prop :=
  ∀ M ∈ Ω, ∀ m : G, IsClassicalMember3 M m → m = z₀ → M = K₀

@[expose] def NonClassicalAt (Ω : Set (Subgroup G)) (x : G) : Prop :=
  ∀ M ∈ Ω, ∀ m : G, IsClassicalMember3 M m → m ≠ x

end Hyps

section Center

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {ι : Type}

theorem ubar_mem_center_at_self {z₀ : G} (hu' : z₀ ∈ locLayer Ω z₀) :
    QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω z₀)) ⟨z₀, hu'⟩ ∈
      Subgroup.center (locQuot Ω z₀) := by
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have hy : (y : G) * z₀ = z₀ * (y : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp (centralizingLayer_le_centralizer Ω {z₀} y.2)
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext hy

theorem kind_eq_sl23_of_ubar_central
    {x : G} (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {K : Subgroup G} {u : G}
    (hK : K ∈ centralizingMembers Ω {x}) (hu : IsClassicalMember3 K u) (hu' : u ∈ locLayer Ω x)
    (hcen : QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩ ∈
      Subgroup.center (locQuot Ω x)) (i : ι) (hi : locImg Ω x K ≤ (D.hom i).range) :
    D.kind i = CompData.sl23 := by
  by_contra hne
  have hKY : K ≤ locLayer Ω x := le_centralizingLayer hK
  have hcl : IsClassicalMember3 (locImg Ω x K)
      (QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩) :=
    (hu.subgroupOf hKY).map_oddQuotient
  have h1 := locImg_le_normalClosure_of_nonA1 D hK hu i hi hne hu'
  have h2 : Subgroup.normalClosure
      ({QuotientGroup.mk' (classicalInvolutionOddCore ↥(locLayer Ω x)) ⟨u, hu'⟩} :
        Set (locQuot Ω x)) ≤ Subgroup.center (locQuot Ω x) :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hcen)
  exact hcl.not_le_center (h1.trans h2)

end Center

section TwoComponents

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K : Subgroup G} {z : G}
  {K₁ K₂ : Subgroup G} {z₁ z₂ : G} {ι : Type}

namespace EdgeData

theorem not_isA1Comp3_of_two_components (hR : RouteD3Setup K z)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h : EdgeData K K₁ K₂ z₁ z₂) [Finite ι]
    (D : LieSystemData3 ι (locQuot (conjClass3 K) z₁) (locFamily (conjClass3 K) z₁))
    {i₁ i₂ : ι} (hA1 : D.kind i₁ = CompData.sl23) (hcover : ∀ j, j = i₁ ∨ j = i₂) :
    D.kind i₂ ≠ CompData.sl23 := by
  intro h2
  have hR₁ : RouteD3Setup K₁ z₁ := Q3TC.RouteD3Setup.of_mem_conjClass3 hR h.mem₁ h.cls₁
  have hcl : conjClass3 K₁ = conjClass3 K := Q3TC.conjClass3_eq_of_mem h.mem₁
  have hO3 : LocalOddThreeFree3 (conjClass3 K₁) z₁ :=
    Q3W.oddThreeFreeInput_proved G K₁ z₁ hR₁
  have hpos : 0 < Nat.card ι := by
    have : Nonempty ι := ⟨i₁⟩
    exact Nat.card_pos
  have hshape : LocalShapeC3 (Nat.card ι - 1) CompData.sl23 (conjClass3 K) z₁ :=
    ⟨ι, inferInstance, D, by omega, i₁, hA1, fun i hi => by
      rcases hcover i with rfl | rfl
      · exact absurd rfl hi
      · exact h2⟩
  rw [← hcl] at hshape
  exact false_of_all_a1_3 hnab hR₁ hO3 hshape

end EdgeData

end TwoComponents

end CFSG.ClassicalInvolution.Q3.Q3PP
