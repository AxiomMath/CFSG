module

public import CFSG.ClassicalInvolution.RouteD.MultiStarComp
public import CFSG.ClassicalInvolution.RouteD.ExoticTwin

public section

namespace CFSG.ClassicalInvolution.RouteD.TWR

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.CoreAssembly
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.RouteD.Exotic
open scoped commutatorElement

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

@[expose] def isoMembers (Ω : Set (Subgroup G)) (x : G) : Set (Subgroup G) :=
  {M | M ∈ centralizingMembers Ω {x} ∧ ∀ N ∈ centralizingMembers Ω {x}, N ≠ M → Commutes M N}

structure OneBig {Ω : Set (Subgroup G)} {x : G}
    (D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)) (i₁ : Fin D.card) : Prop where
  big : ¬ IsA1Comp D i₁
  rest : ∀ i, i ≠ i₁ → IsA1Comp D i

variable {Ω : Set (Subgroup G)} {x : G}

theorem exists_noncommuting_of_not_a1 [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card} (hi : ¬ IsA1Comp D i) {M : Subgroup G} (hM : M ∈ compMembers Ω x D i) :
    ∃ L ∈ centralizingMembers Ω {x}, L ≠ M ∧ ¬ Commutes M L := by
  obtain ⟨N, N', hN, hN', hNN'⟩ := exists_ne_of_not_isA1Comp hΩ hex hi
  by_contra hall
  push Not at hall
  have hblock : ∀ B, Linked Ω x M B → B = M := by
    intro B hB
    induction hB with
    | refl => rfl
    | @tail b c _ hbc ih =>
      rw [ih] at hbc
      by_contra hcM
      exact hbc.2.2 (hall c hbc.2.1 hcM)
  have hN_M : N = M := hblock N ((linked_iff_mem_compMembers hΩ hex hP1 hM).mpr hN)
  have hN'_M : N' = M := hblock N' ((linked_iff_mem_compMembers hΩ hex hP1 hM).mpr hN')
  exact hNN' (hN_M.trans hN'_M.symm)

theorem mem_isoMembers_of_a1 [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω)
    (hP1 : LocalOddCentral Ω {x}) {D : LieSystemData p f (locQuot Ω x) (locFamily Ω x)}
    {i : Fin D.card} (hi : IsA1Comp D i) {M : Subgroup G} (hM : M ∈ compMembers Ω x D i) :
    M ∈ isoMembers Ω x := by
  refine ⟨hM.1, fun N hN hNM => ?_⟩
  have hwhole : locImg Ω x M = (D.hom i).range := locImg_eq_range_of_le_a1 hΩ hex D hM.1 hi hM.2
  exact (commutes_or_eq_of_whole hΩ hex hP1 D hM.1 hN hwhole).resolve_right hNM

end CFSG.ClassicalInvolution.RouteD.TWR
