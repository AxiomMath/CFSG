module

public import CFSG.LocalAnalysis.EvenSmallLie.SympSix.CoverUniqueCheck
public import CFSG.Certificates.Kernel.Misc.Coset.PG
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition

public section

namespace CFSG.EvenSmallLie.SympSix

open Subgroup CFSG.CosetTable CFSG.LieType.Multipliers CFSG.RankThree.PerfectCover
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3 CFSG.EvenSmallLie.Sp6

theorem model_facts : (∀ r ∈ rels, wordPerm r = 1) ∧
    (∀ i, wordPerm (commWords (coverPairs i)) = sympGen i) ∧ wordPerm wordSB = sp6B := by
  have h := model_check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, fun i => h.1.2 i (List.mem_finRange i), h.2⟩

theorem lift_sympGen_mk (w : List (Fin 3 × Bool)) :
    FreeGroup.lift sympGen (FreeGroup.mk w) = wordPerm w :=
  FreeGroup.lift_mk

theorem sympGen_mem
    (i : Fin 3) : sympGen i ∈ co3X36 := by
  rw [← sp6Q_originalSubgroup]
  fin_cases i
  · change tab _ ∈ _
    rw [tab_eq]
    exact evalCodes_mem _ sp6Gens_mem _
  · change tab _ ∈ _
    rw [tab_eq]
    exact evalCodes_mem _ sp6Gens_mem _
  · exact sp6Gens_mem _ (List.mem_cons_self ..)

@[expose] def sympGenX
    (i : Fin 3) : co3X36 := ⟨sympGen i, sympGen_mem i⟩

theorem coe_lift_sympGenX
    (x : FreeGroup (Fin 3)) :
    ((FreeGroup.lift sympGenX x : co3X36) : Equiv.Perm (Fin 36)) = FreeGroup.lift sympGen x := by
  have h : co3X36.subtype.comp (FreeGroup.lift sympGenX) = FreeGroup.lift sympGen :=
    FreeGroup.ext_hom _ _ fun i => by simp [sympGenX]
  exact DFunLike.congr_fun h x

theorem lift_commWords
    (i : Fin 3) :
    FreeGroup.lift sympGenX (FreeGroup.mk (commWords (coverPairs i))) = sympGenX i :=
  Subtype.ext ((coe_lift_sympGenX _).trans ((lift_sympGen_mk _).trans (model_facts.2.1 i)))

theorem closure_sympGenX :
    closure (Set.range sympGenX) = ⊤ := by
  have hmap : (closure (Set.range sympGenX)).map co3X36.subtype = closure (Set.range sympGen) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]
    rfl
  have hle : co3X36 ≤ (closure (Set.range sympGenX)).map co3X36.subtype := by
    rw [hmap, ← sp6Q_originalSubgroup, sp6Q, certificate_originalSubgroup, closure_le]
    intro g hg
    rcases List.mem_pair.1 hg with rfl | rfl
    · exact subset_closure ⟨2, rfl⟩
    · rw [← model_facts.2.2, ← lift_sympGen_mk, ← FreeGroup.range_lift_eq_closure]
      exact ⟨_, rfl⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, hy, hyx⟩ := hle x.2
  rwa [show y = x from Subtype.ext hyx] at hy

theorem card_PG_rels
    : Finite (PG 3 rels) ∧ Nat.card (PG 3 rels) ≤ 1451520 := by
  obtain ⟨fY, cY⟩ := CFSG.KC.MiscCoset.card_le_of_zpowers_index relsY [(1, true)] (k := 5)
    (by norm_num) (by decide) presY_check
  have : Finite (PG (subsetOf 3 [0, 1]).length (restrictWords (subsetOf 3 [0, 1]) rels)) := fY
  obtain ⟨f, c⟩ := card_le_of_genSub_index rels _ pres_check.1 pres_check.2
  exact ⟨f, c.trans ((Nat.mul_le_mul_left 56 cY).trans (by norm_num))⟩

theorem isPresentation_co3X36 :
    IsPresentation sympGenX (wordSet rels) := by
  obtain ⟨hfin, hcard⟩ := card_PG_rels
  refine IsPresentation.of_card_le ?_ closure_sympGenX ?_
  · intro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
    exact Subtype.ext ((coe_lift_sympGenX _).trans ((lift_sympGen_mk w).trans (model_facts.1 w hw)))
  · rw [card_co3X36]
    exact hcard

theorem card_cover₁
    : Finite (PG 2 cover₁) ∧ Nat.card (PG 2 cover₁) ≤ 51840 :=
  cover₁_check

theorem card_cover_le
    : Finite (PG 3 coverWs) ∧ Nat.card (PG 3 coverWs) ≤ 2 * 1451520 := by
  obtain ⟨f₁, c₁⟩ := card_cover₁
  have : Finite (PG (subsetOf 3 [0, 1]).length (restrictWords (subsetOf 3 [0, 1]) coverWs)) := f₁
  obtain ⟨f, c⟩ := card_le_of_genSub_index coverWs _ cover_check.1 cover_check.2
  exact ⟨f, c.trans ((Nat.mul_le_mul_left 56 c₁).trans (by norm_num))⟩

theorem card_of_lieModel
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1) :
    Nat.card X = 1451520 := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hX
  rw [Nat.card_congr e.toEquiv, card_co3X36]

theorem perfect_and_hopfCover_card_le
    {X : Type} [Group X]
    (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1) :
    Group.IsPerfect X ∧ Finite (HopfCover X) ∧ Nat.card (HopfCover X) ≤ 2 * Nat.card X := by
  obtain ⟨e⟩ := nonempty_mulEquiv_co3X36 hX
  have hP : IsPresentation (fun i => e.symm (sympGenX i)) (wordSet rels) :=
    isPresentation_co3X36.mulEquiv e.symm
  have hw : ∀ i, FreeGroup.mk (commWords (coverPairs i)) ∈ commutator (FreeGroup (Fin 3)) :=
    fun i => mk_commWords_mem_commutator _
  have hwg : ∀ i, FreeGroup.lift (fun i => e.symm (sympGenX i))
      (FreeGroup.mk (commWords (coverPairs i))) = e.symm (sympGenX i) := fun i => by
    rw [lift_mulEquiv, lift_commWords]
  have hS : coverRelators (wordSet rels) (fun i => FreeGroup.mk (commWords (coverPairs i))) =
      wordSet coverWs := coverRelators_wordSet rels _
  obtain ⟨hfin, hle⟩ := card_cover_le
  have hfinP : Finite (PresentedCover (wordSet rels)
      fun i => FreeGroup.mk (commWords (coverPairs i))) := by
    rw [PresentedCover, hS]
    exact hfin
  have hcardP : Nat.card (PresentedCover (wordSet rels)
      fun i => FreeGroup.mk (commWords (coverPairs i))) ≤ 2 * Nat.card X := by
    rw [PresentedCover, hS, card_of_lieModel hX]
    exact hle
  let φ := presentedCoverEquiv hP hw hwg
  exact ⟨isPerfect_of_isPresentation hP hw hwg, Finite.of_equiv _ φ.toEquiv,
    (Nat.card_congr φ.toEquiv).symm.le.trans hcardP⟩

theorem hopfLift_bijective
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1)
    {E : Type*} [Group E] [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) (h2 : Nat.card q.ker = 2) :
    Function.Bijective (hopfLift q hq hker) := by
  obtain ⟨-, hfin, hle⟩ := perfect_and_hopfCover_card_le hX
  have hE : Nat.card E = 2 * Nat.card X := by
    rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv, h2, mul_comm]
  exact (hopfLift_surjective q hq hker).bijective_of_nat_card_le (hle.trans hE.ge)

theorem card_ker_le_two
    {X : Type} [Group X] (hX : CFSG.Blueprint.LieModel X .PSp 3 2 1)
    {E : Type*} [Group E] [Group.IsPerfect E] (q : E →* X) (hq : Function.Surjective q)
    (hker : q.ker ≤ center E) : Nat.card q.ker ≤ 2 := by
  obtain ⟨-, hfin, hle⟩ := perfect_and_hopfCover_card_le hX
  have hE := Nat.card_le_card_of_surjective _ (hopfLift_surjective q hq hker)
  rw [q.ker.card_eq_card_quotient_mul_card_subgroup,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv] at hE
  have hX' := card_of_lieModel hX
  rw [hX'] at hE hle
  omega

end CFSG.EvenSmallLie.SympSix
