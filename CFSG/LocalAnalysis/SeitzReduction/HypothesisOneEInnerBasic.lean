module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneEInnerRoots
public import CFSG.LocalAnalysis.SeitzReduction.LongRootPairs
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootOps
open scoped commutatorElement

theorem pinnedX_single_mem_posUnipotent
    {τ : Tag} {K : Type} [Field K] (j : Fin τ.rank) (c : K) :
    pinnedX τ K (Pi.single j 1) c ∈ posUnipotent τ K :=
  rootSubgroup_le_posUnipotent_of_height_pos (isRoot_single τ j) (by rw [height_single]; omega)
    (mem_rootSubgroup.2 ⟨c, rfl⟩)


variable {τ : Tag} {K : Type} [Field K]

theorem commutator_simple_mem_and_rootCoord (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    {γ : Fin τ.rank → ℤ} {j : Fin τ.rank} (hj : coPair τ j γ = -1)
    (hγ' : IsRoot τ (γ + Pi.single j 1) ∧ 0 < height (γ + Pi.single j 1))
    {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) (hδpos : 0 < height δ) (hht : height γ ≤ height δ)
    (c : K) :
    ⁅pinnedX τ K δ c, pinnedX τ K (Pi.single j 1) 1⁆ ∈
        heightSeries τ K (height (γ + Pi.single j 1)) ∧
      rootCoord hγ' ⁅pinnedX τ K δ c, pinnedX τ K (Pi.single j 1) 1⁆ =
        if δ = γ then (commConst τ γ (Pi.single j 1) (1, 1) : K) * c else 0 := by
  have hej := isRoot_single τ j
  have hht' : height (γ + Pi.single j 1) = height γ + 1 := by rw [height_add, height_single]
  have hmem : ⁅pinnedX τ K δ c, pinnedX τ K (Pi.single j 1) 1⁆ ∈
      heightSeries τ K (height (γ + Pi.single j 1)) := by
    rw [hht', ← commutatorElement_inv]
    exact inv_mem (commutator_posUnipotent_heightSeries_le _ (commutator_mem_commutator
      (pinnedX_single_mem_posUnipotent j 1)
      (pinnedX_mem_rootSpan (S := {β | IsRoot τ β ∧ 0 < height β ∧ height γ ≤ height β})
        ⟨hδ, hδpos, hht⟩ c)))
  refine ⟨hmem, ?_⟩
  by_cases hδj : δ = Pi.single j 1
  · subst hδj
    have hne : (Pi.single j 1 : Fin τ.rank → ℤ) ≠ γ := by
      intro h
      have h2 : coPair τ j (Pi.single j 1) = 2 := by
        rw [coPair, Finset.sum_eq_single j (fun l _ hl => by simp [hl])
          (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one, Tag.cartan_self]
      rw [h, hj] at h2
      omega
    rw [ite_eq_right hne, commutatorElement_eq_one_iff_mul_comm.2
      (by rw [← pinnedX_add, ← pinnedX_add, add_comm]), rootCoord_one]
  have hδj' : δ ≠ -Pi.single j 1 := by
    intro h
    have : height δ = -1 := by
      rw [h, height_neg, height_single]
    omega
  obtain ⟨hroot, hnroot⟩ := simply_laced_root_commutator_unit τ (Or.inr hτ) hδ hej hδj hδj'
  by_cases hsum : IsRoot τ (δ + Pi.single j 1)
  · rw [(hroot hsum).2 K c 1, mul_one]
    by_cases hδγ : δ = γ
    · subst hδγ
      rw [ite_eq_left rfl, rootCoord_self]
    · rw [ite_eq_right hδγ]
      refine rootCoord_pinnedX_of_ne hγ' ⟨hsum, by rw [height_add, height_single]; omega⟩
        (by rw [height_add, height_add]; omega) (fun h => hδγ (add_right_cancel h)) _
  · have hc := hnroot hsum K _ (mem_rootSubgroup.2 ⟨c, rfl⟩) _ (mem_rootSubgroup.2 ⟨1, rfl⟩)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc.eq, rootCoord_one,
      ite_eq_right (by rintro rfl; exact hsum hγ'.1)]

theorem mem_rootSubgroup_highRoot_of_commute_simple (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    [Finite K] {z : ModGL τ K} (hz : z ∈ posUnipotent τ K)
    (hc : ∀ j : Fin τ.rank,
      z * pinnedX τ K (Pi.single j 1) 1 = pinnedX τ K (Pi.single j 1) 1 * z) :
    z ∈ rootSubgroup τ K (highRoot τ) := by
  classical
  obtain ⟨α, hα, hrange⟩ := exists_rootEnum (finite_of_forall_isRoot_pos (τ := τ)
    (S := {β | IsRoot τ β ∧ 0 < height β}) fun β hβ => hβ)
  have hpos : ∀ l, IsRoot τ (α l) ∧ 0 < height (α l) := fun l => by
    have h : α l ∈ Set.range α := ⟨l, rfl⟩
    rwa [hrange] at h
  obtain ⟨c, -, hcz⟩ := ((positive_root_collection τ K).2 α hα hrange).2.2 hz
  have hcz' : (List.ofFn fun l => pinnedX τ K (α l) (c l)).prod = z := hcz
  have key : ∀ n : ℕ, ∀ l, height (α l) ≤ n → α l ≠ highRoot τ → c l = 0 := by
    intro n
    induction n with
    | zero =>
      intro l hl _
      have := (hpos l).2
      push_cast at hl
      omega
    | succ n ih =>
      intro i hi hir
      by_cases hle : height (α i) ≤ n
      · exact ih i hle hir
      obtain ⟨j, hj, hγ'⟩ := exists_isRoot_add_single hτ (hpos i).1 (hpos i).2 hir
      have hht' : height (α i + Pi.single j 1) = height (α i) + 1 := by
        rw [height_add, height_single]
      have hγ'p : IsRoot τ (α i + Pi.single j 1) ∧ 0 < height (α i + Pi.single j 1) :=
        ⟨hγ', by have := (hpos i).2; omega⟩
      have hlow : ∀ l, height (α l) < height (α i) → c l = 0 := fun l hl => ih l (by
        push_cast at hi
        omega) fun h => by
          have h1 := height_le_height_highRoot hγ'
          rw [← h] at h1
          omega
      set w := pinnedX τ K (Pi.single j 1) (1 : K) with hw_def
      have hfac : ∀ l, ⁅pinnedX τ K (α l) (c l), w⁆ ∈
            heightSeries τ K (height (α i + Pi.single j 1)) ∧
          rootCoord hγ'p ⁅pinnedX τ K (α l) (c l), w⁆ =
            if l = i then (commConst τ (α i) (Pi.single j 1) (1, 1) : K) * c i else 0 := by
        intro l
        by_cases hl : height (α l) < height (α i)
        · rw [hlow l hl, pinnedX_zero, commutatorElement_one_left, rootCoord_one,
            ite_eq_right (fun h => by subst h; exact lt_irrefl _ hl)]
          exact ⟨one_mem _, rfl⟩
        · obtain ⟨h1, h2⟩ := commutator_simple_mem_and_rootCoord hτ hj hγ'p (hpos l).1
            (hpos l).2 (not_lt.1 hl) (c l)
          refine ⟨h1, h2.trans ?_⟩
          by_cases hli : l = i
          · subst hli
            simp
          · rw [ite_eq_right (fun h => hli (hα h)), ite_eq_right hli]
      obtain ⟨-, hπ⟩ := commutator_prod_mem_and_coord (U := posUnipotent τ K)
        (M := heightSeries τ K (height (α i + Pi.single j 1)))
        (heightSeries_le_normalizer K _) (rootCoord hγ'p)
        (fun x hx y hy => rootCoord_mul hγ'p hx hy) (fun g hg x hx => rootCoord_conj hγ'p hg hx)
        (List.ofFn fun l => pinnedX τ K (α l) (c l)) [w]
        (fun x hx => by
          obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
          exact rootSubgroup_le_posUnipotent_of_height_pos (hpos l).1 (hpos l).2
            (mem_rootSubgroup.2 ⟨_, rfl⟩))
        (fun y hy => by
          rw [List.mem_singleton] at hy
          rw [hy]
          exact pinnedX_single_mem_posUnipotent j 1)
        (fun x hx y hy => by
          rw [List.mem_singleton] at hy
          obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
          rw [hy]
          exact (hfac l).1)
      rw [hcz', List.prod_singleton, commutatorElement_eq_one_iff_mul_comm.2 (hc j),
        rootCoord_one, List.map_ofFn, List.sum_ofFn] at hπ
      simp only [Function.comp_apply, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero, (hfac _).2, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hπ
      obtain ⟨hε, -⟩ := (simply_laced_root_commutator_unit.{0} τ (Or.inr hτ) (hpos i).1
        (isRoot_single τ j) (fun h => by
          have h2 : coPair τ j (Pi.single j 1) = 2 := by
            rw [coPair, Finset.sum_eq_single j (fun l _ hl => by simp [hl])
              (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one,
              Tag.cartan_self]
          rw [← h, hj] at h2
          omega) (fun h => by
          have h1 := (hpos i).2
          rw [h, height_neg, height_single] at h1
          omega)).1 hγ'
      rcases hε with hε | hε
      · rw [hε] at hπ
        simpa using hπ.symm
      · rw [hε] at hπ
        simpa using hπ.symm
  rw [← hcz']
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx
  by_cases hl : α l = highRoot τ
  · rw [hl]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  · rw [key (height (α l)).toNat l (Int.self_le_toNat _) hl, pinnedX_zero]
    exact one_mem _

theorem sq_eq_one_of_commute_posUnipotent_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K]
    [CharP K 2] {z : ModGL τ K} (hz : z ∈ posUnipotent τ K)
    (hc : ∀ u ∈ posUnipotent τ K, z * u = u * z) : z ^ 2 = 1 := by
  obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 (mem_rootSubgroup_highRoot_of_commute_simple hτ hz
    fun j => hc _ (pinnedX_single_mem_posUnipotent j 1))
  rw [sq, ← pinnedX_add, CharTwo.add_self_eq_zero, pinnedX_zero]

end CFSG.SeitzReduction
