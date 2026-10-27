module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E4
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888E5a

public section

open Subgroup
open scoped Classical

namespace CFSG.OddStandard.SmallF3.Omega

variable {X : Type} [Group X] {V : Subgroup X} {W : Fin 4 → Subgroup X}

open scoped Classical in
@[expose] noncomputable def mval (hS : PlaneSys V W) (y : normalizer (V : Set X)) : ℕ :=
  (Finset.univ.filter fun i : Fin 4 => planeHom hS y i ≠ i).card +
    (Finset.univ.filter fun i : Fin 4 => planeHom hS y i = i ∧ ActsNontriv (W i) (y : X)).card

open scoped Classical in
private noncomputable def s888XM_fixedSet (hS : PlaneSys V W) (y : normalizer (V : Set X))
    (i : Fin 4) : Set ↥(W i) :=
  if planeHom hS y i = i then
    {w : ↥(W i) | (y : X) * (w : X) * (y : X)⁻¹ = w}
  else Set.univ

private theorem s888XM_fixedSet_card (hS : PlaneSys V W) (y : normalizer (V : Set X))
    (hy2 : ∀ v ∈ V, (y : X) * (y : X) * v * ((y : X) * (y : X))⁻¹ = v) (i : Fin 4) :
    Nat.card ↥(s888XM_fixedSet hS y i) =
      if planeHom hS y i = i then (if ActsNontriv (W i) (y : X) then 2 else 4) else 4 := by
  classical
  by_cases hπ : planeHom hS y i = i
  · rw [s888XM_fixedSet]
    simp only [if_pos hπ]
    by_cases hn : ActsNontriv (W i) (y : X)
    · simp only [if_pos hn]
      refine card_fixed_of_actsNontriv (hS.card i) (fun a ha => hS.sq a (hS.le i ha)) ?_ hn
      exact ⟨fun a ha => (mem_plane_conj_iff hS y hπ a).mpr ha,
        fun a ha => hy2 a (hS.le i ha)⟩
    · simp only [if_neg hn]
      have hset : ({w : ↥(W i) | (y : X) * (w : X) * (y : X)⁻¹ = w} : Set ↥(W i)) =
          Set.univ := by
        ext w
        simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
        exact not_actsNontriv_iff.mp hn (w : X) w.2
      rw [hset, Nat.card_congr (Equiv.Set.univ (↥(W i)))]
      exact hS.card i
  · rw [s888XM_fixedSet]
    simp only [if_neg hπ]
    rw [Nat.card_congr (Equiv.Set.univ (↥(W i)))]
    exact hS.card i

private lemma s888XM_count :
    ∀ π : Equiv.Perm (Fin 4), π * π = 1 → ∀ s : Fin 4 → Bool,
      (∏ i ∈ Finset.univ.filter (fun i : Fin 4 => i ≤ π i),
          (if π i = i then (if s i = true then 2 else 4) else 4)) =
        2 ^ (8 - ((Finset.univ.filter fun i : Fin 4 => π i ≠ i).card +
          (Finset.univ.filter fun i : Fin 4 => π i = i ∧ s i = true).card)) := by
  decide +kernel

theorem card_centralizer_le_mval (hS : PlaneSys V W) (y : normalizer (V : Set X))
    (hy2 : ∀ v ∈ V, (y : X) * (y : X) * v * ((y : X) * (y : X))⁻¹ = v) :
    Nat.card {v : V // (y : X) * (v : X) * (y : X)⁻¹ = v} ≤ 2 ^ (8 - mval hS y) := by
  classical
  have hππ : planeHom hS y * planeHom hS y = 1 := by
    rw [← map_mul]
    exact planeHom_eq_one_of_centralizes hS (y * y) hy2
  let M : Finset (Fin 4) := Finset.univ.filter fun i => i ≤ planeHom hS y i
  let Φ : {v : V // (y : X) * (v : X) * (y : X)⁻¹ = v} →
      (i : ↥M) → ↥(s888XM_fixedSet hS y i.val) :=
    fun v i => ⟨⟨comp hS (v : V) i.val, comp_mem hS (v : V) i.val⟩, by
      rw [s888XM_fixedSet]
      by_cases hfix : planeHom hS y i.val = i.val
      · rw [if_pos hfix]
        have hcf := comp_fixed hS (v : V) y v.2 i.val
        rw [hfix] at hcf
        exact hcf.symm
      · rw [if_neg hfix]
        exact Set.mem_univ _⟩
  have hΦinj : Function.Injective Φ := by
    intro v v' h
    apply Subtype.ext
    apply comp_injective hS
    funext j
    by_cases hj : j ∈ M
    · have h2 := congrFun h (⟨j, hj⟩ : ↥M)
      exact congrArg (fun x : ↥(s888XM_fixedSet hS y j) => (x.1.1 : X)) h2
    · have hnotle : ¬ j ≤ planeHom hS y j := by
        intro hle
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hle⟩)
      have hlt : planeHom hS y j < j := lt_of_not_ge hnotle
      have hππj : planeHom hS y (planeHom hS y j) = j := by
        have hh := congrArg (fun p : Equiv.Perm (Fin 4) => p j) hππ
        simpa using hh
      have hiM : planeHom hS y j ∈ M := by
        change planeHom hS y j ∈ Finset.univ.filter (fun i : Fin 4 => i ≤ planeHom hS y i)
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hππj]; exact le_of_lt hlt⟩
      have h2 := congrFun h (⟨planeHom hS y j, hiM⟩ : ↥M)
      have hvi : comp hS (v : V) (planeHom hS y j) =
          comp hS (v' : V) (planeHom hS y j) :=
        congrArg (fun x : ↥(s888XM_fixedSet hS y (planeHom hS y j)) => (x.1.1 : X)) h2
      have hcf := comp_fixed hS (v : V) y v.2 (planeHom hS y j)
      rw [hππj] at hcf
      have hcf' := comp_fixed hS (v' : V) y v'.2 (planeHom hS y j)
      rw [hππj] at hcf'
      rw [hcf, hvi, ← hcf']
  haveI : Finite (∀ i : ↥M, ↥(s888XM_fixedSet hS y i.val)) := by
    apply Nat.finite_of_card_ne_zero
    rw [Nat.card_pi]
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    rw [s888XM_fixedSet_card hS y hy2 i.val]
    by_cases h1 : planeHom hS y i.val = i.val
    · rw [if_pos h1]
      by_cases h2 : ActsNontriv (W i.val) (y : X)
      · rw [if_pos h2]; decide
      · rw [if_neg h2]; decide
    · rw [if_neg h1]; decide
  have hle := Nat.card_le_card_of_injective Φ hΦinj
  rw [Nat.card_pi] at hle
  have hprod : (∏ i : ↥M, Nat.card ↥(s888XM_fixedSet hS y i.val)) = 2 ^ (8 - mval hS y) := by
    rw [Finset.prod_coe_sort (s := M)
      (f := fun i : Fin 4 => Nat.card ↥(s888XM_fixedSet hS y i))]
    rw [Finset.prod_congr rfl (fun i _ => s888XM_fixedSet_card hS y hy2 i)]
    have hcount := s888XM_count (planeHom hS y) hππ (fun i => decide (ActsNontriv (W i) (y : X)))
    simp only [decide_eq_true_iff] at hcount
    change (∏ i ∈ Finset.univ.filter (fun i : Fin 4 => i ≤ planeHom hS y i),
        (if planeHom hS y i = i then
          (if ActsNontriv (W i) (y : X) then 2 else 4) else 4)) =
      2 ^ (8 - mval hS y)
    rw [hcount]
    have hmval : mval hS y =
        (Finset.univ.filter fun i : Fin 4 => planeHom hS y i ≠ i).card +
          (Finset.univ.filter fun i : Fin 4 =>
            planeHom hS y i = i ∧ ActsNontriv (W i) (y : X)).card := by
      unfold mval
      rfl
    rw [← hmval]
  rw [hprod] at hle
  exact hle

end CFSG.OddStandard.SmallF3.Omega
