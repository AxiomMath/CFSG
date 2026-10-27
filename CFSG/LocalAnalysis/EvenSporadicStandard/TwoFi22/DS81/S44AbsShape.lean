module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.S44AbsOrbit
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Abs

open Subgroup MulAction

variable {V : Type} [CommGroup V] {X M : Subgroup (MulAut V)} {t : V} {O : Fin 5 → Set V}

theorem shape_arith (p : Fin 5 → Prop) [DecidablePred p] (h01 : p 0 ↔ p 1)
    (hex : ∃ i, p i)
    (hdvd : ((∑ i, if p i then ![22, 22, 231, 231, 1540] i else 0) + 1) * 887040 ∣
      2 ^ 55 * 3 ^ 6 * 5 ^ 2 * 7 ^ 3 * 11 * 17 * 23 * 31 ^ 2 * 73 * 89 * 127) :
    ((∑ i, if p i then ![22, 22, 231, 231, 1540] i else 0) = 44 ∧
        p 0 ∧ p 1 ∧ ¬ p 2 ∧ ¬ p 3 ∧ ¬ p 4) ∨
    ((∑ i, if p i then ![22, 22, 231, 231, 1540] i else 0) = 275 ∧
        p 0 ∧ p 1 ∧ ¬ p 4 ∧ (p 2 ∧ ¬ p 3 ∨ ¬ p 2 ∧ p 3)) ∨
    ((∑ i, if p i then ![22, 22, 231, 231, 1540] i else 0) = 2046 ∧
        p 0 ∧ p 1 ∧ p 2 ∧ p 3 ∧ p 4) := by
  have hex' : p 0 ∨ p 1 ∨ p 2 ∨ p 3 ∨ p 4 := by
    obtain ⟨i, hi⟩ := hex
    match i, hi with
    | 0, hi => exact Or.inl hi
    | 1, hi => exact Or.inr (Or.inl hi)
    | 2, hi => exact Or.inr (Or.inr (Or.inl hi))
    | 3, hi => exact Or.inr (Or.inr (Or.inr (Or.inl hi)))
    | 4, hi => exact Or.inr (Or.inr (Or.inr (Or.inr hi)))
  rw [Fin.sum_univ_five] at hdvd ⊢
  by_cases h0 : p 0 <;> by_cases h1 : p 1 <;> by_cases h2 : p 2 <;> by_cases h3 : p 3 <;>
    by_cases h4 : p 4 <;> simp [h0, h1, h2, h3, h4] at hdvd h01 hex' ⊢

theorem arith_rest (p q : Fin 5 → Prop) [DecidablePred q]
    (hp : p 0 ∧ p 1 ∧ ¬ p 4 ∧ (p 2 ∧ ¬ p 3 ∨ ¬ p 2 ∧ p 3))
    (hpq : ∀ i, q i → ¬ p i)
    (hpos : 0 < ∑ i, if q i then ![22, 22, 231, 231, 1540] i else 0)
    (h23 : 23 ∣ ∑ i, if q i then ![22, 22, 231, 231, 1540] i else 0) :
    (∑ i, if q i then ![22, 22, 231, 231, 1540] i else 0) = 1771 ∧ q 4 ∧
      (¬ p 2 → q 2) ∧ (¬ p 3 → q 3) := by
  obtain ⟨h0, h1, h4, h23'⟩ := hp
  have hq0 : ¬ q 0 := fun h => hpq 0 h h0
  have hq1 : ¬ q 1 := fun h => hpq 1 h h1
  rw [Fin.sum_univ_five] at hpos h23 ⊢
  rcases h23' with ⟨h2, h3⟩ | ⟨h2, h3⟩
  · have hq2 : ¬ q 2 := fun h => hpq 2 h h2
    by_cases hq3 : q 3 <;> by_cases hq4 : q 4 <;>
      simp [hq0, hq1, hq2, hq3, hq4, h2, h3] at hpos h23 ⊢
  · have hq3 : ¬ q 3 := fun h => hpq 3 h h3
    by_cases hq2 : q 2 <;> by_cases hq4 : q 4 <;>
      simp [hq0, hq1, hq2, hq3, hq4, h2, h3] at hpos h23 ⊢

theorem shape [Finite V] (hMX : M ≤ X) (hO : OrbitData M t O)
    (hν : ∃ ν ∈ X, ν t = t ∧ (fun v => ν v) '' O 0 = O 1) (hmove : ∃ x ∈ X, x t ≠ t)
    (hdvd : (orbit X t).ncard * 887040 ∣
      2 ^ 55 * 3 ^ 6 * 5 ^ 2 * 7 ^ 3 * 11 * 17 * 23 * 31 ^ 2 * 73 * 89 * 127) :
    ((orbit X t).ncard = 45 ∧ O 0 ⊆ orbit X t ∧ O 1 ⊆ orbit X t ∧ ¬ O 2 ⊆ orbit X t ∧
        ¬ O 3 ⊆ orbit X t ∧ ¬ O 4 ⊆ orbit X t) ∨
    ((orbit X t).ncard = 276 ∧ O 0 ⊆ orbit X t ∧ O 1 ⊆ orbit X t ∧ ¬ O 4 ⊆ orbit X t ∧
        (O 2 ⊆ orbit X t ∧ ¬ O 3 ⊆ orbit X t ∨ ¬ O 2 ⊆ orbit X t ∧ O 3 ⊆ orbit X t)) ∨
    ((orbit X t).ncard = 2047 ∧ O 0 ⊆ orbit X t ∧ O 1 ⊆ orbit X t ∧ O 2 ⊆ orbit X t ∧
        O 3 ⊆ orbit X t ∧ O 4 ⊆ orbit X t) := by
  classical
  have hΩinv : ∀ g ∈ X, ∀ z ∈ orbit X t, g z ∈ orbit X t :=
    fun g hg z hz => apply_mem_orbit hg hz
  have ht : t ∈ orbit X t := mem_orbit_self t
  have h1 : (1 : V) ∉ orbit X t := one_notMem_orbit hO.ne_one
  have hZ : ∀ m ∈ M, ∀ z ∈ orbit X t \ {t}, m z ∈ orbit X t \ {t} := by
    intro m hm z hz
    refine ⟨hΩinv m (hMX hm) z hz.1, fun h => hz.2 ?_⟩
    have : m z = m t := h.trans (hO.fix m hm).symm
    exact m.injective this
  have hp : ∀ i, O i ⊆ orbit X t ↔ O i ⊆ orbit X t \ {t} := by
    intro i
    constructor
    · intro h z hz
      refine ⟨h hz, fun hzt => hO.not_mem_t i ?_⟩
      rwa [Set.mem_singleton_iff.1 hzt] at hz
    · intro h z hz
      exact (h hz).1
  have hsum := ncard_eq_sum hO hZ (fun h => h1 h.1) (fun h => h.2 rfl)
    (fun i => O i ⊆ orbit X t) hp
  have hcard : (orbit X t).ncard = (orbit X t \ {t}).ncard + 1 :=
    (Set.ncard_sdiff_singleton_add_one ht (Set.toFinite _)).symm
  obtain ⟨ν, hνX, hνt, hνimg⟩ := hν
  have h01 : O 0 ⊆ orbit X t ↔ O 1 ⊆ orbit X t := by
    constructor
    · intro h w hw
      rw [← hνimg] at hw
      obtain ⟨u, hu, rfl⟩ := hw
      exact hΩinv ν hνX u (h hu)
    · intro h u hu
      have : ν u ∈ orbit X t := h (hνimg ▸ Set.mem_image_of_mem _ hu)
      exact mem_orbit_of_apply hνX this
  have hex : ∃ i, O i ⊆ orbit X t := by
    obtain ⟨x, hxX, hxt⟩ := hmove
    have hxΩ : x t ∈ orbit X t := hΩinv x hxX t ht
    have hx1 : x t ≠ 1 := fun h => h1 (h ▸ hxΩ)
    rcases hO.cover (x t) hx1 with h | ⟨i, hi⟩
    · exact absurd h hxt
    · exact ⟨i, subset_of_mem (orbit_invariant hMX t) hO hi hxΩ⟩
  rw [hcard, hsum] at hdvd
  rcases shape_arith (fun i => O i ⊆ orbit X t) h01 hex hdvd with
    ⟨hs, h⟩ | ⟨hs, h⟩ | ⟨hs, h⟩
  · exact Or.inl ⟨by omega, h⟩
  · exact Or.inr (Or.inl ⟨by omega, h⟩)
  · exact Or.inr (Or.inr ⟨by omega, h⟩)

theorem exists_rest [Finite V] (hMX : M ≤ X) (hO : OrbitData M t O)
    (h23dvd : ∀ y : V, y ≠ 1 → 23 ∣ (orbit X y).ncard)
    (h0 : O 0 ⊆ orbit X t) (h1 : O 1 ⊆ orbit X t) (h4 : ¬ O 4 ⊆ orbit X t)
    (h23 : O 2 ⊆ orbit X t ∧ ¬ O 3 ⊆ orbit X t ∨ ¬ O 2 ⊆ orbit X t ∧ O 3 ⊆ orbit X t) :
    ∃ y : V, y ≠ 1 ∧ y ∉ orbit X t ∧ (orbit X y).ncard = 1771 ∧
      ∀ w : V, w ≠ 1 → w ∉ orbit X t → w ∈ orbit X y := by
  classical
  obtain ⟨y, hy4, hyΩ⟩ : ∃ y ∈ O 4, y ∉ orbit X t := by
    by_contra h
    exact h4 fun y hy => by_contra fun hy' => h ⟨y, hy, hy'⟩
  have hy1 : y ≠ 1 := fun h => hO.not_mem_one 4 (h ▸ hy4)
  have hne : ∀ i, (O i).Nonempty := fun i => by
    apply Set.nonempty_of_ncard_ne_zero
    rw [hO.ncard i]
    match i with
    | 0 => simp
    | 1 => simp
    | 2 => simp
    | 3 => simp
    | 4 => simp
  have hdisj : ∀ z, z ∈ orbit X y → z ∈ orbit X t → False := by
    intro z hzy hzt
    apply hyΩ
    have e1 : orbit X z = orbit X y := MulAction.orbit_eq_iff.2 hzy
    have e2 : orbit X z = orbit X t := MulAction.orbit_eq_iff.2 hzt
    rw [← e2, e1]
    exact mem_orbit_self y
  have hZt : t ∉ orbit X y := fun h => hyΩ (mem_orbit_symm.1 h)
  have hsum := ncard_eq_sum hO (orbit_invariant hMX y) (one_notMem_orbit hy1) hZt
    (fun i => O i ⊆ orbit X y) (fun i => Iff.rfl)
  have hpos : 0 < (orbit X y).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨y, mem_orbit_self y⟩
  have hdvd := h23dvd y hy1
  have hpq : ∀ i, O i ⊆ orbit X y → ¬ O i ⊆ orbit X t := by
    intro i hiy hit
    obtain ⟨w, hw⟩ := hne i
    exact hdisj w (hiy hw) (hit hw)
  rw [hsum] at hpos hdvd
  obtain ⟨hs, hq4, hq2, hq3⟩ := arith_rest (fun i => O i ⊆ orbit X t) (fun i => O i ⊆ orbit X y)
    ⟨h0, h1, h4, h23⟩ hpq hpos hdvd
  refine ⟨y, hy1, hyΩ, by rw [hsum]; exact hs, ?_⟩
  intro w hw1 hwΩ
  have hwt : w ≠ t := fun h => hwΩ (by rw [h]; exact mem_orbit_self t)
  rcases hO.cover w hw1 with h | ⟨i, hi⟩
  · exact absurd h hwt
  · have hpi : ¬ O i ⊆ orbit X t := fun h => hwΩ (h hi)
    have : O i ⊆ orbit X y := by
      match i, hpi with
      | 0, hpi => exact absurd h0 hpi
      | 1, hpi => exact absurd h1 hpi
      | 2, hpi => exact hq2 hpi
      | 3, hpi => exact hq3 hpi
      | 4, _ => exact hq4
    exact this hi

end CFSG.EvenSporadicStandard.TwoFi22.DS81.S44.Abs
