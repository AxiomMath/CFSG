module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecSwapHom

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.Permutation.SymmetricCoxeter CFSG.CGT.PushingUpLit.BHSSym

variable {G : Type*} [Group G] {z : G} {m : ℕ}

@[expose] def xs (D : SwapData z (m + 1)) (i : ℕ) : G := (D.ι (adjSwap m i) : G)

theorem adjSwap_isSwap {i : ℕ} (hi : i < m) : (adjSwap m i).IsSwap := by
  rw [adjSwap_of_lt hi]
  exact ⟨_, _, by simp [Fin.ext_iff], rfl⟩

theorem adjSwap_inj {i j : ℕ} (hi : i < m) (hj : j < m) (h : adjSwap m i = adjSwap m j) :
    i = j := by
  rw [adjSwap_of_lt hi, adjSwap_of_lt hj] at h
  rcases swap_eq_swap (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])
    h with ⟨h1, -⟩ | ⟨h1, h2⟩
  · simpa [Fin.ext_iff] using h1
  · simp only [Fin.ext_iff] at h1 h2
    omega

theorem xs_mem (D : SwapData z (m + 1)) (i : ℕ) : xs D i ∈ D.S := (D.ι _).2

theorem xs_partner (D : SwapData z (m + 1)) {i : ℕ} (hi : i < m) : xs D i ∈ Partners z :=
  D.mem_partners_iff.2 ⟨adjSwap m i, adjSwap_isSwap hi, rfl⟩

theorem isCoxeterA_xs (D : SwapData z (m + 1)) : IsCoxeterA m (xs D) :=
  IsCoxeterA.map D.hom (isCoxeterA_adjSwap m)

theorem xs_sq (D : SwapData z (m + 1)) {i : ℕ} (hi : i < m) : xs D i * xs D i = 1 :=
  (isCoxeterA_xs D).sq i hi

theorem xs_comm (D : SwapData z (m + 1)) {i j : ℕ} (hij : i + 2 ≤ j) (hj : j < m) :
    xs D i * xs D j = xs D j * xs D i :=
  (isCoxeterA_xs D).comm i j hij hj

theorem xs_ne (D : SwapData z (m + 1)) {i j : ℕ} (hi : i < m) (hj : j < m) (hij : i ≠ j) :
    xs D i ≠ xs D j := fun h => hij (adjSwap_inj hi hj (D.hom_injective h))

theorem xs_comm_z (D : SwapData z (m + 1)) (i : ℕ) : xs D i * z = z * xs D i :=
  D.comm_z (xs_mem D i)

theorem xs_ne_z (D : SwapData z (m + 1)) (hz : z ≠ 1) (i : ℕ) : xs D i ≠ z := by
  intro h
  have := xs_mem D i
  rw [h] at this
  exact D.z_notMem hz this

theorem exists_en (hm : 7 ≤ m) (hz : orderOf z = 2) (D : SwapData z (m + 1)) :
    ∃ en : G, en * en = 1 ∧ en ≠ z ∧ (xs D (m - 1) * en) ^ 3 = 1 ∧ (en * z) ^ 3 = 1 ∧
      (∀ i, i + 2 ≤ m → xs D i * en = en * xs D i) ∧ (∀ i, 2 ≤ i → i < m → en ≠ xs D i) := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hz2 : z * z = 1 := by rw [← sq, ← hz]; exact pow_orderOf_eq_one z
  obtain ⟨D₀⟩ := D.nonempty_of_isConj (xs_partner D (by omega : 0 < m)).1
  have hp : ∀ i, 2 ≤ i → i < m → xs D i ∈ Partners (xs D 0) := fun i hi2 him =>
    Partners.of_isConj (xs_partner D (by omega : 0 < m)) (xs_partner D him).1
      (xs_ne D him (by omega) (by omega))
      (xs_comm D (by omega) him).symm
  have hpz : z ∈ Partners (xs D 0) := Partners.symm (xs_partner D (by omega : 0 < m))
  obtain ⟨en, hen, h1, h2, h3, h4, h5⟩ := D₀.exists_completion (k := m - 2) (by omega)
    (t := fun j => xs D (j + 2))
    (fun j hj => hp (j + 2) (by omega) (by omega))
    (fun i j hij hj => xs_comm D (by omega) (by omega))
    (fun i j hi hj hij => xs_ne D (by omega) (by omega) (by omega))
    hpz
    (fun i hi => (xs_ne_z D hz1 (i + 2)).symm)
    (fun i hi => (xs_comm_z D (i + 2)).symm)
  have hxm : m - 2 - 1 + 2 = m - 1 := by omega
  simp only [hxm] at h1
  have hen0 : xs D 0 * en = en * xs D 0 := hen.2.2.symm
  have hen2 : en * en = 1 := Partners.mul_self_of hen (xs_sq D (by omega : 0 < m))
  have hcomm : ∀ i, 2 ≤ i → i + 2 ≤ m → xs D i * en = en * xs D i := by
    intro i hi2 him
    have := h3 (i - 2) (by omega)
    rwa [show i - 2 + 2 = i by omega, eq_comm] at this
  have hne : ∀ i, 2 ≤ i → i < m → en ≠ xs D i := by
    intro i hi2 him
    have := h4 (i - 2) (by omega)
    rwa [show i - 2 + 2 = i by omega] at this
  obtain ⟨D₃⟩ := D.nonempty_of_isConj (xs_partner D (by omega : 3 < m)).1
  have hP3 : ∀ i, i < m → i ≠ 3 → i + 2 ≤ 3 ∨ 3 + 2 ≤ i → xs D i ∈ Partners (xs D 3) := by
    intro i him hi3 hi
    refine Partners.of_isConj (xs_partner D (by omega : 3 < m)) (xs_partner D him).1
      (xs_ne D him (by omega) hi3) ?_
    rcases hi with hi | hi
    · exact xs_comm D hi (by omega)
    · exact (xs_comm D hi him).symm
  have hu : xs D (m - 1) ∈ Partners (xs D 3) := hP3 _ (by omega) (by omega) (Or.inr (by omega))
  have hs : xs D 1 ∈ Partners (xs D 3) := hP3 _ (by omega) (by omega) (Or.inl (by omega))
  have hw : z ∈ Partners (xs D 3) := Partners.symm (xs_partner D (by omega : 3 < m))
  have hv : en ∈ Partners (xs D 3) := by
    refine ⟨(xs_partner D (by omega : 3 < m)).1.symm.trans
      ((xs_partner D (by omega : 0 < m)).1.trans hen.1), hne 3 (by omega) (by omega), ?_⟩
    exact (hcomm 3 (by omega) (by omega)).symm
  have hone : xs D 1 * en = en * xs D 1 := D₃.commute_of_chain_three hu hv hw hs
    (hne (m - 1) (by omega) (by omega)).symm h5 (xs_ne_z D hz1 (m - 1))
    h1 h2 (xs_comm_z D (m - 1)) (xs_comm D (by omega : 1 + 2 ≤ m - 1) (by omega))
    (xs_comm_z D 1) (xs_ne D (by omega : 1 < m) (by omega : m - 1 < m) (by omega))
    (xs_ne_z D hz1 1)
  refine ⟨en, hen2, h5, h1, h2, ?_, hne⟩
  intro i hi
  rcases (by omega : i = 0 ∨ i = 1 ∨ 2 ≤ i) with rfl | rfl | hi2
  · exact hen0
  · exact hone
  · exact hcomm i hi2 hi

theorem exists_symmetric_overgroup (hm : 7 ≤ m) (hz : orderOf z = 2) (D : SwapData z (m + 1)) :
    ∃ (M : Subgroup G) (e : Perm (Fin (m + 3)) ≃* M),
      centralizer ({z} : Set G) ≤ M ∧ (e (adjSwap (m + 2) (m + 1)) : G) = z := by
  obtain ⟨en, hen2, hene, h1, h2, hcomm, hne⟩ := exists_en hm hz D
  have hz2 : z * z = 1 := by rw [← sq, ← hz]; exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  let t : ℕ → G := snoc (m + 1)
    (snoc m (xs D) en) z
  have ht : ∀ i, i < m → t i = xs D i := fun i hi => by
    simp only [t]
    rw [snoc_of_lt (by omega),
      snoc_of_lt hi]
  have htz : t (m + 1) = z := snoc_self
  have hx1 : IsCoxeterA (m + 1) (snoc m (xs D) en) :=
    IsCoxeterA.snoc (isCoxeterA_xs D) hen2
      (fun _ => braid_of_pow_three (xs_sq D (by omega)) hen2 h1)
      (fun i hi => hcomm i hi)
  have hx2 : IsCoxeterA (m + 2) t :=
    IsCoxeterA.snoc hx1 hz2
      (fun _ => by
        rw [show m + 1 - 1 = m by omega, snoc_self]
        exact braid_of_pow_three hen2 hz2 h2)
      (fun i hi => by
        rw [snoc_of_lt (by omega : i < m)]
        exact xs_comm_z D i)
  have h01 : t 0 ≠ t 1 := by
    rw [ht 0 (by omega), ht 1 (by omega)]
    exact xs_ne D (by omega) (by omega) (by omega)
  have h02 : t 0 ≠ t 2 := by
    rw [ht 0 (by omega), ht 2 (by omega)]
    exact xs_ne D (by omega) (by omega) (by omega)
  obtain ⟨e, he⟩ := exists_mulEquiv_closure (n := m + 2) (by omega)
    hx2 h01 (fun _ => h02)
  have hzM : z ∈ Subgroup.closure (t '' Set.Iio (m + 2)) :=
    Subgroup.subset_closure ⟨m + 1, by simp, htz⟩
  have hSM : D.S ≤ Subgroup.closure (t '' Set.Iio (m + 2)) := by
    have hle : Subgroup.closure (adjSwap m '' Set.Iio m) ≤
        (Subgroup.closure (t '' Set.Iio (m + 2))).comap D.hom := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, hi, rfl⟩
      have hi' : i < m := hi
      show D.hom (adjSwap m i) ∈ Subgroup.closure (t '' Set.Iio (m + 2))
      have : D.hom (adjSwap m i) = t i := (ht i hi').symm
      rw [this]
      exact Subgroup.subset_closure ⟨i, by simp; omega, rfl⟩
    rw [closure_adjSwap] at hle
    intro s hs
    obtain ⟨σ, hσ⟩ := D.ι.surjective ⟨s, hs⟩
    have : D.hom σ = s := by rw [D.hom_apply, hσ]
    rw [← this]
    exact hle (Subgroup.mem_top σ)
  refine ⟨_, e, ?_, ?_⟩
  · rw [D.cent]
    exact sup_le (zpowers_le.2 hzM) hSM
  · rw [he (m + 1) (by omega), htz]

end CFSG.OddStandard.AltStdSec
