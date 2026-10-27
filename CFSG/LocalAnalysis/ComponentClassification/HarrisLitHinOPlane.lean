module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinOSplit

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open Subgroup Module QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem exists_aniso_orth [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) {ι : Type*} [Fintype ι] [DecidableEq ι] (e : ι → V)
    (he : ∀ i, Q (e i) ≠ 0) (horth : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0)
    (hcard : Fintype.card ι < finrank K V) : ∃ v, Q v ≠ 0 ∧ ∀ i, polar Q (e i) v = 0 := by
  set p : V →ₗ[K] V :=
    LinearMap.id - ∑ i, ((2 * Q (e i))⁻¹ • polarBilin Q (e i)).smulRight (e i) with hpdef
  have hp : ∀ x, p x = x - ∑ i, ((2 * Q (e i))⁻¹ * polar Q (e i) x) • e i := by
    intro x
    simp [hpdef, LinearMap.sum_apply, LinearMap.smulRight_apply, polarBilin_apply_apply]
  have hpol : ∀ j x, polar Q (e j) (p x) = 0 := by
    intro j x
    have h1 : polar Q (e j) (∑ i, ((2 * Q (e i))⁻¹ * polar Q (e i) x) • e i) =
        (2 * Q (e j))⁻¹ * polar Q (e j) x * polar Q (e j) (e j) := by
      rw [← polarBilin_apply_apply, map_sum, Finset.sum_eq_single j]
      · rw [map_smul, polarBilin_apply_apply, smul_eq_mul]
      · intro i _ hij
        rw [map_smul, polarBilin_apply_apply, horth j i (Ne.symm hij), smul_zero]
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hp, polar_sub_right, h1, OddClassSelector.polar_self_eq]
    have := he j
    field_simp
    ring
  by_contra hno
  push Not at hno
  have hQp : ∀ x, Q (p x) = 0 := by
    intro x
    by_contra h
    obtain ⟨i, hi⟩ := hno (p x) h
    exact hi (hpol i x)
  have hp0 : ∀ x, p x = 0 := by
    intro x
    apply hQ.1
    intro y
    rw [polarBilin_apply_apply]
    have hy : y = p y + ∑ i, ((2 * Q (e i))⁻¹ * polar Q (e i) y) • e i := by
      rw [hp, sub_add_cancel]
    have hpp : polar Q (p x) (p y) = 0 := by
      rw [polar, ← map_add, hQp, hQp, hQp, sub_zero, sub_zero]
    rw [hy, polar_add_right, hpp, zero_add, ← polarBilin_apply_apply, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_smul, polarBilin_apply_apply, polar_comm _ (p x) (e i), hpol, smul_zero]
  have htop : Submodule.span K (Set.range e) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ i, ((2 * Q (e i))⁻¹ * polar Q (e i) x) • e i := by
      have := hp x
      rw [hp0] at this
      exact sub_eq_zero.mp this.symm
    rw [hx]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have := finrank_range_le_card (R := K) e
  rw [Set.finrank, htop, finrank_top] at this
  omega

variable (Q) (A : V ≃ₗ[K] V) (c : K)

@[expose] def tOf (v : V) : K := polar Q v (A v) / (2 * Q v)

@[expose] def wOf (v : V) : V := A v - tOf Q A v • v

@[expose] def IsAPlane (p : V × V) : Prop :=
  Q p.1 ≠ 0 ∧ Q p.2 ≠ 0 ∧ polar Q p.1 p.2 = 0 ∧ ∃ t : K, c - t ^ 2 ≠ 0 ∧
    A p.1 = p.2 + t • p.1 ∧ A p.2 = (c - t ^ 2) • p.1 - t • p.2 ∧ Q p.2 = (c - t ^ 2) * Q p.1

@[expose] def PlaneOrth (p q : V × V) : Prop :=
  polar Q p.1 q.1 = 0 ∧ polar Q p.1 q.2 = 0 ∧ polar Q p.2 q.1 = 0 ∧ polar Q p.2 q.2 = 0

variable {Q A c}

theorem PlaneOrth.symm {p q : V × V} (h : PlaneOrth Q p q) : PlaneOrth Q q p := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [polar_comm] <;> assumption

theorem isAPlane_wOf (h2 : (2 : K) ≠ 0) (hA2 : ∀ x, A (A x) = c • x)
    (hQA : ∀ x, Q (A x) = c * Q x) (hc : ¬ IsSquare c) {v : V} (hv : Q v ≠ 0) :
    IsAPlane Q A c (v, wOf Q A v) := by
  set t := tOf Q A v with ht
  have hct : c - t ^ 2 ≠ 0 := fun h => hc ⟨t, by rw [_root_.sq] at h; linear_combination h⟩
  have hvAv : polar Q v (A v) = 2 * Q v * t := by
    rw [ht, tOf]
    field_simp
  have hw : wOf Q A v = A v - t • v := rfl
  have hQw : Q (wOf Q A v) = (c - t ^ 2) * Q v := by
    rw [hw, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, QuadraticMap.map_smul,
      hQA, polar_neg_right, polar_smul_right, polar_comm _ (A v) v, hvAv, smul_eq_mul,
      smul_eq_mul]
    ring
  refine ⟨hv, ?_, ?_, t, hct, ?_, ?_, hQw⟩
  · rw [hQw]
    exact mul_ne_zero hct hv
  · change polar Q v (wOf Q A v) = 0
    rw [hw, polar_sub_right, polar_smul_right, OddClassSelector.polar_self_eq, hvAv, smul_eq_mul]
    ring
  · change A v = wOf Q A v + t • v
    rw [hw, sub_add_cancel]
  · change A (wOf Q A v) = (c - t ^ 2) • v - t • wOf Q A v
    rw [hw, map_sub, map_smul, hA2]
    module

theorem reflect_mul_reflect_apply {v w : V} (hv : Q v ≠ 0) (hw : Q w ≠ 0)
    (hvw : polar Q v w = 0) (y : V) :
    (reflect Q v * reflect Q w) y = y - (polar Q w y / Q w) • w - (polar Q v y / Q v) • v := by
  rw [LinearEquiv.mul_apply, reflect_apply hw, reflect_apply hv, polar_sub_right,
    polar_smul_right, hvw, smul_zero, sub_zero]

theorem plane_commute (hadj : ∀ x y, polar Q (A x) y = polar Q x (A y)) {p : V × V}
    (hp : IsAPlane Q A c p) :
    (reflect Q p.1 * reflect Q p.2) * A = A * (reflect Q p.1 * reflect Q p.2) := by
  obtain ⟨hv, hw, hvw, t, hct, hAv, hAw, hQw⟩ := hp
  refine LinearEquiv.ext fun y => ?_
  change (reflect Q p.1 * reflect Q p.2) (A y) = A ((reflect Q p.1 * reflect Q p.2) y)
  rw [reflect_mul_reflect_apply hv hw hvw,
    reflect_mul_reflect_apply hv hw hvw, map_sub, map_sub, map_smul, map_smul, ← hadj, ← hadj,
    hAv, hAw, polar_add_left, polar_smul_left, polar_sub_left, polar_smul_left, polar_smul_left]
  simp only [smul_eq_mul]
  have e1 : (polar Q p.2 y + t * polar Q p.1 y) / Q p.1 =
      polar Q p.2 y / Q p.2 * (c - t ^ 2) + polar Q p.1 y / Q p.1 * t := by
    rw [hQw]
    field_simp
  have e2 : ((c - t ^ 2) * polar Q p.1 y - t * polar Q p.2 y) / Q p.2 =
      polar Q p.1 y / Q p.1 - polar Q p.2 y / Q p.2 * t := by
    rw [hQw]
    field_simp
  rw [e1, e2]
  module

theorem comm4 {a b c' d : V} (hac : polar Q a c' = 0) (had : polar Q a d = 0)
    (hbc : polar Q b c' = 0) (hbd : polar Q b d = 0) :
    (reflect Q a * reflect Q b) * (reflect Q c' * reflect Q d) =
      (reflect Q c' * reflect Q d) * (reflect Q a * reflect Q b) :=
  ((Commute.mul_right (OddClassSelector.reflect_comm_of_polar_eq_zero hac)
    (OddClassSelector.reflect_comm_of_polar_eq_zero had)).mul_left
    (Commute.mul_right (OddClassSelector.reflect_comm_of_polar_eq_zero hbc)
      (OddClassSelector.reflect_comm_of_polar_eq_zero hbd))).eq

theorem exists_planes [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hA2 : ∀ x, A (A x) = c • x)
    (hQA : ∀ x, Q (A x) = c * Q x) (hadj : ∀ x y, polar Q (A x) y = polar Q x (A y))
    (hc : ¬ IsSquare c) (k : ℕ) (hk : 2 * k ≤ finrank K V) :
    ∃ f : Fin k → V × V, (∀ i, IsAPlane Q A c (f i)) ∧
      ∀ i j, i ≠ j → PlaneOrth Q (f i) (f j) := by
  classical
  induction k with
  | zero => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ k ih =>
    obtain ⟨f, hf, hfo⟩ := ih (by omega)
    set e : Fin k ⊕ Fin k → V := Sum.elim (fun i => (f i).1) (fun i => (f i).2) with he
    have heQ : ∀ i, Q (e i) ≠ 0 := by
      rintro (i | i)
      exacts [(hf i).1, (hf i).2.1]
    have heo : ∀ i j, i ≠ j → polar Q (e i) (e j) = 0 := by
      rintro (i | i) (j | j) hij
      · exact (hfo i j (fun h => hij (by rw [h]))).1
      · by_cases h : i = j
        · rw [← h]
          exact (hf i).2.2.1
        · exact (hfo i j h).2.1
      · by_cases h : i = j
        · rw [← h]
          change polar Q (f i).2 (f i).1 = 0
          rw [polar_comm]
          exact (hf i).2.2.1
        · exact (hfo i j h).2.2.1
      · exact (hfo i j (fun h => hij (by rw [h]))).2.2.2
    obtain ⟨v, hv, hve⟩ := exists_aniso_orth h2 hQ e heQ heo (by simp; omega)
    have hp := isAPlane_wOf h2 hA2 hQA hc hv
    have hpo : ∀ i, PlaneOrth Q (v, wOf Q A v) (f i) := by
      intro i
      obtain ⟨-, -, -, t, -, hAv, hAw, -⟩ := hf i
      have h1 : polar Q (f i).1 v = 0 := hve (Sum.inl i)
      have h2' : polar Q (f i).2 v = 0 := hve (Sum.inr i)
      have hA1 : polar Q (A (f i).1) v = 0 := by
        rw [hAv, polar_add_left, polar_smul_left, h1, h2', smul_zero, add_zero]
      have hA2' : polar Q (A (f i).2) v = 0 := by
        rw [hAw, polar_sub_left, polar_smul_left, polar_smul_left, h1, h2', smul_zero,
          smul_zero, sub_zero]
      have hw : ∀ x, polar Q x v = 0 → polar Q (A x) v = 0 → polar Q (wOf Q A v) x = 0 := by
        intro x hx hAx
        rw [wOf, polar_sub_left, polar_smul_left, hadj, polar_comm _ v (A x), hAx,
          polar_comm _ v x, hx, smul_zero, sub_zero]
      refine ⟨?_, ?_, hw _ h1 hA1, hw _ h2' hA2'⟩
      · change polar Q v (f i).1 = 0
        rw [polar_comm]
        exact h1
      · change polar Q v (f i).2 = 0
        rw [polar_comm]
        exact h2'
    refine ⟨Fin.cons (v, wOf Q A v) f, fun i => ?_, fun i j hij => ?_⟩
    · induction i using Fin.cases with
      | zero =>
        rw [Fin.cons_zero]
        exact hp
      | succ i =>
        rw [Fin.cons_succ]
        exact hf i
    · induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => exact absurd rfl hij
        | succ j =>
          rw [Fin.cons_zero, Fin.cons_succ]
          exact hpo j
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          rw [Fin.cons_zero, Fin.cons_succ]
          exact (hpo i).symm
        | succ j =>
          rw [Fin.cons_succ, Fin.cons_succ]
          exact hfo i j (fun h => hij (by rw [h]))

theorem exists_elemTwo_ext [Finite K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hQ : (polarBilin Q).Nondegenerate) (hP : ThreePairs Q) (hd : finrank K V = 8)
    (hA2 : ∀ x, A (A x) = c • x) (hQA : ∀ x, Q (A x) = c * Q x)
    (hadj : ∀ x y, polar Q (A x) y = polar Q x (A y)) (hc : ¬ IsSquare c) :
    ∃ E : Subgroup (V ≃ₗ[K] V),
      E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      ElemTwo E ∧ 8 ≤ Nat.card E ∧ ∀ g ∈ E, g * A = A * g := by
  classical
  have := finite_linearEquiv (K := K) (V := V)
  obtain ⟨f, hf, hfo⟩ := exists_planes h2 hQ hA2 hQA hadj hc 4 (by omega)
  set x : Fin 4 → V ≃ₗ[K] V := fun i => reflect Q (f i).1 * reflect Q (f i).2 with hx
  have hcomm : ∀ i j, x i * x j = x j * x i := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨h1, h2', h3, h4⟩ := hfo i j hij
      exact comm4 h1 h2' h3 h4
  have hsq : ∀ i, x i * x i = 1 := by
    intro i
    have hab := OddClassSelector.reflect_comm_of_polar_eq_zero (hf i).2.2.1
    change (reflect Q (f i).1 * reflect Q (f i).2) * (reflect Q (f i).1 * reflect Q (f i).2) = 1
    rw [mul_assoc, ← mul_assoc (reflect Q (f i).2), ← hab, mul_assoc, reflect_mul_self,
      mul_one, reflect_mul_self]
  have hneg : ∀ i, x i (f i).1 = -(f i).1 := by
    intro i
    have hba : polar Q (f i).2 (f i).1 = 0 := by
      rw [polar_comm]
      exact (hf i).2.2.1
    change reflect Q (f i).1 (reflect Q (f i).2 (f i).1) = -(f i).1
    rw [reflect_apply_of_polar_eq_zero hba, reflect_self_eq (hf i).1]
  have hfix : ∀ i j, i ≠ j → x j (f i).1 = (f i).1 := by
    intro i j hij
    obtain ⟨h1, -, h3, -⟩ := hfo j i (Ne.symm hij)
    change reflect Q (f j).1 (reflect Q (f j).2 (f i).1) = (f i).1
    rw [reflect_apply_of_polar_eq_zero h3, reflect_apply_of_polar_eq_zero h1]
  have hu : ∀ i, (f i).1 ≠ 0 := fun i h => (hf i).1 (by rw [h, QuadraticMap.map_zero])
  obtain ⟨hH2, hHcard, -⟩ := card_closure_dual h2 x (fun i => (f i).1) hcomm hsq hneg hfix hu
    Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hHcard
  set H := closure (x '' ↑(Finset.univ : Finset (Fin 4))) with hHdef
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hHdef, closure_le]
    rintro _ ⟨i, -, rfl⟩
    exact mul_mem (reflect_mem_orthogonalGroup Q _) (reflect_mem_orthogonalGroup Q _)
  have hHdet : H ≤ (LinearEquiv.det : (V ≃ₗ[K] V) →* Kˣ).ker := by
    rw [hHdef, closure_le]
    rintro _ ⟨i, -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hx, map_mul]
    have : Invertible (Q (f i).1) := invertibleOfNonzero (hf i).1
    have : Invertible (Q (f i).2) := invertibleOfNonzero (hf i).2.1
    rw [reflect_eq_reflection, reflect_eq_reflection, TauCeti.QuadraticMap.det_reflection,
      TauCeti.QuadraticMap.det_reflection, neg_one_mul, neg_neg]
  have hHA : H ≤ centralizer {A} := by
    rw [hHdef, closure_le]
    rintro _ ⟨i, -, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
    exact plane_commute hadj (hf i)
  have h2E := card_le_two_mul_card_inf h2 hQ hP hHO (fun h hh => hHdet hh)
  refine ⟨H ⊓ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
    inf_le_right, ⟨fun a ha b hb => hH2.1 a ha.1 b hb.1, fun a ha => hH2.2 a ha.1⟩, by omega,
    fun g hg => mem_centralizer_singleton_iff.mp (hHA hg.1)⟩

end CFSG.ComponentClassification.HarrisLit.Hin
