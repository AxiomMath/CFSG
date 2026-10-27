module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.ClassicalGroups.Orthogonal.Basic

public section

namespace CFSG.ComponentClassification.Sol76T13.Hq4

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def IsOrthFamily (Q : QuadraticForm K V) {ι : Type*} (x : ι → V) : Prop :=
  (∀ i, Q (x i) ≠ 0) ∧ ∀ i j, i ≠ j → polar Q (x i) (x j) = 0

theorem polar_self_eq_two_mul' (x : V) : polar Q x x = 2 * Q x := by
  rw [polar_self, two_smul, two_mul]

theorem polar_sum_smul_right {ι : Type*} [Fintype ι] (v : V) (c : ι → K) (x : ι → V) :
    polar Q v (∑ i, c i • x i) = ∑ i, c i * polar Q v (x i) := by
  have h := map_sum (polarBilin Q v) (fun i => c i • x i) Finset.univ
  simp only [polarBilin_apply_apply, map_smul, smul_eq_mul] at h
  rw [h]

section Projection

variable {ι : Type*} [Fintype ι] {x : ι → V}

@[expose] noncomputable def orthProj (Q : QuadraticForm K V) (x : ι → V) (v : V) : V :=
  v - ∑ i, (polar Q v (x i) / polar Q (x i) (x i)) • x i

theorem polar_orthProj [DecidableEq ι] (h2 : (2 : K) ≠ 0) (hx : IsOrthFamily Q x) (v : V)
    (j : ι) : polar Q (orthProj Q x v) (x j) = 0 := by
  rw [orthProj, polar_sub_left, polar_comm Q (∑ i, _), polar_sum_smul_right,
    Finset.sum_eq_single j]
  · rw [polar_comm Q (x j) (x j), div_mul_cancel₀]
    · exact sub_self _
    · rw [polar_self_eq_two_mul']
      exact mul_ne_zero h2 (hx.1 j)
  · intro i _ hij
    rw [polar_comm Q (x j) (x i), hx.2 i j hij, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem orthProj_add (v w : V) :
    orthProj Q x (v + w) = orthProj Q x v + orthProj Q x w := by
  simp only [orthProj, polar_add_left, add_div, add_smul, Finset.sum_add_distrib]
  abel

theorem eq_orthProj_add (v : V) :
    v = orthProj Q x v + ∑ i, (polar Q v (x i) / polar Q (x i) (x i)) • x i := by
  rw [orthProj, sub_add_cancel]

theorem exists_orth_of_lt_finrank [DecidableEq ι] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0) (hx : IsOrthFamily Q x)
    (hk : Fintype.card ι < Module.finrank K V) :
    (∃ y, y ≠ 0 ∧ ∀ i, polar Q y (x i) = 0) ∧ (∃ y, Q y ≠ 0 ∧ ∀ i, polar Q y (x i) = 0) := by
  have hspan : Submodule.span K (Set.range x) ≠ ⊤ := by
    intro h
    have h1 := finrank_range_le_card (R := K) x
    rw [Set.finrank, h, finrank_top] at h1
    omega
  obtain ⟨v, hv⟩ : ∃ v : V, v ∉ Submodule.span K (Set.range x) := by
    by_contra hcon
    push Not at hcon
    exact hspan (eq_top_iff.mpr fun v _ => hcon v)
  have hpv : orthProj Q x v ≠ 0 := by
    intro h0
    apply hv
    rw [eq_orthProj_add (Q := Q) (x := x) v, h0, zero_add]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨⟨_, hpv, polar_orthProj h2 hx v⟩, ?_⟩
  by_contra hcon
  push Not at hcon
  apply hpv
  refine hnd _ fun w => ?_
  have hQ0 : ∀ y, (∀ i, polar Q y (x i) = 0) → Q y = 0 := fun y hy => by
    by_contra h
    exact absurd (hcon y h) (by push Not; exact hy)
  rw [eq_orthProj_add (Q := Q) (x := x) w, polar_add_right, polar_sum_smul_right]
  have h1 : polar Q (orthProj Q x v) (orthProj Q x w) = 0 := by
    rw [polar, ← orthProj_add, hQ0 _ (polar_orthProj h2 hx _), hQ0 _ (polar_orthProj h2 hx _),
      hQ0 _ (polar_orthProj h2 hx _), sub_zero, sub_zero]
  rw [h1, zero_add]
  exact Finset.sum_eq_zero fun i _ => by rw [polar_orthProj h2 hx, mul_zero]

end Projection

theorem isOrthFamily_snoc {k : ℕ} {x : Fin k → V} (hx : IsOrthFamily Q x) {y : V} (hy : Q y ≠ 0)
    (hyx : ∀ i, polar Q y (x i) = 0) : IsOrthFamily Q (Fin.snoc x y : Fin (k + 1) → V) := by
  refine ⟨fun i => ?_, fun i j hij => ?_⟩
  · refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last]; exact hy
    · rw [Fin.snoc_castSucc]; exact hx.1 i
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j => rw [Fin.snoc_last, Fin.snoc_castSucc]; exact hyx j
    | cast i =>
      induction j using Fin.lastCases with
      | last => rw [Fin.snoc_last, Fin.snoc_castSucc, polar_comm]; exact hyx i
      | cast j =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        exact hx.2 i j (fun h => hij (by rw [h]))

variable {g : V ≃ₗ[K] V}

theorem exists_eigen_orth [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1) {k : ℕ}
    {x : Fin k → V} (hx : IsOrthFamily Q x) (hxe : ∀ i, g (x i) = x i ∨ g (x i) = -x i)
    (hk : k < Module.finrank K V) :
    ∃ y, Q y ≠ 0 ∧ (g y = y ∨ g y = -y) ∧ ∀ i, polar Q y (x i) = 0 := by
  obtain ⟨-, y, hy, hyx⟩ := exists_orth_of_lt_finrank h2 hnd hx (by rwa [Fintype.card_fin])
  have hgg : ∀ v, g (g v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hg2]
    rfl
  have hgx : ∀ i, polar Q (g y) (x i) = 0 := fun i => by
    have hxi : x i = g (g (x i)) := (hgg (x i)).symm
    rw [hxi, polar_map_of_mem hg]
    rcases hxe i with h | h
    · rw [h]; exact hyx i
    · rw [h, polar_neg_right, hyx i, neg_zero]
  set yp := (2 : K)⁻¹ • (y + g y) with hyp
  set ym := (2 : K)⁻¹ • (y - g y) with hym
  have hyp_e : g yp = yp := by
    rw [hyp, map_smul, map_add, hgg, add_comm]
  have hym_e : g ym = -ym := by
    rw [hym, map_smul, map_sub, hgg, ← smul_neg, neg_sub]
  have hsum : y = yp + ym := by
    rw [hyp, hym, ← smul_add]
    rw [show y + g y + (y - g y) = (2 : K) • y by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have hpol : polar Q yp ym = 0 := by
    have h := polar_map_of_mem hg yp ym
    rw [hyp_e, hym_e, polar_neg_right] at h
    have h' : (2 : K) * polar Q yp ym = 0 := by linear_combination -h
    exact (mul_eq_zero.mp h').resolve_left h2
  have hQy : Q y = Q yp + Q ym := by
    rw [hsum, QuadraticMap.map_add Q yp ym, hpol, add_zero]
  have hperp : ∀ i, polar Q yp (x i) = 0 ∧ polar Q ym (x i) = 0 := fun i => by
    rw [hyp, hym, polar_smul_left, polar_smul_left, polar_add_left, polar_sub_left, hyx i, hgx i]
    simp
  by_cases hp : Q yp = 0
  · refine ⟨ym, ?_, Or.inr hym_e, fun i => (hperp i).2⟩
    rw [hQy, hp, zero_add] at hy
    exact hy
  · exact ⟨yp, hp, Or.inl hyp_e, fun i => (hperp i).1⟩

theorem exists_eigen_frame [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : g * g = 1) :
    ∀ m : ℕ, m ≤ Module.finrank K V →
      ∃ x : Fin m → V, IsOrthFamily Q x ∧ ∀ i, g (x i) = x i ∨ g (x i) = -x i := by
  intro m
  induction m with
  | zero => exact fun _ => ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
  | succ k ih =>
    intro hk
    obtain ⟨x, hx, hxe⟩ := ih (by omega)
    obtain ⟨y, hy, hye, hyx⟩ := exists_eigen_orth h2 hnd hg hg2 hx hxe (by omega)
    refine ⟨Fin.snoc x y, isOrthFamily_snoc hx hy hyx, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [Fin.snoc_last]; exact hye
    · rw [Fin.snoc_castSucc]; exact hxe i

theorem polar_apply_self_of_sq_neg (h2 : (2 : K) ≠ 0)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : ∀ v, g (g v) = -v) (w : V) :
    polar Q w (g w) = 0 := by
  have hgg : g (g w) = -w := hg2 w
  have h := polar_map_of_mem hg w (g w)
  rw [hgg, polar_neg_right, polar_comm] at h
  have h' : (2 : K) * polar Q w (g w) = 0 := by linear_combination -h
  exact (mul_eq_zero.mp h').resolve_left h2

@[expose] def planeFamily (g : V ≃ₗ[K] V) {k : ℕ} (w : Fin k → V) : Fin k ⊕ Fin k → V
  | .inl i => w i
  | .inr i => g (w i)

theorem exists_plane_frame [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (hnd : ∀ v, (∀ w, polar Q v w = 0) → v = 0)
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg2 : ∀ v, g (g v) = -v) :
    ∀ k : ℕ, 2 * k ≤ Module.finrank K V →
      ∃ w : Fin k → V, IsOrthFamily Q (planeFamily g w) := by
  have hgg : ∀ v, g (g v) = -v := hg2
  intro k
  induction k with
  | zero =>
    exact fun _ => ⟨Fin.elim0, ⟨fun i => by rcases i with i | i <;> exact i.elim0,
      fun i => by rcases i with i | i <;> exact i.elim0⟩⟩
  | succ k ih =>
    intro hk
    obtain ⟨w, hw⟩ := ih (by omega)
    obtain ⟨-, y, hy, hyw⟩ := exists_orth_of_lt_finrank h2 hnd hw
      (by rw [Fintype.card_sum, Fintype.card_fin]; omega)
    have hy1 : ∀ i, polar Q y (w i) = 0 := fun i => hyw (.inl i)
    have hy2 : ∀ i, polar Q y (g (w i)) = 0 := fun i => hyw (.inr i)
    have hgy1 : ∀ i, polar Q (g y) (w i) = 0 := fun i => by
      have h := polar_map_of_mem hg y (g (w i))
      rw [hgg, polar_neg_right, hy2 i, neg_eq_zero] at h
      exact h
    have hgy2 : ∀ i, polar Q (g y) (g (w i)) = 0 := fun i => by
      rw [polar_map_of_mem hg, hy1 i]
    refine ⟨Fin.snoc w y, ⟨fun i => ?_, fun i j hij => ?_⟩⟩
    · rcases i with i | i
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simp only [planeFamily, Fin.snoc_last]; exact hy
        · simp only [planeFamily, Fin.snoc_castSucc]; exact hw.1 (.inl i)
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simp only [planeFamily, Fin.snoc_last]; rw [map_of_mem hg]; exact hy
        · simp only [planeFamily, Fin.snoc_castSucc]; exact hw.1 (.inr i)
    · have hlast : ∀ (a b : Bool) (i : Fin k),
          polar Q ((if a then g else 1) y) ((if b then g else 1) (w i)) = 0 := by
        intro a b i
        cases a <;> cases b
        · exact hy1 i
        · exact hy2 i
        · exact hgy1 i
        · exact hgy2 i
      rcases i with i | i <;> rcases j with j | j
      all_goals
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last =>
            simp only [planeFamily, Fin.snoc_last]
            first
              | exact absurd rfl hij
              | exact polar_apply_self_of_sq_neg h2 hg hg2 y
              | (rw [polar_comm]; exact polar_apply_self_of_sq_neg h2 hg hg2 y)
          | cast j =>
            simp only [planeFamily, Fin.snoc_last, Fin.snoc_castSucc]
            first
              | exact hy1 j | exact hy2 j | exact hgy1 j | exact hgy2 j
        | cast i =>
          induction j using Fin.lastCases with
          | last =>
            simp only [planeFamily, Fin.snoc_last, Fin.snoc_castSucc]
            rw [polar_comm]
            first
              | exact hy1 i | exact hy2 i | exact hgy1 i | exact hgy2 i
          | cast j =>
            simp only [planeFamily, Fin.snoc_castSucc]
            first
              | exact hw.2 (.inl i) (.inl j) (fun h => hij (by
                  rw [Sum.inl.injEq] at h; rw [h]))
              | exact hw.2 (.inl i) (.inr j) Sum.inl_ne_inr
              | exact hw.2 (.inr i) (.inl j) Sum.inr_ne_inl
              | exact hw.2 (.inr i) (.inr j) (fun h => hij (by
                  rw [Sum.inr.injEq] at h; rw [h]))

end CFSG.ComponentClassification.Sol76T13.Hq4
