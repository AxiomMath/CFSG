module

public import CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocalRootOrder

public section

namespace CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal

open Matrix

variable {K : Type} [Field K]

@[expose] def blockMat (K : Type) [Field K] (s : Fin 3 → Matrix (Fin 2) (Fin 2) K) (c : K) :
    Matrix Idx Idx K :=
  Matrix.of fun a b =>
    match a, b with
    | .inl i, .inl j => if i = j then s i 0 0 else 0
    | .inl i, .inr (.inl j) => if i = j then s i 0 1 else 0
    | .inr (.inl i), .inl j => if i = j then s i 1 0 else 0
    | .inr (.inl i), .inr (.inl j) => if i = j then s i 1 1 else 0
    | .inr (.inr _), .inr (.inr _) => c
    | _, _ => 0

theorem rotMat_eq_blockMat (v : Fin 3 → ZMod 3) :
    rotMat K v = blockMat K (fun i => planeRot K (v i)) 1 := rfl

theorem blockMat_mulVec_vecOf (s : Fin 3 → Matrix (Fin 2) (Fin 2) K) (c : K) (xs ys : Fin 3 → K)
    (z : K) : blockMat K s c *ᵥ vecOf K xs ys z =
      vecOf K (fun i => s i 0 0 * xs i + s i 0 1 * ys i)
        (fun i => s i 1 0 * xs i + s i 1 1 * ys i) (c * z) := by
  funext a
  rcases a with i | i | u
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, blockMat]
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, blockMat]
  · simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, blockMat, vecOf]

theorem blockMat_mul (s s' : Fin 3 → Matrix (Fin 2) (Fin 2) K) (c c' : K) :
    blockMat K s c * blockMat K s' c' = blockMat K (fun i => s i * s' i) (c * c') := by
  rw [Matrix.ext_iff_mulVec]
  intro w
  rw [← Matrix.mulVec_mulVec, ← vecOf_eq_self w, blockMat_mulVec_vecOf, blockMat_mulVec_vecOf,
    blockMat_mulVec_vecOf, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, by ring⟩ <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem blockMat_one : blockMat K (fun _ => 1) 1 = 1 := by
  rw [Matrix.ext_iff_mulVec]
  intro w
  rw [← vecOf_eq_self w, blockMat_mulVec_vecOf, Matrix.one_mulVec, vecOf_eq_iff]
  refine ⟨funext fun i => ?_, funext fun i => ?_, by ring⟩ <;> simp

theorem blockMat_pow (s : Fin 3 → Matrix (Fin 2) (Fin 2) K) (c : K) (n : ℕ) :
    blockMat K s c ^ n = blockMat K (fun i => s i ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using blockMat_one.symm
  | succ n ih => rw [pow_succ, ih, blockMat_mul]; simp [pow_succ]

theorem blockMat_injective {s s' : Fin 3 → Matrix (Fin 2) (Fin 2) K} {c c' : K}
    (h : blockMat K s c = blockMat K s' c') : s = s' ∧ c = c' := by
  refine ⟨funext fun i => ?_, ?_⟩
  · ext a b
    fin_cases a <;> fin_cases b
    · simpa [blockMat] using congrFun (congrFun h (.inl i)) (.inl i)
    · simpa [blockMat] using congrFun (congrFun h (.inl i)) (.inr (.inl i))
    · simpa [blockMat] using congrFun (congrFun h (.inr (.inl i))) (.inl i)
    · simpa [blockMat] using congrFun (congrFun h (.inr (.inl i))) (.inr (.inl i))
  · simpa [blockMat] using congrFun (congrFun h (.inr (.inr ()))) (.inr (.inr ()))

theorem planeRot_commute {s : Matrix (Fin 2) (Fin 2) K}
    (hs : s * cubeRootMat K = cubeRootMat K * s) (k : ZMod 3) :
    s * planeRot K k = planeRot K k * s := by
  unfold planeRot
  exact Commute.pow_right (show Commute s (cubeRootMat K) from hs) k.val

theorem blockMat_mul_rotMat {s : Fin 3 → Matrix (Fin 2) (Fin 2) K} (c : K)
    (hs : ∀ i, s i * cubeRootMat K = cubeRootMat K * s i) (v : Fin 3 → ZMod 3) :
    blockMat K s c * rotMat K v = rotMat K v * blockMat K s c := by
  rw [rotMat_eq_blockMat, blockMat_mul, blockMat_mul]
  congr 1
  · funext i
    exact planeRot_commute (hs i) (v i)
  · ring

theorem entries_of_commute_cubeRootMat {s : Matrix (Fin 2) (Fin 2) K}
    (hs : s * cubeRootMat K = cubeRootMat K * s) :
    s 1 0 = - s 0 1 ∧ s 1 1 = s 0 0 + s 0 1 := by
  have h00 := congrFun (congrFun hs 0) 0
  have h01 := congrFun (congrFun hs 0) 1
  simp [cubeRootMat, Matrix.mul_apply, Fin.sum_univ_two] at h00 h01
  constructor
  · linear_combination h00
  · linear_combination h01

theorem planeNorm_mulVec_of_commute {s : Matrix (Fin 2) (Fin 2) K}
    (hs : s * cubeRootMat K = cubeRootMat K * s) (x y : K) :
    (s 0 0 * x + s 0 1 * y) ^ 2 - (s 0 0 * x + s 0 1 * y) * (s 1 0 * x + s 1 1 * y) +
      (s 1 0 * x + s 1 1 * y) ^ 2 = s.det * (x ^ 2 - x * y + y ^ 2) := by
  obtain ⟨h10, h11⟩ := entries_of_commute_cubeRootMat hs
  rw [Matrix.det_fin_two, h10, h11]
  ring

theorem modelQuad_blockMat_mulVec {s : Fin 3 → Matrix (Fin 2) (Fin 2) K} {c : K}
    (hs : ∀ i, s i * cubeRootMat K = cubeRootMat K * s i) (hdet : ∀ i, (s i).det = 1)
    (hc : c ^ 2 = 1) (a : K) (w : Idx → K) :
    modelQuad K a (blockMat K s c *ᵥ w) = modelQuad K a w := by
  rw [← vecOf_eq_self w, blockMat_mulVec_vecOf, modelQuad_vecOf, modelQuad_vecOf]
  have h0 := planeNorm_mulVec_of_commute (hs 0) (w (.inl 0)) (w (.inr (.inl 0)))
  have h1 := planeNorm_mulVec_of_commute (hs 1) (w (.inl 1)) (w (.inr (.inl 1)))
  have h2 := planeNorm_mulVec_of_commute (hs 2) (w (.inl 2)) (w (.inr (.inl 2)))
  rw [hdet 0] at h0
  rw [hdet 1] at h1
  rw [hdet 2] at h2
  simp only [mul_pow, hc, one_mul]
  linear_combination h0 + h1 + h2

private lemma exists_blockMat_vanish_plane (h3 : (3 : K) ≠ 0) {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m) (i : Fin 3) {w : Idx → K}
    (hw : w (.inl i) = 0 ∧ w (.inr (.inl i)) = 0) :
    (m *ᵥ w) (.inl i) = 0 ∧ (m *ᵥ w) (.inr (.inl i)) = 0 := by
  have hfix : rotMat K (Pi.single i 1) *ᵥ w = w := by
    rw [rotMat_mulVec_eq_self_iff h3]
    intro j hj
    have hji : j = i := by
      by_contra hne
      have h0 : (Pi.single i (1 : ZMod 3) : Fin 3 → ZMod 3) j = 0 := by
        simp [Pi.single_apply, hne]
      exact hj h0
    subst hji
    exact hw
  have hfix' : rotMat K (Pi.single i 1) *ᵥ (m *ᵥ w) = m *ᵥ w := by
    rw [Matrix.mulVec_mulVec, ← hm (Pi.single i 1), ← Matrix.mulVec_mulVec, hfix]
  rw [rotMat_mulVec_eq_self_iff h3] at hfix'
  exact hfix' i (by simp)

private lemma exists_blockMat_single_add_rot (j : Fin 3) {w : Idx → K}
    (hd : w (.inr (.inr ())) = 0)
    (hoff : ∀ i, i ≠ j → w (.inl i) = 0 ∧ w (.inr (.inl i)) = 0) :
    w + rotMat K (Pi.single j 1) *ᵥ w + rotMat K (Pi.single j 2) *ᵥ w = 0 := by
  funext a
  rcases a with i | i | u
  · rw [Pi.add_apply, Pi.add_apply, rotMat_mulVec_inl, rotMat_mulVec_inl]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply, planeRot_one, planeRot_two] <;> ring
    · obtain ⟨hx, hy⟩ := hoff i hij
      simp [Pi.single_apply, hij, hx, hy, planeRot_zero]
  · rw [Pi.add_apply, Pi.add_apply, rotMat_mulVec_inr_inl, rotMat_mulVec_inr_inl]
    by_cases hij : i = j
    · subst hij
      simp [Pi.single_apply, planeRot_one, planeRot_two] <;> ring
    · obtain ⟨hx, hy⟩ := hoff i hij
      simp [Pi.single_apply, hij, hx, hy, planeRot_zero]
  · rw [Pi.add_apply, Pi.add_apply, rotMat_mulVec_inr_inr, rotMat_mulVec_inr_inr]
    simp [hd]

private lemma exists_blockMat_entry_plane_off (h3 : (3 : K) ≠ 0) {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m)
    {i k : Fin 3} (hik : i ≠ k) {b : Idx}
    (hb : b = .inl k ∨ b = .inr (.inl k)) :
    m (.inl i) b = 0 ∧ m (.inr (.inl i)) b = 0 := by
  have hw : (Pi.single b (1 : K) : Idx → K) (.inl i) = 0 ∧
      (Pi.single b (1 : K) : Idx → K) (.inr (.inl i)) = 0 := by
    rcases hb with rfl | rfl <;> constructor <;> simp [Pi.single_apply, hik]
  have h := exists_blockMat_vanish_plane h3 hm i hw
  simpa [Matrix.mulVec_single_one] using h

private lemma exists_blockMat_entry_d'_col (h3 : (3 : K) ≠ 0) {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m) (i : Fin 3) :
    m (.inl i) (.inr (.inr ())) = 0 ∧ m (.inr (.inl i)) (.inr (.inr ())) = 0 := by
  have hw : (Pi.single (.inr (.inr ())) (1 : K) : Idx → K) (.inl i) = 0 ∧
      (Pi.single (.inr (.inr ())) (1 : K) : Idx → K) (.inr (.inl i)) = 0 := by
    constructor <;> simp [Pi.single_apply]
  have h := exists_blockMat_vanish_plane h3 hm i hw
  simpa [Matrix.mulVec_single_one] using h

private lemma exists_blockMat_entry_off (h3 : (3 : K) ≠ 0) {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m)
    {i k : Fin 3} (hik : i ≠ k) {a b : Idx}
    (ha : a = .inl i ∨ a = .inr (.inl i)) (hb : b = .inl k ∨ b = .inr (.inl k)) :
    m a b = 0 := by
  rcases ha with rfl | rfl
  · rcases hb with rfl | rfl
    · exact (exists_blockMat_entry_plane_off h3 hm hik (Or.inl rfl)).1
    · exact (exists_blockMat_entry_plane_off h3 hm hik (Or.inr rfl)).1
  · rcases hb with rfl | rfl
    · exact (exists_blockMat_entry_plane_off h3 hm hik (Or.inl rfl)).2
    · exact (exists_blockMat_entry_plane_off h3 hm hik (Or.inr rfl)).2

private lemma exists_blockMat_entry_d'_col' (h3 : (3 : K) ≠ 0) {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m)
    {i : Fin 3} {a : Idx} (ha : a = .inl i ∨ a = .inr (.inl i)) :
    m a (.inr (.inr ())) = 0 := by
  rcases ha with rfl | rfl
  · exact (exists_blockMat_entry_d'_col h3 hm i).1
  · exact (exists_blockMat_entry_d'_col h3 hm i).2

private lemma exists_blockMat_entry_d'_row (h3 : (3 : K) ≠ 0) {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m)
    {j : Fin 3} {b : Idx} (hb : b = .inl j ∨ b = .inr (.inl j)) :
    m (.inr (.inr ())) b = 0 := by
  have hz : (Pi.single b (1 : K) : Idx → K) (.inr (.inr ())) = 0 := by
    rcases hb with rfl | rfl <;> simp [Pi.single_apply]
  have hoff : ∀ i, i ≠ j →
      (Pi.single b (1 : K) : Idx → K) (.inl i) = 0 ∧
        (Pi.single b (1 : K) : Idx → K) (.inr (.inl i)) = 0 := by
    intro i hij
    rcases hb with rfl | rfl <;> constructor <;> simp [Pi.single_apply, hij]
  have hsum := exists_blockMat_single_add_rot j hz hoff
  let u : Idx → K := m *ᵥ (Pi.single b (1 : K))
  have hcomm1 : m *ᵥ (rotMat K (Pi.single j 1) *ᵥ (Pi.single b (1 : K))) =
      rotMat K (Pi.single j 1) *ᵥ u := by
    rw [Matrix.mulVec_mulVec, hm (Pi.single j 1), ← Matrix.mulVec_mulVec]
  have hcomm2 : m *ᵥ (rotMat K (Pi.single j 2) *ᵥ (Pi.single b (1 : K))) =
      rotMat K (Pi.single j 2) *ᵥ u := by
    rw [Matrix.mulVec_mulVec, hm (Pi.single j 2), ← Matrix.mulVec_mulVec]
  have h0 : u + rotMat K (Pi.single j 1) *ᵥ u + rotMat K (Pi.single j 2) *ᵥ u = 0 := by
    change m *ᵥ (Pi.single b (1 : K)) +
      rotMat K (Pi.single j 1) *ᵥ u + rotMat K (Pi.single j 2) *ᵥ u = 0
    rw [← hcomm1, ← hcomm2, ← Matrix.mulVec_add, ← Matrix.mulVec_add, hsum,
      Matrix.mulVec_zero]
  have hd' : u (.inr (.inr ())) + u (.inr (.inr ())) + u (.inr (.inr ())) = 0 := by
    have := congrFun h0 (.inr (.inr ()))
    rw [Pi.add_apply, Pi.add_apply, rotMat_mulVec_inr_inr, rotMat_mulVec_inr_inr] at this
    simpa using this
  have h3u : (3 : K) * u (.inr (.inr ())) = 0 := by linear_combination hd'
  have hu0 : u (.inr (.inr ())) = 0 := (mul_eq_zero.mp h3u).resolve_left h3
  simpa [u, Matrix.mulVec_single_one] using hu0

private lemma exists_blockMat_block_eq (h3 : (3 : K) ≠ 0) {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m) :
    ∃ (s : Fin 3 → Matrix (Fin 2) (Fin 2) K) (c : K), m = blockMat K s c := by
  let s : Fin 3 → Matrix (Fin 2) (Fin 2) K := fun i =>
    !![m (.inl i) (.inl i), m (.inl i) (.inr (.inl i));
       m (.inr (.inl i)) (.inl i), m (.inr (.inl i)) (.inr (.inl i))]
  let c : K := m (.inr (.inr ())) (.inr (.inr ()))
  refine ⟨s, c, ?_⟩
  ext a b
  rcases a with i | i | u
  · rcases b with k | k | w
    · by_cases hik : i = k
      · subst hik
        simp [s, blockMat]
      · have h0 : m (.inl i) (.inl k) = 0 :=
          exists_blockMat_entry_off h3 hm hik (Or.inl rfl) (Or.inl rfl)
        simp [blockMat, hik, h0]
    · by_cases hik : i = k
      · subst hik
        simp [s, blockMat]
      · have h0 : m (.inl i) (.inr (.inl k)) = 0 :=
          exists_blockMat_entry_off h3 hm hik (Or.inl rfl) (Or.inr rfl)
        simp [blockMat, hik, h0]
    · have h0 := exists_blockMat_entry_d'_col' h3 hm (i := i) (Or.inl rfl)
      simp [blockMat, h0]
  · rcases b with k | k | w
    · by_cases hik : i = k
      · subst hik
        simp [s, blockMat]
      · have h0 : m (.inr (.inl i)) (.inl k) = 0 :=
          exists_blockMat_entry_off h3 hm hik (Or.inr rfl) (Or.inl rfl)
        simp [blockMat, hik, h0]
    · by_cases hik : i = k
      · subst hik
        simp [s, blockMat]
      · have h0 : m (.inr (.inl i)) (.inr (.inl k)) = 0 :=
          exists_blockMat_entry_off h3 hm hik (Or.inr rfl) (Or.inr rfl)
        simp [blockMat, hik, h0]
    · have h0 := exists_blockMat_entry_d'_col' h3 hm (i := i) (Or.inr rfl)
      simp [blockMat, h0]
  · rcases b with k | k | w
    · have h0 := exists_blockMat_entry_d'_row h3 hm (j := k) (b := .inl k) (Or.inl rfl)
      simp [blockMat, h0]
    · have h0 := exists_blockMat_entry_d'_row h3 hm (j := k) (b := .inr (.inl k)) (Or.inr rfl)
      simp [blockMat, h0]
    · simp [blockMat, c]

private lemma exists_blockMat_commute {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m)
    {s : Fin 3 → Matrix (Fin 2) (Fin 2) K} {c : K} (hm_eq : m = blockMat K s c) :
    ∀ j, s j * cubeRootMat K = cubeRootMat K * s j := by
  intro j
  have hcommj := hm (Pi.single j 1)
  rw [hm_eq, rotMat_eq_blockMat, blockMat_mul, blockMat_mul] at hcommj
  have hs := (blockMat_injective hcommj).1
  have h := congrFun hs j
  simpa [Pi.single_apply, planeRot_one, cubeRootMat] using h

theorem exists_blockMat_of_commute (h3 : (3 : K) ≠ 0) {m : Matrix Idx Idx K}
    (hm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m) :
    ∃ (s : Fin 3 → Matrix (Fin 2) (Fin 2) K) (c : K),
      (∀ i, s i * cubeRootMat K = cubeRootMat K * s i) ∧ m = blockMat K s c := by
  obtain ⟨s, c, hm_eq⟩ := exists_blockMat_block_eq h3 hm
  exact ⟨s, c, exists_blockMat_commute hm hm_eq, hm_eq⟩

theorem eq_blockMat_of_isometry_commute (h3 : (3 : K) ≠ 0) {a : K} (ha : a ≠ 0)
    {m : Matrix Idx Idx K} (hiso : ∀ w, modelQuad K a (m *ᵥ w) = modelQuad K a w)
    (hcomm : ∀ v : Fin 3 → ZMod 3, m * rotMat K v = rotMat K v * m) :
    ∃ (s : Fin 3 → Matrix (Fin 2) (Fin 2) K) (c : K),
      (∀ i, s i * cubeRootMat K = cubeRootMat K * s i) ∧ (∀ i, (s i).det = 1) ∧ c ^ 2 = 1 ∧
        m = blockMat K s c := by
  obtain ⟨s, c, hs, rfl⟩ := exists_blockMat_of_commute h3 hcomm
  have hgen : ∀ xs ys : Fin 3 → K, ∀ z : K,
      (s 0).det * (xs 0 ^ 2 - xs 0 * ys 0 + ys 0 ^ 2) +
        (s 1).det * (xs 1 ^ 2 - xs 1 * ys 1 + ys 1 ^ 2) +
        (s 2).det * (xs 2 ^ 2 - xs 2 * ys 2 + ys 2 ^ 2) + a * c ^ 2 * z ^ 2 =
      (xs 0 ^ 2 - xs 0 * ys 0 + ys 0 ^ 2) + (xs 1 ^ 2 - xs 1 * ys 1 + ys 1 ^ 2) +
        (xs 2 ^ 2 - xs 2 * ys 2 + ys 2 ^ 2) + a * z ^ 2 := by
    intro xs ys z
    have h := hiso (vecOf K xs ys z)
    rw [blockMat_mulVec_vecOf, modelQuad_vecOf, modelQuad_vecOf] at h
    rw [planeNorm_mulVec_of_commute (hs 0), planeNorm_mulVec_of_commute (hs 1),
      planeNorm_mulVec_of_commute (hs 2)] at h
    linear_combination h
  have h0 := hgen ![1, 0, 0] 0 0
  have h1 := hgen ![0, 1, 0] 0 0
  have h2 := hgen ![0, 0, 1] 0 0
  have hz := hgen 0 0 1
  simp at h0 h1 h2 hz
  refine ⟨s, c, hs, fun i => ?_, ?_, rfl⟩
  · fin_cases i
    · simpa using h0
    · simpa using h1
    · simpa using h2
  · exact mul_left_cancel₀ ha (by linear_combination hz)

@[expose] def planeBlock (K : Type) [Field K] (i : Fin 3) (s : Matrix (Fin 2) (Fin 2) K) :
    Matrix Idx Idx K :=
  blockMat K (Function.update (fun _ => 1) i s) 1

theorem planeBlock_mul (i : Fin 3) (s s' : Matrix (Fin 2) (Fin 2) K) :
    planeBlock K i s * planeBlock K i s' = planeBlock K i (s * s') := by
  unfold planeBlock
  rw [blockMat_mul, mul_one]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp
  · simp [Function.update_of_ne hj]

theorem planeBlock_one (i : Fin 3) : planeBlock K i (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  unfold planeBlock
  rw [Function.update_eq_self_iff.mpr rfl]
  exact blockMat_one

@[expose] def planeBlockHom (K : Type) [Field K] (i : Fin 3) :
    Matrix (Fin 2) (Fin 2) K →* Matrix Idx Idx K where
  toFun := planeBlock K i
  map_one' := planeBlock_one i
  map_mul' s s' := (planeBlock_mul i s s').symm

@[expose] def planeGL (K : Type) [Field K] (i : Fin 3) : GL (Fin 2) K →* GL Idx K :=
  Units.map (planeBlockHom K i)

theorem coe_planeGL (i : Fin 3) (s : GL (Fin 2) K) :
    ((planeGL K i s : GL Idx K) : Matrix Idx Idx K) =
      planeBlock K i (s : Matrix (Fin 2) (Fin 2) K) := rfl

theorem planeBlock_injective (i : Fin 3) :
    Function.Injective (planeBlock K i : Matrix (Fin 2) (Fin 2) K → Matrix Idx Idx K) := by
  intro s s' h
  have := congrFun (blockMat_injective h).1 i
  simpa using this

theorem planeGL_injective (i : Fin 3) : Function.Injective (planeGL K i) := by
  intro s s' h
  apply Units.ext
  exact planeBlock_injective i (congrArg (fun g : GL Idx K => (g : Matrix Idx Idx K)) h)

theorem eq_one_of_planeBlock_eq_planeBlock {i j : Fin 3} (hij : i ≠ j)
    {s s' : Matrix (Fin 2) (Fin 2) K} (h : planeBlock K i s = planeBlock K j s') : s = 1 := by
  have := congrFun (blockMat_injective h).1 i
  simpa [Function.update_of_ne hij] using this

theorem eq_one_of_planeGL_eq_planeGL {i j : Fin 3} (hij : i ≠ j) {s s' : GL (Fin 2) K}
    (h : planeGL K i s = planeGL K j s') : s = 1 := by
  apply Units.ext
  exact eq_one_of_planeBlock_eq_planeBlock hij
    (congrArg (fun g : GL Idx K => (g : Matrix Idx Idx K)) h)

theorem update_one_mul_cubeRootMat {s : Matrix (Fin 2) (Fin 2) K}
    (hs : s * cubeRootMat K = cubeRootMat K * s) (i j : Fin 3) :
    Function.update (fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) K)) i s j * cubeRootMat K =
      cubeRootMat K * Function.update (fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) K)) i s j := by
  by_cases hj : j = i
  · subst hj
    simpa using hs
  · simp [Function.update_of_ne hj]

theorem det_update_one {s : Matrix (Fin 2) (Fin 2) K} (hdet : s.det = 1) (i j : Fin 3) :
    (Function.update (fun _ : Fin 3 => (1 : Matrix (Fin 2) (Fin 2) K)) i s j).det = 1 := by
  by_cases hj : j = i
  · subst hj
    simpa using hdet
  · simp [Function.update_of_ne hj]

theorem modelQuad_planeGL_mulVec {s : GL (Fin 2) K}
    (hs : (s : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K = cubeRootMat K * s)
    (hdet : (s : Matrix (Fin 2) (Fin 2) K).det = 1) (i : Fin 3) (a : K) (w : Idx → K) :
    modelQuad K a (((planeGL K i s : GL Idx K) : Matrix Idx Idx K) *ᵥ w) = modelQuad K a w :=
  modelQuad_blockMat_mulVec (update_one_mul_cubeRootMat hs i) (det_update_one hdet i) (one_pow 2)
    a w

theorem planeGL_mul_rotMat {s : GL (Fin 2) K}
    (hs : (s : Matrix (Fin 2) (Fin 2) K) * cubeRootMat K = cubeRootMat K * s) (i : Fin 3)
    (v : Fin 3 → ZMod 3) :
    ((planeGL K i s : GL Idx K) : Matrix Idx Idx K) * rotMat K v =
      rotMat K v * ((planeGL K i s : GL Idx K) : Matrix Idx Idx K) :=
  blockMat_mul_rotMat 1 (update_one_mul_cubeRootMat hs i) v

theorem planeGL_commute_of_ne {i j : Fin 3} (h : i ≠ j) (s s' : GL (Fin 2) K) :
    Commute (planeGL K i s) (planeGL K j s') := by
  show planeGL K i s * planeGL K j s' = planeGL K j s' * planeGL K i s
  apply Units.ext
  simp only [Units.val_mul, coe_planeGL, planeBlock, blockMat_mul, mul_one]
  congr 1
  funext k
  by_cases hki : k = i
  · subst hki
    simp [Function.update_of_ne h]
  · by_cases hkj : k = j
    · subst hkj
      simp [Function.update_of_ne hki]
    · simp [Function.update_of_ne hki, Function.update_of_ne hkj]

end CFSG.ClassicalGroups.Orthogonal.Omega7ThreeLocal
