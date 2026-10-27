module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRoots
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

public section

namespace CFSG.SeitzReduction.LinearPilot

open Matrix

variable {K : Type*} [Field K]

section Semisimple

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem pow_succ_mulVec_eq_of_mulVec_eq (A : Matrix ι ι K) (μ : K) {v w : ι → K}
    (hAv : A *ᵥ v = μ • v + w) (hAw : A *ᵥ w = μ • w) (k : ℕ) :
    (A ^ (k + 1)) *ᵥ v = μ ^ (k + 1) • v + (((k + 1 : ℕ) : K) * μ ^ k) • w := by
  induction k with
  | zero =>
    rw [zero_add, pow_one, hAv, pow_one, pow_zero, Nat.cast_one, one_mul, one_smul]
  | succ k ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_add, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hAv, hAw]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

theorem sub_smul_one_mulVec (A : Matrix ι ι K) (μ : K) (v : ι → K) :
    (A - μ • (1 : Matrix ι ι K)) *ᵥ v = A *ᵥ v - μ • v := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem sub_smul_mulVec_eq_zero [CharP K 2] {A : Matrix ι ι K} {m : ℕ} (hm : Odd m) {ν : K}
    (hν : ν ≠ 0) (hA : A ^ m = ν • (1 : Matrix ι ι K)) (μ : K) {v : ι → K}
    (hv : (A - μ • (1 : Matrix ι ι K)) *ᵥ ((A - μ • (1 : Matrix ι ι K)) *ᵥ v) = 0) :
    (A - μ • (1 : Matrix ι ι K)) *ᵥ v = 0 := by
  set w := (A - μ • (1 : Matrix ι ι K)) *ᵥ v with hw
  have hAw : A *ᵥ w = μ • w := by
    rw [sub_smul_one_mulVec, sub_eq_zero] at hv
    exact hv
  have hAv : A *ᵥ v = μ • v + w := by
    rw [hw, sub_smul_one_mulVec]
    abel
  obtain ⟨k, rfl⟩ := hm
  have key := pow_succ_mulVec_eq_of_mulVec_eq A μ hAv hAw (2 * k)
  rw [hA, Matrix.smul_mulVec, Matrix.one_mulVec] at key
  have hm1 : ((2 * k + 1 : ℕ) : K) = 1 := by
    push_cast
    rw [CharTwo.two_eq_zero, zero_mul, zero_add]
  rw [hm1, one_mul] at key
  have h2 : ν • w = μ ^ (2 * k + 1) • w := by
    have h := congrArg (fun x => (A - μ • (1 : Matrix ι ι K)) *ᵥ x) key
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul] at h
    rw [← hw] at h
    have hw0 : (A - μ • (1 : Matrix ι ι K)) *ᵥ w = 0 := by
      rw [sub_smul_one_mulVec, hAw, sub_self]
    rw [hw0, smul_zero, add_zero] at h
    exact h
  by_contra hwne
  have hνμ : ν = μ ^ (2 * k + 1) := by
    have h3 : (ν - μ ^ (2 * k + 1)) • w = 0 := by rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hwne
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hνμ
    exact hν hνμ
  rw [← hνμ] at key
  have h4 : μ ^ (2 * k) • w = 0 := add_eq_left.1 key.symm
  exact hwne ((smul_eq_zero.1 h4).resolve_left (pow_ne_zero _ hμ))

end Semisimple

section RankOne

theorem exists_fourth_index {u w f : Fin 4} (huw : u ≠ w) (hfu : f ≠ u) (hfw : f ≠ w) :
    ∃ f' : Fin 4, f' ≠ u ∧ f' ≠ w ∧ f' ≠ f ∧ ∀ i : Fin 4, i = u ∨ i = w ∨ i = f ∨ i = f' := by
  have hu := u.isLt
  have hw := w.isLt
  have hf := f.isLt
  have huw' : (u : ℕ) ≠ w := fun h => huw (Fin.ext h)
  have hfu' : (f : ℕ) ≠ u := fun h => hfu (Fin.ext h)
  have hfw' : (f : ℕ) ≠ w := fun h => hfw (Fin.ext h)
  refine ⟨⟨6 - u - w - f, by omega⟩, fun h => ?_, fun h => ?_, fun h => ?_, fun i => ?_⟩
  · have h' := congrArg Fin.val h
    simp only at h'
    omega
  · have h' := congrArg Fin.val h
    simp only at h'
    omega
  · have h' := congrArg Fin.val h
    simp only at h'
    omega
  · have hi := i.isLt
    by_contra hne
    simp only [not_or, Fin.ext_iff] at hne
    omega

theorem eq_smul_add_smul_of_dotProduct_eq_zero {u w f f' : Fin 4}
    (hcover : ∀ i : Fin 4, i = u ∨ i = w ∨ i = f ∨ i = f') (huw : u ≠ w) (hfu : f ≠ u)
    (hfw : f ≠ w) (hf'u : f' ≠ u) (hf'w : f' ≠ w) (hf'f : f' ≠ f) {r : Fin 4 → K}
    (hru : r u = 0) (hrw : r w = 0) (hrf : r f ≠ 0) {x : Fin 4 → K} (hxw : x w = 0)
    (hxr : r ⬝ᵥ x = 0) :
    x = x u • Pi.single u 1 + x f' • (Pi.single f' 1 - (r f' / r f) • Pi.single f 1) := by
  have hdot : r ⬝ᵥ x = r f * x f + r f' * x f' := by
    rw [dotProduct]
    refine Finset.sum_eq_add_of_mem f f' (Finset.mem_univ _) (Finset.mem_univ _) hf'f.symm ?_
    intro c _ hc
    rcases hcover c with rfl | rfl | rfl | rfl
    · rw [hru, zero_mul]
    · rw [hrw, zero_mul]
    · exact absurd rfl hc.1
    · exact absurd rfl hc.2
  have hxf : x f = -(r f' / r f) * x f' := by
    rw [hxr] at hdot
    field_simp
    linear_combination -hdot
  funext i
  rcases hcover i with rfl | rfl | rfl | rfl
  · simp [hfu.symm, hf'u.symm]
  · simp [huw.symm, hfw.symm, hf'w.symm, hxw]
  · simp [hfu, hf'f.symm, hxf]
    ring
  · simp [hf'u, hf'f]

theorem exists_eq_vecMulVec_of_kernel_four {B : Matrix (Fin 4) (Fin 4) K} {u w : Fin 4}
    (huw : u ≠ w) {r : Fin 4 → K} (hru : r u = 0) (hrw : r w = 0) (hr : r ≠ 0)
    (hBu : B *ᵥ Pi.single u 1 = 0) (hBw : ∀ v, (B *ᵥ v) w = 0)
    (hBr : ∀ v, r ⬝ᵥ (B *ᵥ v) = 0) (hss : ∀ v, B *ᵥ (B *ᵥ v) = 0 → B *ᵥ v = 0) :
    ∃ p q : Fin 4 → K, B = vecMulVec p q := by
  obtain ⟨f, hf⟩ : ∃ f, r f ≠ 0 := by
    by_contra h
    push Not at h
    exact hr (funext h)
  have hfu : f ≠ u := fun h => hf (h ▸ hru)
  have hfw : f ≠ w := fun h => hf (h ▸ hrw)
  obtain ⟨f', hf'u, hf'w, hf'f, hcover⟩ := exists_fourth_index huw hfu hfw
  set z : Fin 4 → K := Pi.single f' 1 - (r f' / r f) • Pi.single f 1 with hz
  have hdec : ∀ x : Fin 4 → K, B *ᵥ x = (B *ᵥ x) u • Pi.single u 1 + (B *ᵥ x) f' • z :=
    fun x => eq_smul_add_smul_of_dotProduct_eq_zero hcover huw hfu hfw hf'u hf'w hf'f hru hrw hf
      (hBw x) (hBr x)
  have hkill : ∀ x : Fin 4 → K, (B *ᵥ x) f' = 0 → B *ᵥ x = 0 := fun x hx =>
    hss x (by rw [hdec x, hx, zero_smul, add_zero, Matrix.mulVec_smul, hBu, smul_zero])
  by_cases hq : (B *ᵥ z) f' = 0
  ·
    have hBz : B *ᵥ z = 0 := hkill z hq
    have hall : ∀ v, B *ᵥ v = 0 := fun v => hss v (by
      rw [hdec v, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hBu, hBz, smul_zero,
        smul_zero, add_zero])
    refine ⟨0, 0, ?_⟩
    ext i j
    have h := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h
    simpa [vecMulVec_apply] using h
  · refine ⟨B *ᵥ z, fun j => (B *ᵥ Pi.single j 1) f' / (B *ᵥ z) f', ?_⟩
    have hBj : ∀ j, B *ᵥ Pi.single j 1 = ((B *ᵥ Pi.single j 1) f' / (B *ᵥ z) f') • (B *ᵥ z) := by
      intro j
      have h := hkill (Pi.single j 1 - ((B *ᵥ Pi.single j 1) f' / (B *ᵥ z) f') • z) (by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          div_mul_cancel₀ _ hq, sub_self])
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_eq_zero] at h
      exact h
    ext i j
    have h := congrFun (hBj j) i
    rw [Matrix.mulVec_single_one, Pi.smul_apply, smul_eq_mul] at h
    rw [vecMulVec_apply, mul_comm]
    simpa using h

end RankOne

section Diag

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem vecMulVec_mulVec_eq_smul (p q v : ι → K) : vecMulVec p q *ᵥ v = (q ⬝ᵥ v) • p := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem exists_mul_eq_mul_smul_single [Nonempty ι] {p q : ι → K}
    (hss : ∀ v, vecMulVec p q *ᵥ (vecMulVec p q *ᵥ v) = 0 → vecMulVec p q *ᵥ v = 0) :
    ∃ (g : Matrix ι ι K) (b : ι) (c : K), g.det ≠ 0 ∧
      vecMulVec p q * g = g * (c • single b b 1) := by
  by_cases hB : vecMulVec p q = 0
  · obtain ⟨b⟩ := ‹Nonempty ι›
    exact ⟨1, b, 0, by rw [det_one]; exact one_ne_zero,
      by rw [hB, zero_smul, Matrix.zero_mul, Matrix.mul_zero]⟩
  have hq : q ≠ 0 := by
    rintro rfl
    apply hB
    ext i j
    simp [vecMulVec_apply]
  obtain ⟨b, hb⟩ : ∃ b, q b ≠ 0 := by
    by_contra h
    push Not at h
    exact hq (funext h)
  have hτ : q ⬝ᵥ p ≠ 0 := by
    intro hτ
    apply hB
    have hall : ∀ v, vecMulVec p q *ᵥ v = 0 := fun v => hss v (by
      rw [vecMulVec_mulVec_eq_smul p q v, Matrix.mulVec_smul, vecMulVec_mulVec_eq_smul p q p, hτ,
        zero_smul, smul_zero])
    ext i j
    have h := congrFun (hall (Pi.single j 1)) i
    rw [Matrix.mulVec_single_one] at h
    simpa using h
  set g : Matrix ι ι K := Matrix.of fun i j =>
    if j = b then p i else (1 : Matrix ι ι K) i j - (q j / q b) * (1 : Matrix ι ι K) i b with hg
  have hqg : q ᵥ* g = (q ⬝ᵥ p) • Pi.single b 1 := by
    ext j
    by_cases hj : j = b
    · subst hj
      simp [vecMul, dotProduct, hg]
    · simp only [vecMul, dotProduct, hg, Matrix.of_apply, hj, ite_false, mul_sub,
        Finset.sum_sub_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero]
      field_simp
      ring
  refine ⟨g, b, q ⬝ᵥ p, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := g)).2 hdet
    apply hv0
    have hvb : v b = 0 := by
      have h := congrArg (fun x => q ⬝ᵥ x) hv
      simp only [dotProduct_mulVec, hqg, dotProduct_zero, smul_dotProduct, single_one_dotProduct,
        smul_eq_mul] at h
      exact (mul_eq_zero.1 h).resolve_left hτ
    ext i
    by_cases hi : i = b
    · rw [hi, hvb, Pi.zero_apply]
    · have h := congrFun hv i
      have hterm : ∀ j, g i j * v j = (1 : Matrix ι ι K) i j * v j := by
        intro j
        by_cases hj : j = b
        · subst hj
          rw [hvb, mul_zero, mul_zero]
        · simp [hg, hj, Matrix.one_apply, hi]
      rw [mulVec, dotProduct, Finset.sum_congr rfl fun j _ => hterm j] at h
      simpa [Matrix.one_apply] using h
  · rw [vecMulVec_mul, hqg]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.smul_apply,
      single_apply]
    by_cases hj : j = b
    · subst hj
      simp [hg]
    · simp [hj, Ne.symm hj]

end Diag

section Main

theorem vecMul_sub_smul_apply_eq_zero {M N : Matrix (Fin 4) (Fin 4) K} {u w : Fin 4}
    (hE : Commute (single u w (1 : K)) M) (hNM : Commute N M)
    (hNsupp : ∀ i j, N i j ≠ 0 → (i = u ∧ j ≠ u) ∨ (j = w ∧ i ≠ w)) {j : Fin 4} (hj : j ≠ w) :
    ((fun k => if k = w then 0 else N u k) ᵥ* (M - M u u • (1 : Matrix (Fin 4) (Fin 4) K))) j =
      0 := by
  have hroww : ∀ k, k ≠ w → M w k = 0 := fun k hk => row_eq_zero_of_commute_single hE hk
  have h := congrFun (congrFun hNM.eq u) j
  simp only [Matrix.mul_apply] at h
  have hl : ∑ k, N u k * M k j = ∑ k, (if k = w then 0 else N u k) * M k j := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = w
    · subst hk
      rw [hroww j hj, mul_zero, ite_eq_left rfl, zero_mul]
    · rw [ite_eq_right hk]
  have hr : ∑ k, M u k * N k j = M u u * N u j := by
    refine Finset.sum_eq_single u (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ u) h)
    by_cases hN : N k j = 0
    · rw [hN, mul_zero]
    · rcases hNsupp k j hN with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hk
      · exact absurd h1 hj
  rw [hl, hr] at h
  rw [vecMul_sub, vecMul_smul, vecMul_one, Pi.sub_apply, Pi.smul_apply, ite_eq_right hj,
    smul_eq_mul]
  simp only [vecMul, dotProduct] at h ⊢
  rw [h]
  ring

theorem sub_smul_mulVec_apply_eq_zero {M N : Matrix (Fin 4) (Fin 4) K} {u w : Fin 4}
    (hE : Commute (single u w (1 : K)) M) (hNM : Commute N M)
    (hNsupp : ∀ i j, N i j ≠ 0 → (i = u ∧ j ≠ u) ∨ (j = w ∧ i ≠ w)) {i : Fin 4} (hi : i ≠ u) :
    ((M - M u u • (1 : Matrix (Fin 4) (Fin 4) K)) *ᵥ (fun k => if k = u then 0 else N k w)) i =
      0 := by
  have hcolu : ∀ k, k ≠ u → M k u = 0 := fun k hk => col_eq_zero_of_commute_single hE hk
  have hdiag : M u u = M w w := diag_eq_of_commute_single hE
  have h := congrFun (congrFun hNM.eq i) w
  simp only [Matrix.mul_apply] at h
  have hr : ∑ k, M i k * N k w = ∑ k, M i k * (if k = u then 0 else N k w) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : k = u
    · subst hk
      rw [hcolu i hi, zero_mul, ite_eq_left rfl, mul_zero]
    · rw [ite_eq_right hk]
  have hl : ∑ k, N i k * M k w = N i w * M w w := by
    refine Finset.sum_eq_single w (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ w) h)
    by_cases hN : N i k = 0
    · rw [hN, zero_mul]
    · rcases hNsupp i k hN with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hi
      · exact absurd h1 hk
  rw [hl, hr] at h
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply,
    ite_eq_right hi, smul_eq_mul, hdiag]
  simp only [mulVec, dotProduct] at h ⊢
  rw [← h]
  ring

theorem exists_commute_conj_of_commute_single [CharP K 2] {M : Matrix (Fin 4) (Fin 4) K}
    {u w : Fin 4} (huw : u ≠ w) (hE : Commute (single u w (1 : K)) M)
    {N : Matrix (Fin 4) (Fin 4) K} (hNM : Commute N M)
    (hNsupp : ∀ i j, N i j ≠ 0 → (i = u ∧ j ≠ u) ∨ (j = w ∧ i ≠ w))
    (hN : ∃ i j, N i j ≠ 0 ∧ ¬ (i = u ∧ j = w)) {m : ℕ} (hm : Odd m) {ν : K} (hν : ν ≠ 0)
    (hMm : M ^ m = ν • (1 : Matrix (Fin 4) (Fin 4) K)) :
    ∃ (g : Matrix (Fin 4) (Fin 4) K) (b : Fin 4), g.det ≠ 0 ∧
      ∀ h : Matrix (Fin 4) (Fin 4) K,
        (∀ i j, (i = b ∨ j = b) → h i j = (1 : Matrix (Fin 4) (Fin 4) K) i j) →
        Commute M (g * h * g⁻¹) := by
  set μ := M u u with hμ
  have hcolu : ∀ i, i ≠ u → M i u = 0 := fun i hi => col_eq_zero_of_commute_single hE hi
  have hroww : ∀ j, j ≠ w → M w j = 0 := fun j hj => row_eq_zero_of_commute_single hE hj
  have hdiag : M u u = M w w := diag_eq_of_commute_single hE
  set B := M - μ • (1 : Matrix (Fin 4) (Fin 4) K) with hB
  have hss : ∀ v, B *ᵥ (B *ᵥ v) = 0 → B *ᵥ v = 0 :=
    fun v hv => sub_smul_mulVec_eq_zero hm hν hMm μ hv
  have hMTm : Mᵀ ^ m = ν • (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [← transpose_pow, hMm, transpose_smul, transpose_one]
  have hBT : Bᵀ = Mᵀ - μ • (1 : Matrix (Fin 4) (Fin 4) K) := by
    rw [hB, transpose_sub, transpose_smul, transpose_one]
  have hssT : ∀ v, Bᵀ *ᵥ (Bᵀ *ᵥ v) = 0 → Bᵀ *ᵥ v = 0 := fun v hv => by
    rw [hBT] at hv ⊢
    exact sub_smul_mulVec_eq_zero hm hν hMTm μ hv
  have hBcol : ∀ i, B i u = 0 := fun i => by
    by_cases hi : i = u
    · subst hi
      simp [hB, hμ]
    · simp [hB, hi, hcolu i hi]
  have hBrow : ∀ j, B w j = 0 := fun j => by
    by_cases hj : j = w
    · subst hj
      simp [hB, hμ, hdiag]
    · simp [hB, Ne.symm hj, hroww j hj]
  have hBu : B *ᵥ Pi.single u 1 = 0 := by
    ext i
    rw [Matrix.mulVec_single_one]
    exact hBcol i
  have hBw : ∀ v, (B *ᵥ v) w = 0 := fun v => by
    simp [mulVec, dotProduct, hBrow]
  have hBTw : Bᵀ *ᵥ Pi.single w 1 = 0 := by
    ext i
    rw [Matrix.mulVec_single_one]
    exact hBrow i
  have hBTu : ∀ v, (Bᵀ *ᵥ v) u = 0 := fun v => by
    simp [mulVec, dotProduct, hBcol]
  set r : Fin 4 → K := fun k => if k = w then 0 else N u k with hr
  set s : Fin 4 → K := fun k => if k = u then 0 else N k w with hs
  have hNuu : N u u = 0 := by
    by_contra h
    rcases hNsupp u u h with ⟨-, h'⟩ | ⟨h', -⟩
    · exact h' rfl
    · exact huw h'
  have hNww : N w w = 0 := by
    by_contra h
    rcases hNsupp w w h with ⟨h', -⟩ | ⟨-, h'⟩
    · exact huw h'.symm
    · exact h' rfl
  have hru : r u = 0 := by simp [hr, huw, hNuu]
  have hrw : r w = 0 := by simp [hr]
  have hsu : s u = 0 := by simp [hs]
  have hsw : s w = 0 := by simp [hs, huw.symm, hNww]
  have hrB : r ᵥ* B = 0 := by
    have hoff : ∀ j, j ≠ w → (r ᵥ* B) j = 0 := fun j hj =>
      vecMul_sub_smul_apply_eq_zero hE hNM hNsupp hj
    have hrB' : r ᵥ* B = (r ᵥ* B) w • Pi.single w 1 := by
      ext j
      by_cases hj : j = w
      · subst hj
        simp
      · simp [hoff j hj, hj]
    have h2 : Bᵀ *ᵥ (Bᵀ *ᵥ r) = 0 := by
      rw [mulVec_transpose, mulVec_transpose, hrB', smul_vecMul, single_one_vecMul]
      ext j
      simp [hBrow]
    rw [← mulVec_transpose]
    exact hssT r h2
  have hBs : B *ᵥ s = 0 := by
    have hoff : ∀ i, i ≠ u → (B *ᵥ s) i = 0 := fun i hi =>
      sub_smul_mulVec_apply_eq_zero hE hNM hNsupp hi
    have hBs' : B *ᵥ s = (B *ᵥ s) u • Pi.single u 1 := by
      ext i
      by_cases hi : i = u
      · subst hi
        simp
      · simp [hoff i hi, hi]
    refine hss s ?_
    rw [hBs', Matrix.mulVec_smul, hBu, smul_zero]
  have hrs : r ≠ 0 ∨ s ≠ 0 := by
    obtain ⟨i, j, hij, hne⟩ := hN
    rcases hNsupp i j hij with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · left
      have hjw : j ≠ w := fun h => hne ⟨rfl, h⟩
      intro h0
      have h1 := congrFun h0 j
      simp only [hr, hjw, ite_false, Pi.zero_apply] at h1
      exact hij h1
    · right
      have hiu : i ≠ u := fun h => hne ⟨h, rfl⟩
      intro h0
      have h1 := congrFun h0 i
      simp only [hs, hiu, ite_false, Pi.zero_apply] at h1
      exact hij h1
  obtain ⟨p, q, hpq⟩ : ∃ p q : Fin 4 → K, B = vecMulVec p q := by
    rcases hrs with hr0 | hs0
    · exact exists_eq_vecMulVec_of_kernel_four huw hru hrw hr0 hBu hBw
        (fun v => by rw [dotProduct_mulVec, hrB, zero_dotProduct]) hss
    · obtain ⟨p, q, hpq⟩ := exists_eq_vecMulVec_of_kernel_four huw.symm hsw hsu hs0 hBTw hBTu
        (fun v => by rw [dotProduct_mulVec, vecMul_transpose, hBs, zero_dotProduct]) hssT
      refine ⟨q, p, ?_⟩
      rw [← transpose_transpose B, hpq, transpose_vecMulVec]
  obtain ⟨g, b, c, hg, hBg⟩ :=
    exists_mul_eq_mul_smul_single (p := p) (q := q) (by rw [← hpq]; exact hss)
  refine ⟨g, b, hg, fun h hh => ?_⟩
  set D : Matrix (Fin 4) (Fin 4) K := μ • (1 : Matrix (Fin 4) (Fin 4) K) + c • single b b 1
    with hD
  have hMg : M * g = g * D := by
    have hM : M = B + μ • (1 : Matrix (Fin 4) (Fin 4) K) := by rw [hB]; abel
    rw [hM, Matrix.add_mul, hpq, hBg, hD]
    simp only [Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    abel
  have hsh : single b b (1 : K) * h = h * single b b 1 := by
    ext i j
    have hbj : h b j = (1 : Matrix (Fin 4) (Fin 4) K) b j := hh b j (Or.inl rfl)
    have hib : h i b = (1 : Matrix (Fin 4) (Fin 4) K) i b := hh i b (Or.inr rfl)
    by_cases hi : i = b <;> by_cases hj : j = b
    · subst hi hj
      simp [Matrix.mul_apply, single_apply]
    · subst hi
      simp [Matrix.mul_apply, single_apply, hbj, Matrix.one_apply_ne (Ne.symm hj), Ne.symm hj]
    · subst hj
      simp [Matrix.mul_apply, single_apply, hib, Matrix.one_apply_ne hi, Ne.symm hi]
    · simp [Matrix.mul_apply, Ne.symm hi, Ne.symm hj]
  have hDh : D * h = h * D := by
    rw [hD, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hsh]
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.2 hg
  have hginv : g⁻¹ * M = D * g⁻¹ := by
    calc g⁻¹ * M = g⁻¹ * M * (g * g⁻¹) := by rw [Matrix.mul_nonsing_inv _ hgu, Matrix.mul_one]
      _ = g⁻¹ * (M * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = g⁻¹ * (g * D) * g⁻¹ := by rw [hMg]
      _ = D * g⁻¹ := by rw [← Matrix.mul_assoc g⁻¹ g D, Matrix.nonsing_inv_mul _ hgu,
          Matrix.one_mul]
  show M * (g * h * g⁻¹) = g * h * g⁻¹ * M
  calc M * (g * h * g⁻¹) = M * g * h * g⁻¹ := by simp only [Matrix.mul_assoc]
    _ = g * (D * h) * g⁻¹ := by rw [hMg]; simp only [Matrix.mul_assoc]
    _ = g * (h * D) * g⁻¹ := by rw [hDh]
    _ = g * h * (D * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g * h * (g⁻¹ * M) := by rw [hginv]
    _ = g * h * g⁻¹ * M := by simp only [Matrix.mul_assoc]

end Main

end CFSG.SeitzReduction.LinearPilot
