module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFM12Eig

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFM12

open Matrix

variable {F : Type} [Field F]

@[expose] def herm (u v : Fin 6 → F) : F := ∑ i, u i ^ 4 * v i

section Basics

variable [CharP F 2]

theorem sq_add_char2 (a b : F) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  have h := add_pow_char (p := 2) a b
  simpa using h

theorem pow4_add (a b : F) : (a + b) ^ 4 = a ^ 4 + b ^ 4 := by
  have h : (a + b) ^ 4 = ((a + b) ^ 2) ^ 2 := by ring
  rw [h, sq_add_char2, sq_add_char2]
  ring

theorem pow4_sum {ι : Type} (s : Finset ι) (f : ι → F) :
    (∑ i ∈ s, f i) ^ 4 = ∑ i ∈ s, f i ^ 4 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pow4_add, ih]

theorem herm_add_left (u u' v : Fin 6 → F) : herm (u + u') v = herm u v + herm u' v := by
  unfold herm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  rw [pow4_add]
  ring

theorem herm_smul_left (c : F) (u v : Fin 6 → F) : herm (c • u) v = c ^ 4 * herm u v := by
  unfold herm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem herm_add_right (u v v' : Fin 6 → F) : herm u (v + v') = herm u v + herm u v' := by
  unfold herm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

theorem herm_smul_right (c : F) (u v : Fin 6 → F) : herm u (c • v) = c * herm u v := by
  unfold herm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem herm_zero_left (v : Fin 6 → F) : herm 0 v = 0 := by
  unfold herm
  simp

theorem herm_zero_right (u : Fin 6 → F) : herm u 0 = 0 := by
  unfold herm
  simp

theorem herm_symm (hx16 : ∀ x : F, x ^ 16 = x) (u v : Fin 6 → F) :
    herm v u = (herm u v) ^ 4 := by
  unfold herm
  rw [pow4_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_pow, ← pow_mul]
  have h : u i ^ (4 * 4) = u i := by
    rw [show 4 * 4 = 16 by norm_num]
    exact hx16 _
  rw [h]
  ring

theorem herm_unitary {g : Matrix (Fin 6) (Fin 6) F}
    (hU : (g.map (fun x : F => x ^ 4))ᵀ * g = 1) (u v : Fin 6 → F) :
    herm (g *ᵥ u) (g *ᵥ v) = herm u v := by
  have hcol : ∀ k l : Fin 6, ∑ i, (g i k) ^ 4 * g i l = if k = l then 1 else 0 := by
    intro k l
    have h := congrFun (congrFun hU k) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [Matrix.transpose_apply, Matrix.map_apply] using h
  have step1 : ∀ i : Fin 6, (∑ k, g i k * u k) ^ 4 * ∑ l, g i l * v l =
      ∑ k, ∑ l, (g i k) ^ 4 * (u k) ^ 4 * (g i l * v l) := by
    intro i
    rw [pow4_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_pow]
  have step2 : ∀ k l : Fin 6, ∑ i, (g i k) ^ 4 * (u k) ^ 4 * (g i l * v l) =
      (u k) ^ 4 * v l * (if k = l then 1 else 0) := by
    intro k l
    rw [← hcol k l, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  unfold herm
  simp only [mulVec, dotProduct]
  simp only [step1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp only [step2, mul_ite, mul_one, mul_zero]
  simp

end Basics

section Eigen

variable [CharP F 2]

theorem four_eq_zero : (4 : F) = 0 := by
  have h : ((4 : ℕ) : F) = 0 := (CharP.cast_eq_zero_iff F 2 4).2 (by norm_num)
  simpa using h

theorem five_eq_one : (5 : F) = 1 := by
  have h4 := four_eq_zero (F := F)
  calc (5 : F) = 4 + 1 := by norm_num
    _ = 1 := by rw [h4, zero_add]

theorem exists_zeta [Finite F] (hF : Nat.card F = 16) : ∃ ζ : F, ζ ^ 5 = 1 ∧ ζ ≠ 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 16 := by rw [← Nat.card_eq_fintype_card, hF]
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5card : 5 ∣ Fintype.card Fˣ := by
    rw [Fintype.card_units, hcard]
    norm_num
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card 5 h5card
  have h5 : (ζ : Fˣ) ^ 5 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  refine ⟨(ζ : F), ?_, ?_⟩
  · have := congrArg Units.val h5
    simpa using this
  · intro h
    have h1 : (ζ : Fˣ) = 1 := Units.ext h
    rw [h1, orderOf_one] at hζ
    norm_num at hζ

variable {ζ : F}

theorem zeta_pow_eq_one_iff (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (n : ℕ) :
    ζ ^ n = 1 ↔ 5 ∣ n := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hord : orderOf ζ = 5 := orderOf_eq_prime hζ5 hζ1
  rw [← orderOf_dvd_iff_pow_eq_one, hord]

theorem geom5_zero {x : F} (hx5 : x ^ 5 = 1) (hx1 : x ≠ 1) :
    ∑ j ∈ Finset.range 5, x ^ j = 0 := by
  rw [geom_sum_eq hx1, hx5, sub_self, zero_div]

theorem geom_zeta_mul (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (k : ℕ) (hk : ¬ 5 ∣ 4 * k) :
    ∑ j ∈ Finset.range 5, ζ ^ (4 * j * k) = 0 := by
  have hx5 : (ζ ^ (4 * k)) ^ 5 = 1 := by
    rw [← pow_mul, show 4 * k * 5 = 5 * (4 * k) by ring, pow_mul, hζ5, one_pow]
  have hx1 : ζ ^ (4 * k) ≠ 1 := fun h => hk ((zeta_pow_eq_one_iff hζ5 hζ1 _).1 h)
  have : ∑ j ∈ Finset.range 5, ζ ^ (4 * j * k) = ∑ j ∈ Finset.range 5, (ζ ^ (4 * k)) ^ j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← pow_mul]
    ring_nf
  rw [this]
  exact geom5_zero hx5 hx1

@[expose] def pr (g : Matrix (Fin 6) (Fin 6) F) (ζ : F) (j : ℕ) (v : Fin 6 → F) : Fin 6 → F :=
  ∑ k ∈ Finset.range 5, (ζ ^ (4 * j * k)) • ((g ^ k) *ᵥ v)

theorem pr_sum (g : Matrix (Fin 6) (Fin 6) F) (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1) (v : Fin 6 → F) :
    ∑ j ∈ Finset.range 5, pr g ζ j v = v := by
  unfold pr
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul]
  have h1 : ∀ k ∈ ({1, 2, 3, 4} : Finset ℕ), ∑ j ∈ Finset.range 5, ζ ^ (4 * j * k) = 0 := by
    intro k hk
    apply geom_zeta_mul hζ5 hζ1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl <;> decide
  have e0 : ∑ j ∈ Finset.range 5, ζ ^ (4 * j * 0) = 1 := by
    simp [five_eq_one]
  have e1 := h1 1 (by simp)
  have e2 := h1 2 (by simp)
  have e3 := h1 3 (by simp)
  have e4 := h1 4 (by simp)
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, e0, e1, e2, e3, e4]
  simp

theorem mulVec_finset_sum (M : Matrix (Fin 6) (Fin 6) F) (s : Finset ℕ) (f : ℕ → Fin 6 → F) :
    M *ᵥ (∑ k ∈ s, f k) = ∑ k ∈ s, M *ᵥ f k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.mulVec_add, ih]

theorem pow_five_mul (hζ5 : ζ ^ 5 = 1) (n : ℕ) : ζ ^ (5 * n) = 1 := by
  rw [pow_mul, hζ5, one_pow]

theorem pr_eigen (g : Matrix (Fin 6) (Fin 6) F) (hζ5 : ζ ^ 5 = 1) (hg5 : g ^ 5 = 1) (j : ℕ)
    (v : Fin 6 → F) : g *ᵥ pr g ζ j v = (ζ ^ j) • pr g ζ j v := by
  have hsc : ∀ k : ℕ, ζ ^ j * ζ ^ (4 * j * (k + 1)) = ζ ^ (4 * j * k) := by
    intro k
    rw [← pow_add, show j + 4 * j * (k + 1) = 4 * j * k + 5 * j by ring, pow_add,
      pow_five_mul hζ5 j, mul_one]
  have hlast : ζ ^ (4 * j * 4) = ζ ^ j := by
    rw [show 4 * j * 4 = j + 5 * (3 * j) by ring, pow_add, pow_five_mul hζ5, mul_one]
  have hg5v : (g ^ 5) *ᵥ v = v := by
    rw [hg5, Matrix.one_mulVec]
  unfold pr
  rw [mulVec_finset_sum]
  simp only [Matrix.mulVec_smul]
  rw [Finset.smul_sum]
  simp only [smul_smul, Matrix.mulVec_mulVec, ← pow_succ']
  rw [Finset.sum_range_succ]
  conv_rhs => rw [Finset.sum_range_succ']
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsc k]
  · have e1 : (g ^ (4 + 1)) *ᵥ v = v := by
      rw [show 4 + 1 = 5 from rfl]
      exact hg5v
    rw [e1, hlast]
    simp

theorem herm_sum_right {ι : Type} (s : Finset ι) (u : Fin 6 → F) (f : ι → Fin 6 → F) :
    herm u (∑ i ∈ s, f i) = ∑ i ∈ s, herm u (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_right, ih]

theorem herm_sum_left {ι : Type} (s : Finset ι) (u : Fin 6 → F) (f : ι → Fin 6 → F) :
    herm (∑ i ∈ s, f i) u = ∑ i ∈ s, herm (f i) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [herm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, herm_add_left, ih]

theorem herm_eigen_orth {g : Matrix (Fin 6) (Fin 6) F}
    (hU : (g.map (fun x : F => x ^ 4))ᵀ * g = 1) {x y : Fin 6 → F} {a b : F}
    (hx : g *ᵥ x = a • x) (hy : g *ᵥ y = b • y) (hab : a ^ 4 * b ≠ 1) : herm x y = 0 := by
  have h1 := herm_unitary hU x y
  rw [hx, hy, herm_smul_left, herm_smul_right] at h1
  have h2 : (a ^ 4 * b - 1) * herm x y = 0 := by linear_combination h1
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h) hab
  · exact h

theorem herm_eigen_zeta {g : Matrix (Fin 6) (Fin 6) F}
    (hU : (g.map (fun x : F => x ^ 4))ᵀ * g = 1) (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1)
    {x y : Fin 6 → F} {j m : ℕ} (hjm : ¬ j % 5 = m % 5)
    (hx : g *ᵥ x = (ζ ^ j) • x) (hy : g *ᵥ y = (ζ ^ m) • y) : herm x y = 0 := by
  apply herm_eigen_orth hU hx hy
  rw [← pow_mul, ← pow_add]
  intro h
  rw [zeta_pow_eq_one_iff hζ5 hζ1] at h
  omega

theorem herm_expand (x y : Fin 6 → F) (a : F) :
    herm (x + a • y) (x + a • y) = herm x x + a * herm x y + a ^ 4 * herm y x + a ^ 4 * a * herm y y := by
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right]
  ring

theorem herm_zero_of_isotropic (hx16 : ∀ x : F, x ^ 16 = x) (hζ5 : ζ ^ 5 = 1) (hζ1 : ζ ≠ 1)
    {x y : Fin 6 → F} (hxx : herm x x = 0) (hyy : herm y y = 0)
    (h : ∀ a : F, herm (x + a • y) (x + a • y) = 0) : herm x y = 0 := by
  have hsym : herm y x = (herm x y) ^ 4 := herm_symm hx16 x y
  have e1 := h 1
  have e2 := h ζ
  rw [herm_expand, hxx, hyy, hsym] at e1 e2
  have hζ0 : ζ ≠ 0 := by
    intro h0
    rw [h0] at hζ5
    norm_num at hζ5
  have hne : ζ - ζ ^ 4 ≠ 0 := by
    intro h4
    have hz : ζ ^ 3 = 1 := by
      have h' : ζ * ζ ^ 3 = ζ * 1 := by
        rw [mul_one, ← pow_succ']
        exact (sub_eq_zero.1 h4).symm
      exact mul_left_cancel₀ hζ0 h'
    rw [zeta_pow_eq_one_iff hζ5 hζ1] at hz
    norm_num at hz
  have h5 : (ζ - ζ ^ 4) * herm x y = 0 := by
    linear_combination e2 - ζ ^ 4 * e1
  rcases mul_eq_zero.1 h5 with h6 | h6
  · exact absurd h6 hne
  · exact h6

end Eigen

end CFSG.LocalAnalysis.GLTheoremA.SFM12
