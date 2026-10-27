module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3B4Model
public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowOuter

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem forall_W {P : HypIndex 2 1 → Prop} (h2 : P ιe₂) (h3 : P ιz) (h5 : P ιf₂) :
    ∀ c, c ≠ ιe₁ → c ≠ ιf₁ → P c := by
  intro c hc1 hc4
  rcases c with i | m | i <;> (try fin_cases i) <;> (try fin_cases m) <;>
    first | exact h2 | exact h3 | exact h5 | exact absurd rfl hc1 | exact absurd rfl hc4

theorem eq_diagonal_of_block {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hblk : ∀ c, c ≠ ιe₁ → c ≠ ιf₁ → A ιe₁ c = 0 ∧ A ιf₁ c = 0 ∧ A c ιe₁ = 0 ∧ A c ιf₁ = 0)
    (h14 : A ιe₁ ιf₁ = 0) (h41 : A ιf₁ ιe₁ = 0) (h23 : A ιe₂ ιz = 0) (h25 : A ιe₂ ιf₂ = 0)
    (h32 : A ιz ιe₂ = 0) (h35 : A ιz ιf₂ = 0) (h52 : A ιf₂ ιe₂ = 0) (h53 : A ιf₂ ιz = 0) :
    A = diagonal fun a => A a a := by
  obtain ⟨b12, b42, b21, b24⟩ := hblk ιe₂ (by decide) (by decide)
  obtain ⟨b13, b43, b31, b34⟩ := hblk ιz (by decide) (by decide)
  obtain ⟨b15, b45, b51, b54⟩ := hblk ιf₂ (by decide) (by decide)
  ext a b
  rcases a with i | m | i <;> rcases b with j | l | j <;> (try fin_cases i) <;>
    (try fin_cases j) <;> (try fin_cases m) <;> (try fin_cases l) <;> simp_all

theorem torus_pow_apply {t : hypSU h 2 1} (ht : t ∈ hypTorus h 2 1) (n : ℕ)
    (a : HypIndex 2 1) : mat (t ^ n) a a = mat t a a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one, one_apply_eq]
  | succ n ih => rw [pow_succ, torus_mul_apply (pow_mem ht n) ht, ih, pow_succ]

theorem pow_five_of_mem_hypScalars {s : hypSU h 2 1} (hs : s ∈ hypScalars h 2 1) :
    s ^ 5 = 1 := by
  obtain ⟨c, -, hc5, hc⟩ := hs
  have hc5' : c ^ 5 = 1 := hc5
  apply Subtype.ext
  rw [Subgroup.coe_pow, hc, ← map_pow, hc5', map_one, Subgroup.coe_one]

theorem exists_I₂_fifth (hf : 2 ≤ f) :
    ∃ j ∈ I₂sub h, ∃ β : K, β ≠ 1 ∧ β ≠ 0 ∧ mat (j ^ 5) ιe₁ ιe₁ = β ∧
      mat (j ^ 5) ιf₁ ιf₁ = β⁻¹ ∧ mat (j ^ 5) ιe₂ ιe₂ = 1 ∧ mat (j ^ 5) ιz ιz = 1 ∧
      mat (j ^ 5) ιf₂ ιf₂ = 1 := by
  obtain ⟨ω, hω⟩ := exists_unit_generator h
  have hq4 : 4 ≤ 2 ^ f := (Nat.pow_le_pow_right two_pos hf).trans_eq' (by norm_num)
  have e : (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    have h1 : 1 ≤ 2 ^ f := by omega
    have h2 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [h1, h2]
    ring
  have hdvd : 2 ^ f + 1 ∣ orderOf ω := by
    rw [hω, e]
    exact dvd_mul_right _ _
  set ω' : Kˣ := ω ^ (2 ^ f + 1) with hω'
  have hord : orderOf ω' = 2 ^ f - 1 := by
    rw [hω', orderOf_pow_of_dvd (by omega) hdvd, hω, e, Nat.mul_div_cancel_left _ (by omega)]
  set b : K := (ω' : K) with hb
  have hb0 : b ≠ 0 := Units.ne_zero _
  have hbar : h.bar b = b := by
    rw [UnitaryFieldData.bar_apply, hb, ← Units.val_pow_eq_pow_val]
    congr 1
    calc ω' ^ 2 ^ f = ω' ^ (2 ^ f - 1 + 1) := by congr 1; omega
      _ = ω' ^ (2 ^ f - 1) * ω' := pow_succ _ _
      _ = ω' := by rw [← hord, pow_orderOf_eq_one, one_mul]
  have hb5 : b ^ 5 ≠ 1 := by
    intro e5
    have e' : ω' ^ 5 = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact e5)
    have hd := orderOf_dvd_of_pow_eq_one e'
    rw [hord] at hd
    have hle := Nat.le_of_dvd (by norm_num) hd
    rcases Nat.lt_or_ge f 3 with hf3 | hf3
    · obtain rfl : f = 2 := by omega
      norm_num at hd
    · have : 8 ≤ 2 ^ f := (Nat.pow_le_pow_right two_pos hf3).trans_eq' (by norm_num)
      omega
  obtain ⟨j, hj, e1, e2, e3, e4, e5⟩ := exists_jSU h hb0 hbar
  refine ⟨j, mem_I₂sub.2 ⟨hj, e2.trans e3.symm, e3.trans e5.symm⟩, b ^ 5, hb5,
    pow_ne_zero _ hb0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [torus_pow_apply hj, e1]
  · rw [torus_pow_apply hj, e4, inv_pow]
  · rw [torus_pow_apply hj, e2, one_pow]
  · rw [torus_pow_apply hj, e3, one_pow]
  · rw [torus_pow_apply hj, e5, one_pow]

theorem act_pow_five_eq {x : Gam h} {j s : hypSU h 2 1} (hs : s ∈ hypScalars h 2 1)
    (hx : act h x j = s * j) : act h x (j ^ 5) = j ^ 5 := by
  rw [act_pow, hx, Commute.mul_pow (scalar_central hs j).symm 5, pow_five_of_mem_hypScalars hs,
    one_mul]

theorem lmat_entry_of_act_torus {x : Gam h} {t : hypSU h 2 1} (ht : t ∈ hypTorus h 2 1)
    (hx : act h x t = t) (a b : HypIndex 2 1) :
    lmat x a b * x.1.right (mat t b b) = mat t a a * lmat x a b := by
  have e := congrFun (congrFun (lmat_mul_map x t) a) b
  rw [hx, torus_mat ht, Matrix.diagonal_map (map_zero _), Matrix.mul_diagonal,
    Matrix.diagonal_mul] at e
  exact e

theorem lmat_block_of_fixed {x : Gam h} {t : hypSU h 2 1} (ht : t ∈ hypTorus h 2 1)
    (hx : act h x t = t) (h1 : mat t ιe₁ ιe₁ ≠ 1) (h4 : mat t ιf₁ ιf₁ ≠ 1)
    (hW : ∀ c, c ≠ ιe₁ → c ≠ ιf₁ → mat t c c = 1) :
    ∀ c, c ≠ ιe₁ → c ≠ ιf₁ →
      lmat x ιe₁ c = 0 ∧ lmat x ιf₁ c = 0 ∧ lmat x c ιe₁ = 0 ∧ lmat x c ιf₁ = 0 := by
  intro c hc1 hc4
  have e := lmat_entry_of_act_torus ht hx
  have hσ1 : x.1.right (mat t ιe₁ ιe₁) ≠ 1 := fun e' =>
    h1 ((map_eq_one_iff _ x.1.right.injective).1 e')
  have hσ4 : x.1.right (mat t ιf₁ ιf₁) ≠ 1 := fun e' =>
    h4 ((map_eq_one_iff _ x.1.right.injective).1 e')
  refine ⟨?_, ?_, ?_, ?_⟩
  · have k := e ιe₁ c
    rw [hW c hc1 hc4, map_one, mul_one] at k
    have : (mat t ιe₁ ιe₁ - 1) * lmat x ιe₁ c = 0 := by linear_combination -k
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h1)
  · have k := e ιf₁ c
    rw [hW c hc1 hc4, map_one, mul_one] at k
    have : (mat t ιf₁ ιf₁ - 1) * lmat x ιf₁ c = 0 := by linear_combination -k
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 h4)
  · have k := e c ιe₁
    rw [hW c hc1 hc4, one_mul] at k
    have : lmat x c ιe₁ * (x.1.right (mat t ιe₁ ιe₁) - 1) = 0 := by linear_combination k
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hσ1)
  · have k := e c ιf₁
    rw [hW c hc1 hc4, one_mul] at k
    have : lmat x c ιf₁ * (x.1.right (mat t ιf₁ ιf₁) - 1) = 0 := by linear_combination k
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hσ4)

theorem exists_fixed_I₂ (hf : 2 ≤ f) {x : Gam h}
    (hI : ∀ i ∈ I₂sub h, ∃ s ∈ hypScalars h 2 1, act h x i = s * i) :
    ∃ t ∈ hypTorus h 2 1, act h x t = t ∧ ∃ β : K, β ≠ 1 ∧ β ≠ 0 ∧ mat t ιe₁ ιe₁ = β ∧
      mat t ιf₁ ιf₁ = β⁻¹ ∧ (∀ c, c ≠ ιe₁ → c ≠ ιf₁ → mat t c c = 1) ∧
      ∀ c, c ≠ ιe₁ → c ≠ ιf₁ →
        lmat x ιe₁ c = 0 ∧ lmat x ιf₁ c = 0 ∧ lmat x c ιe₁ = 0 ∧ lmat x c ιf₁ = 0 := by
  obtain ⟨j, hj, β, hβ1, hβ0, e1, e4, e2, e3, e5⟩ := exists_I₂_fifth (h := h) hf
  obtain ⟨s, hs, hjs⟩ := hI j hj
  have hfix := act_pow_five_eq hs hjs
  have ht : j ^ 5 ∈ hypTorus h 2 1 := pow_mem (torusEq_le _ hj) 5
  have hW : ∀ c, c ≠ ιe₁ → c ≠ ιf₁ → mat (j ^ 5) c c = 1 := forall_W e2 e3 e5
  have h4 : mat (j ^ 5) ιf₁ ιf₁ ≠ 1 := by
    rw [e4]
    exact fun e' => hβ1 (inv_eq_one.1 e')
  exact ⟨j ^ 5, ht, hfix, β, hβ1, hβ0, e1, e4, hW,
    lmat_block_of_fixed ht hfix (e1 ▸ hβ1) h4 hW⟩

theorem act_mem_N₂sub {x : Gam h}
    (hcol : ∀ c, c ≠ ιe₁ → c ≠ ιf₁ → lmat x c ιe₁ = 0 ∧ lmat x c ιf₁ = 0) {n : hypSU h 2 1}
    (hn : n ∈ N₂sub h) : act h x n ∈ N₂sub h := by
  set A := lmat x with hA
  set A' : Matrix (HypIndex 2 1) (HypIndex 2 1) K :=
    ((x.1.left⁻¹ : GL (HypIndex 2 1) K) : Matrix (HypIndex 2 1) (HypIndex 2 1) K) with hA'
  set M := mat (act h x n) with hM
  obtain ⟨hn1, hn4⟩ := mem_N₂sub.1 hn
  obtain ⟨z2a, z2b⟩ := hcol ιe₂ (by decide) (by decide)
  obtain ⟨z3a, z3b⟩ := hcol ιz (by decide) (by decide)
  obtain ⟨z5a, z5b⟩ := hcol ιf₂ (by decide) (by decide)
  have hprod : ∀ (Y : Matrix (HypIndex 2 1) (HypIndex 2 1) K) (a k : HypIndex 2 1),
      (k = ιe₁ ∨ k = ιf₁) → (Y * A) a k = Y a ιe₁ * A ιe₁ k + Y a ιf₁ * A ιf₁ k := by
    intro Y a k hk
    rw [Matrix.mul_apply, sum_hypIndex_two]
    rcases hk with rfl | rfl
    · rw [z2a, z3a, z5a]
      ring
    · rw [z2b, z3b, z5b]
      ring
  have hcolM : ∀ a k, (k = ιe₁ ∨ k = ιf₁) →
      A a k = M a ιe₁ * A ιe₁ k + M a ιf₁ * A ιf₁ k := by
    intro a k hk
    have e := congrFun (congrFun (lmat_mul_map x n) a) k
    have hnk : ∀ l, (mat n).map x.1.right l k =
        (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) l k := by
      intro l
      rw [Matrix.map_apply]
      rcases hk with rfl | rfl
      · rw [hn1 l]
        by_cases hl : l = ιe₁
        · rw [hl, one_apply_eq, map_one]
        · rw [one_apply_ne hl, map_zero]
      · rw [hn4 l]
        by_cases hl : l = ιf₁
        · rw [hl, one_apply_eq, map_one]
        · rw [one_apply_ne hl, map_zero]
    rw [Matrix.mul_apply, Finset.sum_eq_single k (fun l _ hl => by
      rw [hnk l, one_apply_ne hl, mul_zero]) (by simp), hnk k, one_apply_eq, mul_one,
      ← hM, hprod M a k hk] at e
    exact e
  have hinv := (lmat_mul_inv x).2
  have cb : ∀ i k, (k = ιe₁ ∨ k = ιf₁) →
      A' i ιe₁ * A ιe₁ k + A' i ιf₁ * A ιf₁ k = (1 : Matrix (HypIndex 2 1) (HypIndex 2 1) K) i k :=
    fun i k hk => by rw [← hprod A' i k hk, hinv]
  have c11 := cb ιe₁ ιe₁ (Or.inl rfl)
  have c12 := cb ιe₁ ιf₁ (Or.inr rfl)
  have c21 := cb ιf₁ ιe₁ (Or.inl rfl)
  have c22 := cb ιf₁ ιf₁ (Or.inr rfl)
  rw [one_apply_eq] at c11 c22
  rw [one_apply_ne (by decide)] at c12 c21
  set B : Matrix (Fin 2) (Fin 2) K := !![A ιe₁ ιe₁, A ιe₁ ιf₁; A ιf₁ ιe₁, A ιf₁ ιf₁] with hB
  set C : Matrix (Fin 2) (Fin 2) K := !![A' ιe₁ ιe₁, A' ιe₁ ιf₁; A' ιf₁ ιe₁, A' ιf₁ ιf₁] with hC
  have hCB : C * B = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hB, hC, Matrix.mul_apply, Fin.sum_univ_two, c11, c12, c21, c22]
  have hBC : B * C = 1 := mul_eq_one_comm.1 hCB
  have b11 : A ιe₁ ιe₁ * A' ιe₁ ιe₁ + A ιe₁ ιf₁ * A' ιf₁ ιe₁ = 1 := by
    simpa [hB, hC, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hBC 0) 0
  have b12 : A ιe₁ ιe₁ * A' ιe₁ ιf₁ + A ιe₁ ιf₁ * A' ιf₁ ιf₁ = 0 := by
    simpa [hB, hC, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hBC 0) 1
  have b21 : A ιf₁ ιe₁ * A' ιe₁ ιe₁ + A ιf₁ ιf₁ * A' ιf₁ ιe₁ = 0 := by
    simpa [hB, hC, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hBC 1) 0
  have b22 : A ιf₁ ιe₁ * A' ιe₁ ιf₁ + A ιf₁ ιf₁ * A' ιf₁ ιf₁ = 1 := by
    simpa [hB, hC, Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hBC 1) 1
  have hMe : ∀ a, M a ιe₁ = A a ιe₁ * A' ιe₁ ιe₁ + A a ιf₁ * A' ιf₁ ιe₁ := by
    intro a
    have k1 := hcolM a ιe₁ (Or.inl rfl)
    have k2 := hcolM a ιf₁ (Or.inr rfl)
    linear_combination -A' ιe₁ ιe₁ * k1 - A' ιf₁ ιe₁ * k2 - M a ιe₁ * b11 - M a ιf₁ * b21
  have hMf : ∀ a, M a ιf₁ = A a ιe₁ * A' ιe₁ ιf₁ + A a ιf₁ * A' ιf₁ ιf₁ := by
    intro a
    have k1 := hcolM a ιe₁ (Or.inl rfl)
    have k2 := hcolM a ιf₁ (Or.inr rfl)
    linear_combination -A' ιe₁ ιf₁ * k1 - A' ιf₁ ιf₁ * k2 - M a ιe₁ * b12 - M a ιf₁ * b22
  refine mem_N₂sub.2 ⟨fun a => ?_, fun a => ?_⟩
  · change M a ιe₁ = _
    rw [hMe a]
    by_cases ha1 : a = ιe₁
    · rw [ha1, b11, one_apply_eq]
    by_cases ha4 : a = ιf₁
    · rw [ha4, b21, one_apply_ne (by decide)]
    · rw [(hcol a ha1 ha4).1, (hcol a ha1 ha4).2, zero_mul, zero_mul, add_zero,
        one_apply_ne ha1]
  · change M a ιf₁ = _
    rw [hMf a]
    by_cases ha1 : a = ιe₁
    · rw [ha1, b12, one_apply_ne (by decide)]
    by_cases ha4 : a = ιf₁
    · rw [ha4, b22, one_apply_eq]
    · rw [(hcol a ha1 ha4).1, (hcol a ha1 ha4).2, zero_mul, zero_mul, add_zero,
        one_apply_ne ha4]

theorem N₂_root_core {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K} {σ : K ≃+* K}
    (hA : ∀ n ∈ N₂sub h, n ∈ hypUnitriangular h 2 1 → A * (mat n).map σ = mat n * A) :
    A ιf₂ ιz = 0 ∧ A ιz ιe₂ = 0 ∧ A ιf₂ ιe₂ = 0 ∧ ∀ u : K, A ιe₂ ιe₂ * σ u = u * A ιz ιz := by
  have := h.charP
  have key : ∀ n ∈ N₂sub h, n ∈ hypUnitriangular h 2 1 → ∀ i j : HypIndex 2 1,
      (A * (mat n).map σ) i j = (mat n * A) i j := fun n hn hnU i j => by rw [hA n hn hnU]
  obtain ⟨n₁, hn₁, hn₁e⟩ := exists_rootI₆ h (map_one h.bar)
  have hn₁N := patSub_sI₆_le_N₂sub hn₁
  obtain ⟨hn₁U, -, a2, a3, a4, a5, a6, a7, a8, -⟩ := mem_patSub_sI₆.1 hn₁
  obtain ⟨⟨-, d2, d3, -, d5⟩, ⟨l1, l2, l3, -, l5, l6, -, l8, l9, l10⟩⟩ := U_entries hn₁U
  have k1 := key n₁ hn₁N hn₁U ιe₂ ιz
  have k2 := key n₁ hn₁N hn₁U ιz ιf₂
  have k3 := key n₁ hn₁N hn₁U ιf₂ ιf₂
  simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, a2, a3, a4, a5, a6, a7,
    a8, d2, d3, d5, l1, l2, l3, l5, l6, l8, l9, l10, hn₁e, map_zero,
    map_one, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at k1 k2 k3
  have hfz : A ιf₂ ιz = 0 := by linear_combination k1.symm
  have hze : A ιz ιe₂ = 0 := by linear_combination k2
  have hfe : A ιf₂ ιe₂ = 0 := by linear_combination k3
  refine ⟨hfz, hze, hfe, fun u => ?_⟩
  obtain ⟨c, hc⟩ := trace_surj (hK := h) (a := u * h.bar u)
    (by rw [map_mul, h.bar_bar, mul_comm])
  obtain ⟨n, hn, hnu, hnc⟩ := exists_rootI₂ h hc
  have hnN := patSub_sI₂_le_N₂sub hn
  obtain ⟨hnU, -, -, b3, -, -, b6, -⟩ := mem_patSub_sI₂.1 hn
  obtain ⟨⟨-, e2, e3, -, -⟩, ⟨m1, -, -, -, -, -, -, m8, m9, -⟩⟩ := U_entries hnU
  have k := key n hnN hnU ιe₂ ιz
  simp only [Matrix.mul_apply, sum_hypIndex_two, Matrix.map_apply, b3, b6,
    e2, e3, m1, m8, m9, hnu, hnc, hfz, map_zero,
    map_one, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add] at k
  linear_combination k

theorem sSU_comm_core {A : Matrix (HypIndex 2 1) (HypIndex 2 1) K}
    (hA : A * mat (sSU h) = mat (sSU h) * A) :
    A ιe₂ ιe₂ = A ιf₂ ιf₂ ∧ A ιe₂ ιz = A ιf₂ ιz ∧ A ιz ιe₂ = A ιz ιf₂ ∧
      A ιe₂ ιf₂ = A ιf₂ ιe₂ := by
  have e : ∀ a b, A a (σs b) = A (σs a) b := by
    intro a b
    have k := congrFun (congrFun hA a) b
    rw [Matrix.mul_apply, Matrix.mul_apply] at k
    simp only [mat_sSU, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul] at k
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _), Finset.sum_eq_single (σs b)] at k
    · rwa [ite_eq_left (σs_σs b)] at k
    · intro l _ hl
      refine ite_eq_right fun hlb => ?_
      exact hl (by rw [← hlb, σs_σs])
    · simp
  have h25 : σs ιf₂ = ιe₂ := by decide
  have h52 : σs ιe₂ = ιf₂ := by decide
  have h33 : σs ιz = ιz := by decide
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := e ιe₂ ιf₂
    rwa [h25, h52] at this
  · have := e ιf₂ ιz
    rw [h33, h25] at this
    exact this.symm
  · have := e ιz ιe₂
    rw [h52, h33] at this
    exact this.symm
  · have := e ιf₂ ιf₂
    rw [h25] at this
    exact this.symm

theorem map_mat_sSU (σ : K ≃+* K) : (mat (sSU h)).map σ = mat (sSU h) := by
  ext a b
  rw [Matrix.map_apply, mat_sSU]
  split_ifs <;> simp

theorem mem_I₂sub_of_comm_N₂sub {g : hypSU h 2 1} (hg : g ∈ N₂sub h)
    (hc : ∀ n ∈ N₂sub h, g * n = n * g) : g ∈ I₂sub h := by
  obtain ⟨hc1, hc4⟩ := mem_N₂sub.1 hg
  have hrows := N₂sub_rows hg
  set A := mat g with hA
  have hmap : ∀ M : Matrix (HypIndex 2 1) (HypIndex 2 1) K, M.map (RingEquiv.refl K) = M :=
    fun M => by ext; rfl
  have hAn : ∀ n ∈ N₂sub h, A * (mat n).map (RingEquiv.refl K) = mat n * A := fun n hn => by
    rw [hmap, hA, ← mat_mul, ← mat_mul, hc n hn]
  obtain ⟨hfz, hze, hfe, hu⟩ := N₂_root_core (σ := RingEquiv.refl K) fun n hn _ => hAn n hn
  have hez : A ιe₂ ιe₂ = A ιz ιz := by simpa using hu 1
  have hs := hAn _ sSU_mem_N₂sub
  rw [map_mat_sSU] at hs
  obtain ⟨s22, s23, s32, s25⟩ := sSU_comm_core hs
  have hblk : ∀ c, c ≠ ιe₁ → c ≠ ιf₁ → A ιe₁ c = 0 ∧ A ιf₁ c = 0 ∧ A c ιe₁ = 0 ∧ A c ιf₁ = 0 :=
    fun c hc1' hc4' => ⟨by rw [(hrows c).1, one_apply_ne (Ne.symm hc1')],
      by rw [(hrows c).2, one_apply_ne (Ne.symm hc4')],
      by rw [hc1 c, one_apply_ne hc1'], by rw [hc4 c, one_apply_ne hc4']⟩
  have hdiag : A = diagonal fun a => A a a :=
    eq_diagonal_of_block hblk (by rw [hc4 ιe₁, one_apply_ne (by decide)])
      (by rw [hc1 ιf₁, one_apply_ne (by decide)]) (by rw [s23, hfz]) (by rw [s25, hfe])
      hze (by rw [← s32, hze]) hfe hfz
  have ht : g ∈ hypTorus h 2 1 :=
    CFSG.RankThree.CentralLiftU.mem_hypTorus_of_diag h (q := fun a => A a a) hdiag
  exact mem_I₂sub.2 ⟨ht, hez, hez.symm.trans s22⟩

theorem Phi_eq_one_of_centralizes_I₂N₂ (hf : 2 ≤ f) {x : Gam h}
    (hI : ∀ i ∈ I₂sub h, ∃ s ∈ hypScalars h 2 1, act h x i = s * i)
    (hN : ∀ n ∈ N₂sub h, act h x n = n) {k : ℕ} (hk : Phi h x ^ 2 ^ k = 1) : Phi h x = 1 := by
  have := h.charP
  obtain ⟨t, ht, hfix, β, hβ1, hβ0, e1, e4, hW, hblk⟩ := exists_fixed_I₂ hf hI
  set A := lmat x with hA
  set σ := x.1.right with hσdef
  have hAN : ∀ n ∈ N₂sub h, A * (mat n).map σ = mat n * A := fun n hn => by
    rw [hA, lmat_mul_map, hN n hn]
  obtain ⟨hfz, hze, hfe, hu⟩ := N₂_root_core (σ := σ) fun n hn _ => hAN n hn
  have hez : A ιe₂ ιe₂ = A ιz ιz := by simpa using hu 1
  have he2 : A ιe₂ ιe₂ ≠ 0 := by
    have e := congrFun (congrFun (lmat_mul_inv x).2 ιe₂) ιe₂
    obtain ⟨b12, b42, -, -⟩ := hblk ιe₂ (by decide) (by decide)
    rw [Matrix.mul_apply, sum_hypIndex_two, ← hA, b12, hze, b42, hfe, one_apply_eq] at e
    simp only [mul_zero, zero_add, add_zero] at e
    exact right_ne_zero_of_mul_eq_one e
  have hσu : ∀ u : K, σ u = u := fun u => by
    have := hu u
    rw [← hez] at this
    exact mul_left_cancel₀ he2 (this.trans (mul_comm _ _))
  have hσ : σ = 1 := RingEquiv.ext hσu
  have hs := hAN _ sSU_mem_N₂sub
  rw [map_mat_sSU] at hs
  obtain ⟨s22, s23, s32, s25⟩ := sSU_comm_core hs
  have hβ : β ≠ β⁻¹ := by
    intro hββ
    have h2 : β * β = 1 := by
      calc β * β = β * β⁻¹ := by rw [← hββ]
        _ = 1 := mul_inv_cancel₀ hβ0
    have : (β - 1) * (β - 1) = 0 := by
      linear_combination h2 + (1 - β) * (CharTwo.two_eq_zero : (2 : K) = 0)
    exact hβ1 (sub_eq_zero.1 (mul_self_eq_zero.1 this))
  have h14 : A ιe₁ ιf₁ = 0 := by
    have k := lmat_entry_of_act_torus ht hfix ιe₁ ιf₁
    rw [hσu, e1, e4] at k
    have : A ιe₁ ιf₁ * (β⁻¹ - β) = 0 := by linear_combination k
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hβ.symm)
  have h41 : A ιf₁ ιe₁ = 0 := by
    have k := lmat_entry_of_act_torus ht hfix ιf₁ ιe₁
    rw [hσu, e1, e4] at k
    have : A ιf₁ ιe₁ * (β - β⁻¹) = 0 := by linear_combination k
    exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hβ)
  have hdiag : A = diagonal fun a => A a a :=
    eq_diagonal_of_block hblk h14 h41 (by rw [s23, hfz]) (by rw [s25, hfe]) hze
      (by rw [← s32, hze]) hfe hfz
  have hpow : ∀ n : ℕ, (x ^ n).1.right = 1 ∧ lmat (x ^ n) = A ^ n := by
    intro n
    induction n with
    | zero => exact ⟨by simp, by rw [pow_zero, pow_zero]; rfl⟩
    | succ n ih =>
      refine ⟨?_, ?_⟩
      · rw [pow_succ', Subgroup.coe_mul, SemidirectProduct.mul_right, ← hσdef, hσ, ih.1,
          mul_one]
      · rw [pow_succ', lmat_mul_of_right_one (by rw [← hσdef, hσ]), ih.2, ← pow_succ']
  obtain ⟨-, c, hc⟩ := Phi_eq_one_iff.1 (show Phi h (x ^ 2 ^ k) = 1 by rw [map_pow]; exact hk)
  have hAk : A ^ 2 ^ k = Matrix.scalar (HypIndex 2 1) (c : K) := by
    rw [← (hpow (2 ^ k)).2, lmat, hc, GeneralLinearGroup.coe_scalar]
  have hd : ∀ a, A a a ^ 2 ^ k = c := by
    intro a
    have e := congrFun (congrFun hAk a) a
    rw [hdiag, Matrix.diagonal_pow, Matrix.diagonal_apply_eq, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq] at e
    exact e
  have hAeq : ∀ a, A a a = A ιe₂ ιe₂ := fun a => by
    have := eq_one_of_pow_two_pow_eq_one h (c := A a a / A ιe₂ ιe₂) (k := k)
      (by rw [div_pow, hd, hd, div_self c.ne_zero])
    exact (div_eq_one_iff_eq he2).1 this
  refine Phi_eq_one_iff.2 ⟨hσ, Units.mk0 (A ιe₂ ιe₂) he2, ?_⟩
  apply Units.ext
  change A = _
  rw [GeneralLinearGroup.coe_scalar, Units.val_mk0, hdiag, Matrix.scalar_apply]
  congr 1
  funext a
  exact hAeq a

theorem N₂sub_comm_I₂sub {n i : hypSU h 2 1} (hn : n ∈ N₂sub h) (hi : i ∈ I₂sub h) :
    i * n = n * i := by
  obtain ⟨hiI, h23, h35⟩ := mem_I₂sub.1 hi
  obtain ⟨hc1, hc4⟩ := mem_N₂sub.1 hn
  have hrows := N₂sub_rows hn
  have hW : ∀ c, c ≠ ιe₁ → c ≠ ιf₁ → mat i c c = mat i ιz ιz := forall_W h23 rfl h35.symm
  refine (torus_commute_iff hiI n).2 fun a b => ?_
  by_cases hab : a = b
  · rw [hab, mul_comm]
  by_cases ha : a = ιe₁ ∨ a = ιf₁
  · have h0 : mat n a b = 0 := by
      rcases ha with rfl | rfl
      · rw [(hrows b).1, one_apply_ne hab]
      · rw [(hrows b).2, one_apply_ne hab]
    rw [h0, mul_zero, zero_mul]
  by_cases hb : b = ιe₁ ∨ b = ιf₁
  · have h0 : mat n a b = 0 := by
      rcases hb with rfl | rfl
      · rw [hc1 a, one_apply_ne hab]
      · rw [hc4 a, one_apply_ne hab]
    rw [h0, mul_zero, zero_mul]
  push Not at ha hb
  rw [hW a ha.1 ha.2, hW b hb.1 hb.2, mul_comm]

theorem conj_r_mem_patSub_I₂ {g : hypSU h 2 1} (hg : g ∈ patSub h sI₅ isPattern_sI₅) :
    rSU h * g * (rSU h)⁻¹ ∈ patSub h sI₂ isPattern_sI₂ :=
  conj_perm_mem_patSub σr_σr σr_partner mat_rSU isPattern_sI₅ isPattern_sI₂ (by decide) hg

theorem mem_N₅sub_of_conj {g : hypSU h 2 1} (hg : rSU h * g * (rSU h)⁻¹ ∈ N₂sub h) :
    g ∈ N₅sub h := by
  refine ⟨rSU h * g * (rSU h)⁻¹, hg, ?_⟩
  have hr : (rSU h)⁻¹ = rSU h := inv_eq_of_mul_eq_one_right rSU_mul_self
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hr]
  rw [← mul_assoc, ← mul_assoc, rSU_mul_self, one_mul, mul_assoc, rSU_mul_self, mul_one]

theorem patSub_I₅_le_N₅sub : patSub h sI₅ isPattern_sI₅ ≤ N₅sub h := fun _ hg =>
  mem_N₅sub_of_conj (patSub_sI₂_le_N₂sub (conj_r_mem_patSub_I₂ hg))

theorem torus_mem_N₅sub {t : hypSU h 2 1} (ht : t ∈ hypTorus h 2 1) (h2 : mat t ιe₂ ιe₂ = 1)
    (h5 : mat t ιf₂ ιf₂ = 1) : t ∈ N₅sub h := by
  refine mem_N₅sub_of_conj (mem_N₂sub.2 ⟨fun a => ?_, fun a => ?_⟩) <;> rw [conj_rSU_apply]
  · have he : σr ιe₁ = ιe₂ := by decide
    rw [he]
    by_cases ha : a = ιe₁
    · rw [ha, he, h2, one_apply_eq]
    · have hσa : σr a ≠ ιe₂ := fun e => ha (by rw [← σr_σr a, e]; decide)
      rw [torus_offdiag ht hσa, one_apply_ne ha]
  · have hf : σr ιf₁ = ιf₂ := by decide
    rw [hf]
    by_cases ha : a = ιf₁
    · rw [ha, hf, h5, one_apply_eq]
    · have hσa : σr a ≠ ιf₂ := fun e => ha (by rw [← σr_σr a, e]; decide)
      rw [torus_offdiag ht hσa, one_apply_ne ha]

end Model

end CFSG.LocalAnalysis.EvenBN.U5
