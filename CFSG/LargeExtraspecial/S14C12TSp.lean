module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
public import CFSG.LieType.Universal.SymplecticExtras.Unipotent
public import CFSG.Timmesfeld.Orders.Classical
import all CFSG.LieType.Universal.SymplecticExtras.Matrices

public section

namespace CFSG.LargeExtraspecial.S14.Sp12

open Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.LieType.Universal.Symplectic.SpExtras
open TauCeti.GLSymplecticFin (RootSubgroupIndex)

variable {K : Type} [Field K] {n : ℕ}

@[expose] def LowZero (n : ℕ) (h : ℤ) (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) : Prop :=
  ∀ a b, lvl b - lvl a < h → N a b = 0

theorem lvl_nonneg (a : Fin n ⊕ Fin n) : 0 ≤ lvl a := by
  rcases a with i | i <;> simp only [lvl] <;> omega

theorem lvl_lt (a : Fin n ⊕ Fin n) : lvl a < 2 * n := by
  rcases a with i | i <;> simp only [lvl] <;> omega

theorem LowZero.mono {h h' : ℤ} {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hN : LowZero n h N) (hh : h' ≤ h) : LowZero n h' N :=
  fun a b hab => hN a b (by omega)

theorem LowZero.add {h : ℤ} {N N' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hN : LowZero n h N) (hN' : LowZero n h N') : LowZero n h (N + N') :=
  fun a b hab => by rw [Matrix.add_apply, hN a b hab, hN' a b hab, add_zero]

theorem LowZero.mul {h h' : ℤ} {N N' : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hN : LowZero n h N) (hN' : LowZero n h' N') : LowZero n (h + h') (N * N') := by
  intro a b hab
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases hc : lvl c - lvl a < h
  · rw [hN a c hc, zero_mul]
  · rw [hN' c b (by omega), mul_zero]

theorem lowZero_one_zero : LowZero n 0 (1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :=
  fun a b hab => Matrix.one_apply_ne (by rintro rfl; omega)

theorem LowZero.pow {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K} (hN : LowZero n 1 N) :
    ∀ k : ℕ, LowZero n k (N ^ k)
  | 0 => by simpa using lowZero_one_zero
  | k + 1 => by
    rw [pow_succ]
    exact ((LowZero.pow hN k).mul hN).mono (by push_cast; omega)

theorem LowZero.eq_zero {N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hN : LowZero n (2 * n) N) : N = 0 := by
  ext a b
  exact hN a b (by have := lvl_nonneg a; have := lvl_lt b; omega)

theorem one_add_pow_two_pow [CharP K 2] (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) :
    ∀ k : ℕ, (1 + A) ^ 2 ^ k = 1 + A ^ 2 ^ k
  | 0 => by simp
  | k + 1 => by
    have h2 : A ^ 2 ^ k + A ^ 2 ^ k = 0 := by
      ext a b
      rw [Matrix.add_apply, Matrix.zero_apply, CharTwo.add_self_eq_zero]
    calc (1 + A) ^ 2 ^ (k + 1) = (1 + A) ^ 2 ^ k * (1 + A) ^ 2 ^ k := by
          rw [pow_succ, pow_mul, sq]
      _ = (1 + A ^ 2 ^ k) * (1 + A ^ 2 ^ k) := by rw [one_add_pow_two_pow A k]
      _ = 1 + (A ^ 2 ^ k + A ^ 2 ^ k) + A ^ 2 ^ k * A ^ 2 ^ k := by noncomm_ring
      _ = 1 + A ^ 2 ^ (k + 1) := by rw [h2, add_zero, ← pow_add, ← two_mul, pow_succ']

theorem pow_two_pow_eq_one [CharP K 2] {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (hM : LowZero n 1 (M - 1)) : M ^ 2 ^ (2 * n) = 1 := by
  have hk : 2 * n ≤ 2 ^ (2 * n) := (Nat.lt_two_pow_self).le
  have h1 : LowZero n (2 * n) ((M - 1) ^ (2 * n)) := by exact_mod_cast hM.pow (2 * n)
  have h0 : (M - 1) ^ 2 ^ (2 * n) = 0 := by
    rw [← Nat.sub_add_cancel hk, pow_add, h1.eq_zero, mul_zero]
  rw [show M = 1 + (M - 1) by abel, one_add_pow_two_pow, h0, add_zero]

section Uni

theorem lowZero_mat_mul {x y : StatedSp n K} (hx : LowZero n 1 (mat n K x - 1))
    (hy : LowZero n 1 (mat n K y - 1)) : LowZero n 1 (mat n K (x * y) - 1) := by
  rw [map_mul, show mat n K x * mat n K y - 1 = (mat n K x - 1) + (mat n K y - 1) +
    (mat n K x - 1) * (mat n K y - 1) by noncomm_ring]
  exact (hx.add hy).add ((hx.mul hy).mono (by norm_num))

theorem lowZero_mat_pow {x : StatedSp n K} (hx : LowZero n 1 (mat n K x - 1)) :
    ∀ k : ℕ, LowZero n 1 (mat n K (x ^ k) - 1)
  | 0 => fun a b _ => by rw [pow_zero, map_one, sub_self, Matrix.zero_apply]
  | k + 1 => by
    rw [pow_succ]
    exact lowZero_mat_mul (lowZero_mat_pow hx k) hx

variable [CharP K 2]

theorem pow_two_pow_eq_one_of_lowZero {x : StatedSp n K} (hx : LowZero n 1 (mat n K x - 1)) :
    x ^ 2 ^ (2 * n) = 1 :=
  mat_injective (by rw [map_pow, map_one]; exact pow_two_pow_eq_one hx)

@[expose] def uniSub (n : ℕ) (K : Type) [Field K] [CharP K 2] : Subgroup (StatedSp n K) where
  carrier := {x | LowZero n 1 (mat n K x - 1)}
  one_mem' := fun a b _ => by rw [map_one, sub_self, Matrix.zero_apply]
  mul_mem' := lowZero_mat_mul
  inv_mem' := fun {x} hx => by
    have h := pow_two_pow_eq_one_of_lowZero hx
    have hinv : x⁻¹ = x ^ (2 ^ (2 * n) - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel Nat.one_le_two_pow, h]
    show LowZero n 1 (mat n K x⁻¹ - 1)
    rw [hinv]
    exact lowZero_mat_pow hx _

theorem isPGroup_uniSub : IsPGroup 2 (uniSub n K) := by
  intro x
  refine ⟨2 * n, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact pow_two_pow_eq_one_of_lowZero x.2

theorem elt_mem_uniSub {r : RootSubgroupIndex n} (hr : 1 ≤ lvl (pos1 r).2 - lvl (pos1 r).1)
    (c : K) : elt r c ∈ uniSub n K := by
  have h := idBelow_mat_elt (F := K) 1 (h := 1) (r := r) (by simpa using hr) c
  intro a b hab
  rw [Matrix.sub_apply, h a b (by simpa using hab), sub_self]

end Uni

theorem E_mul_eq_of_commute {r : RootSubgroupIndex n} {y : StatedSp n K}
    (h : Commute (elt r (1 : K)) y) : E K r * mat n K y = mat n K y * E K r := by
  have h' := congrArg (mat n K) h.eq
  rw [map_mul, map_mul, mat_elt, one_smul, add_mul, mul_add, one_mul, mul_one] at h'
  exact add_left_cancel h'

section Entries

variable {X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}

theorem entries_of_long (k : Fin n)
    (h : E K (.positiveLong k) * X = X * E K (.positiveLong k)) :
    (∀ a, a ≠ .inl k → X a (.inl k) = 0) ∧ (∀ b, b ≠ .inr k → X (.inr k) b = 0) ∧
      X (.inl k) (.inl k) = X (.inr k) (.inr k) := by
  simp only [E] at h
  refine ⟨fun a ha => ?_, fun b hb => ?_, ?_⟩
  · have := congrFun (congrFun h a) (.inr k)
    rw [single_mul_apply_of_ne _ _ _ _ _ ha, mul_single_apply_same, mul_one] at this
    exact this.symm
  · have := congrFun (congrFun h (.inl k)) b
    rw [single_mul_apply_same, mul_single_apply_of_ne _ _ _ _ _ hb, one_mul] at this
    exact this
  · have := congrFun (congrFun h (.inl k)) (.inr k)
    rw [single_mul_apply_same, mul_single_apply_same, one_mul, mul_one] at this
    exact this.symm

theorem entries_of_difference (i j : Fin n) (hij : i ≠ j)
    (h : E K (.difference i j hij) * X = X * E K (.difference i j hij)) :
    (∀ a, a ≠ .inl i → a ≠ .inr j → X a (.inr j) = 0) ∧
      (∀ b, b ≠ .inl j → b ≠ .inr i → X (.inl j) b = 0) ∧
      X (.inl j) (.inl j) = X (.inl i) (.inl i) := by
  simp only [E] at h
  refine ⟨fun a ha ha' => ?_, fun b hb hb' => ?_, ?_⟩
  · have := congrFun (congrFun h a) (.inr i)
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply, Matrix.sub_apply,
      single_mul_apply_of_ne _ _ _ _ _ ha, single_mul_apply_of_ne _ _ _ _ _ ha',
      mul_single_apply_of_ne _ _ _ _ _ Sum.inr_ne_inl, mul_single_apply_same, mul_one] at this
    simpa using this.symm
  · have := congrFun (congrFun h (.inl i)) b
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply, Matrix.sub_apply,
      single_mul_apply_same, single_mul_apply_of_ne _ _ _ _ _ Sum.inl_ne_inr,
      mul_single_apply_of_ne _ _ _ _ _ hb, mul_single_apply_of_ne _ _ _ _ _ hb', one_mul] at this
    simpa using this
  · have := congrFun (congrFun h (.inl i)) (.inl j)
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply, Matrix.sub_apply,
      single_mul_apply_same, single_mul_apply_of_ne _ _ _ _ _ Sum.inl_ne_inr,
      mul_single_apply_same, mul_single_apply_of_ne _ _ _ _ _ Sum.inl_ne_inr, one_mul,
      mul_one] at this
    simpa using this

end Entries

@[expose] def σ (k : Fin 4) : Fin 6 := ⟨k.val + 2, by omega⟩

theorem σ_injective : Function.Injective σ := fun a b h =>
  Fin.ext (by have := congrArg Fin.val h; simp only [σ] at this; omega)

section Six

variable {X : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) K}

theorem entries_inl (j : Fin 6) (hj : 2 ≤ j.val)
    (hlong : E K (.positiveLong j) * X = X * E K (.positiveLong j))
    (h0 : ∀ h0j : (0 : Fin 6) ≠ j,
      E K (.difference 0 j h0j) * X = X * E K (.difference 0 j h0j))
    (h1 : ∀ h1j : (1 : Fin 6) ≠ j,
      E K (.difference 1 j h1j) * X = X * E K (.difference 1 j h1j)) (a : Fin 6 ⊕ Fin 6) :
    X a (.inl j) = (if a = .inl j then X (.inl 0) (.inl 0) else 0) ∧
      X (.inl j) a = (if a = .inl j then X (.inl 0) (.inl 0) else 0) := by
  have h0j : (0 : Fin 6) ≠ j := fun h => by rw [← h] at hj; simp at hj
  have h1j : (1 : Fin 6) ≠ j := fun h => by rw [← h] at hj; simp at hj
  obtain ⟨hc, -, -⟩ := entries_of_long j hlong
  obtain ⟨-, hr0, hd0⟩ := entries_of_difference 0 j h0j (h0 h0j)
  obtain ⟨-, hr1, -⟩ := entries_of_difference 1 j h1j (h1 h1j)
  refine ⟨?_, ?_⟩ <;> split_ifs with ha
  · subst ha; exact hd0
  · exact hc a ha
  · subst ha; exact hd0
  · by_cases ha0 : a = .inr 0
    · subst ha0
      exact hr1 _ ha (by simp)
    · exact hr0 a ha ha0

theorem entries_inr (j : Fin 6) (hj : 2 ≤ j.val)
    (hlong : E K (.positiveLong j) * X = X * E K (.positiveLong j))
    (h0 : ∀ h0j : (0 : Fin 6) ≠ j,
      E K (.difference 0 j h0j) * X = X * E K (.difference 0 j h0j))
    (h1 : ∀ h1j : (1 : Fin 6) ≠ j,
      E K (.difference 1 j h1j) * X = X * E K (.difference 1 j h1j)) (a : Fin 6 ⊕ Fin 6) :
    X a (.inr j) = (if a = .inr j then X (.inl 0) (.inl 0) else 0) ∧
      X (.inr j) a = (if a = .inr j then X (.inl 0) (.inl 0) else 0) := by
  have h0j : (0 : Fin 6) ≠ j := fun h => by rw [← h] at hj; simp at hj
  have h1j : (1 : Fin 6) ≠ j := fun h => by rw [← h] at hj; simp at hj
  obtain ⟨-, hr, hd⟩ := entries_of_long j hlong
  obtain ⟨hc0, -, hd0⟩ := entries_of_difference 0 j h0j (h0 h0j)
  obtain ⟨hc1, -, -⟩ := entries_of_difference 1 j h1j (h1 h1j)
  refine ⟨?_, ?_⟩ <;> split_ifs with ha
  · subst ha; rw [← hd, hd0]
  · by_cases ha0 : a = .inl 0
    · subst ha0
      exact hc1 _ (by simp) ha
    · exact hc0 a ha0 ha
  · subst ha; rw [← hd, hd0]
  · exact hr a ha

end Six

section Embed

open CFSG.ClassicalInvolution.Models.SymplecticPairs

variable {X : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) K}

@[expose] def CommHyp (X : Matrix (Fin 6 ⊕ Fin 6) (Fin 6 ⊕ Fin 6) K) : Prop :=
  (∀ j : Fin 6, 2 ≤ j.val → E K (.positiveLong j) * X = X * E K (.positiveLong j)) ∧
    ∀ (i j : Fin 6) (hij : i ≠ j), i.val < 2 → 2 ≤ j.val →
      E K (.difference i j hij) * X = X * E K (.difference i j hij)

theorem CommHyp.entries (hX : CommHyp X) (c : Fin 4 ⊕ Fin 4) (a : Fin 6 ⊕ Fin 6) :
    X a (Sum.map σ σ c) = (if a = Sum.map σ σ c then X (.inl 0) (.inl 0) else 0) ∧
      X (Sum.map σ σ c) a = (if a = Sum.map σ σ c then X (.inl 0) (.inl 0) else 0) := by
  have hj : ∀ k : Fin 4, 2 ≤ (σ k).val := fun k => by simp only [σ]; omega
  rcases c with k | k
  · exact entries_inl (σ k) (hj k) (hX.1 _ (hj k)) (fun h => hX.2 0 _ h (by decide) (hj k))
      (fun h => hX.2 1 _ h (by decide) (hj k)) a
  · exact entries_inr (σ k) (hj k) (hX.1 _ (hj k)) (fun h => hX.2 0 _ h (by decide) (hj k))
      (fun h => hX.2 1 _ h (by decide) (hj k)) a

theorem mul_spIncl_eq (hX : CommHyp X) :
    X * spIncl (K := K) σ = X (.inl 0) (.inl 0) • spIncl (K := K) σ := by
  ext a c
  rw [Matrix.mul_apply, Matrix.smul_apply, spIncl_apply, smul_eq_mul]
  simp_rw [spIncl_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (Sum.map σ σ c)]
  simp only [Finset.mem_univ, ite_true]
  rw [(hX.entries c a).1]

theorem spIncl_transpose_mul_eq (hX : CommHyp X) :
    (spIncl (K := K) σ)ᵀ * X = X (.inl 0) (.inl 0) • (spIncl (K := K) σ)ᵀ := by
  ext c b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.transpose_apply, spIncl_apply, smul_eq_mul]
  simp_rw [Matrix.transpose_apply, spIncl_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (Sum.map σ σ c)]
  simp only [Finset.mem_univ, ite_true]
  rw [(hX.entries c b).2]
  by_cases h : b = Sum.map σ σ c <;> simp [h]

theorem CommHyp.commute_spEmbedMat (hX : CommHyp X)
    (g : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) :
    X * spEmbedMat σ g = spEmbedMat σ g * X := by
  have h1 := mul_spIncl_eq hX
  have h2 := spIncl_transpose_mul_eq hX
  rw [spEmbedMat]
  set P := spIncl (K := K) σ
  set c := X (.inl 0) (.inl 0)
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  calc X * (P * (g - 1) * Pᵀ) = X * P * (g - 1) * Pᵀ := by simp only [Matrix.mul_assoc]
    _ = c • (P * (g - 1) * Pᵀ) := by rw [h1, Matrix.smul_mul, Matrix.smul_mul]
    _ = P * (g - 1) * (Pᵀ * X) := by rw [h2, Matrix.mul_smul]
    _ = P * (g - 1) * Pᵀ * X := by simp only [Matrix.mul_assoc]

variable [CharP K 2]

theorem commHyp_of_commute {y : StatedSp 6 K} (hy : ∀ u ∈ uniSub 6 K, Commute u y) :
    CommHyp (mat 6 K y) := by
  refine ⟨fun j hj => E_mul_eq_of_commute (hy _ (elt_mem_uniSub ?_ 1)),
    fun i j hij hi hj => E_mul_eq_of_commute (hy _ (elt_mem_uniSub ?_ 1))⟩
  · have := j.isLt
    simp only [pos1, lvl]
    push_cast
    omega
  · simp only [pos1, lvl]
    omega

theorem commute_spEmbed {y : StatedSp 6 K} (hy : ∀ u ∈ uniSub 6 K, Commute u y)
    (g : StatedSp 4 K) : Commute (spEmbed σ σ_injective g) y := by
  apply mat_injective
  rw [map_mul, map_mul, mat_spEmbed]
  exact ((commHyp_of_commute hy).commute_spEmbedMat (mat 4 K g)).symm

end Embed

section Seventeen

variable [Finite K]

theorem exists_orderOf_eq_seventeen (hK : Nat.card K = 2) :
    ∃ g : StatedSp 4 K, orderOf g = 17 := by
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hc := LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp (K := K) 4
  rw [hK] at hc
  have : Finite (StatedSp 4 K) := Nat.finite_of_card_ne_zero (by rw [hc]; decide)
  exact exists_prime_orderOf_dvd_card' 17 (by rw [hc]; decide)

theorem exists_orderOf_eq_seventeen_commute [CharP K 2] (hK : Nat.card K = 2)
    {y : StatedSp 6 K} (hy : ∀ u ∈ uniSub 6 K, Commute u y) :
    ∃ h : StatedSp 6 K, orderOf h = 17 ∧ Commute h y := by
  obtain ⟨g, hg⟩ := exists_orderOf_eq_seventeen hK
  refine ⟨ClassicalInvolution.Models.SymplecticPairs.spEmbed σ σ_injective g, ?_,
    commute_spEmbed hy g⟩
  rw [orderOf_injective _ (ClassicalInvolution.Models.SymplecticPairs.spEmbed_injective
    σ_injective) g, hg]

end Seventeen

theorem exists_commute_of_sylow_le_centralizer {H : Type} [Group H] [Finite H] {p q : ℕ}
    [Fact p.Prime] {U : Subgroup H} (hU : IsPGroup p U)
    (hq : ∀ y : H, (∀ u ∈ U, Commute u y) → ∃ h : H, orderOf h = q ∧ Commute h y) {x : H}
    (hS : ∃ P : Sylow p H, (P : Subgroup H) ≤ Subgroup.centralizer ({x} : Set H)) :
    ∃ h : H, orderOf h = q ∧ Commute h x := by
  obtain ⟨P, hP⟩ := hS
  obtain ⟨P₁, hP₁⟩ := hU.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq H P P₁
  obtain ⟨h, hh, hc⟩ := hq (MulAut.conj g x) fun u hu => by
    have hu' := hP₁ hu
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      MulAut.smul_def] at hu'
    have hcx : Commute (MulAut.conj g⁻¹ u) x :=
      Subgroup.mem_centralizer_singleton_iff.mp (hP hu')
    have h' := hcx.map (MulAut.conj g)
    rwa [show MulAut.conj g (MulAut.conj g⁻¹ u) = u by simp [mul_assoc]] at h'
  refine ⟨MulAut.conj g⁻¹ h, by rw [MulEquiv.orderOf_eq, hh], ?_⟩
  have h' := hc.map (MulAut.conj g⁻¹)
  rwa [show MulAut.conj g⁻¹ (MulAut.conj g x) = x by simp [mul_assoc]] at h'

theorem seventeen_dvd_of_commute {H : Type} [Group H] [Finite H] {x h : H}
    (hh : orderOf h = 17) (hc : Commute h x) :
    17 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) := by
  have hmem : h ∈ Subgroup.centralizer ({x} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hc.eq
  rw [← hh, ← Subgroup.orderOf_mk h hmem]
  exact orderOf_dvd_natCard _

theorem seventeen_dvd_card_centralizer_PSp12 {H : Type} [Group H] [Finite H]
    (h : LieModel H .PSp 6 2 1) {x : H}
    (hS : ∃ P : Sylow 2 H, (P : Subgroup H) ≤ Subgroup.centralizer ({x} : Set H)) :
    17 ∣ Nat.card (Subgroup.centralizer ({x} : Set H)) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h
  have : CharP K 2 := Timmesfeld.ClassicalOrders.charP_two_of_card_eq hK
  have hK2 : Nat.card K = 2 := by rw [hK, pow_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : H ≃* StatedSp 6 K := e.trans ((QuotientGroup.quotientMulEquivOfEq
    (Timmesfeld.ClassicalOrders.statedScalars_subgroupOf_statedSp_eq_bot 6)).trans
      QuotientGroup.quotientBot)
  obtain ⟨h₁, hh₁, hc₁⟩ := exists_commute_of_sylow_le_centralizer
    ((isPGroup_uniSub (n := 6) (K := K)).map f.symm.toMonoidHom) (q := 17) (fun y hy => by
      obtain ⟨h₀, hh₀, hc₀⟩ := exists_orderOf_eq_seventeen_commute hK2 (y := f y) fun u hu => by
        simpa using (hy (f.symm u) ⟨u, hu, rfl⟩).map f.toMonoidHom
      exact ⟨f.symm h₀, by rw [MulEquiv.orderOf_eq, hh₀], by
        simpa using hc₀.map f.symm.toMonoidHom⟩) hS
  exact seventeen_dvd_of_commute hh₁ hc₁

end CFSG.LargeExtraspecial.S14.Sp12
