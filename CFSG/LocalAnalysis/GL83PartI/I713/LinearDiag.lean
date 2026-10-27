module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace GL83.I713

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def zmodPowHom (p : ℕ) [NeZero p] {P : Type*} [Group P] (u : P) (hu : u ^ p = 1) :
    Multiplicative (ZMod p) →* P where
  toFun x := u ^ (ZMod.val (Multiplicative.toAdd x))
  map_one' := by simp
  map_mul' x y := by
    rw [toAdd_mul, ZMod.val_add,
      ← pow_eq_pow_mod (ZMod.val (Multiplicative.toAdd x) + ZMod.val (Multiplicative.toAdd y)) hu,
      pow_add]

theorem pow_prime_eq_one_multiplicative (p : ℕ) [NeZero p] (x : Multiplicative (ZMod p)) :
    x ^ p = 1 := by
  rw [← toAdd_eq_zero, toAdd_pow, nsmul_eq_mul,
    ZMod.natCast_self, zero_mul]

theorem two_le_pRank_of_commute {P : Type*} [Group P] [Finite P] {p : ℕ} (hp : p.Prime)
    {u v : P} (huv : Commute u v) (hu : u ^ p = 1) (hv : v ^ p = 1)
    (hind : ∀ i j : ℕ, u ^ i * v ^ j = 1 → p ∣ i ∧ p ∣ j) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup P) := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hp1 : 1 < p := hp.one_lt
  let g := zmodPowHom p u hu
  let h := zmodPowHom p v hv
  have hcomm : ∀ x y : Multiplicative (ZMod p), Commute (g x) (h y) := fun x y => huv.pow_pow _ _
  let F : Multiplicative (ZMod p) × Multiplicative (ZMod p) →* P := g.noncommCoprod h hcomm
  have hF_apply : ∀ x y : Multiplicative (ZMod p),
      F (x, y) = u ^ (ZMod.val (Multiplicative.toAdd x)) *
        v ^ (ZMod.val (Multiplicative.toAdd y)) :=
    fun x y => rfl
  have hF : Function.Injective F := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    rw [hF_apply] at hxy
    obtain ⟨hx, hy⟩ := hind _ _ hxy
    have hx0 : ZMod.val (Multiplicative.toAdd x) = 0 :=
      Nat.eq_zero_of_dvd_of_lt hx (ZMod.val_lt _)
    have hy0 : ZMod.val (Multiplicative.toAdd y) = 0 :=
      Nat.eq_zero_of_dvd_of_lt hy (ZMod.val_lt _)
    rw [ZMod.val_eq_zero, toAdd_eq_zero] at hx0
    rw [ZMod.val_eq_zero, toAdd_eq_zero] at hy0
    exact Prod.mk_eq_one.2 ⟨hx0, hy0⟩
  have hcard : Nat.card (Multiplicative (ZMod p) × Multiplicative (ZMod p)) = p ^ 2 := by
    rw [Nat.card_prod]
    change Nat.card (ZMod p) * Nat.card (ZMod p) = p ^ 2
    rw [Nat.card_zmod]
    ring
  have hpow : ∀ z : Multiplicative (ZMod p) × Multiplicative (ZMod p), z ^ p = 1 := by
    intro z
    ext
    · simp [pow_prime_eq_one_multiplicative p]
    · simp [pow_prime_eq_one_multiplicative p]
  exact CFSG.SectionRank.le_pRank_of_injective hp1 (fun a b => mul_comm a b) hpow hcard F hF le_top

@[expose] def diagA {n : ℕ} {K : Type*} [Field K] (x : K) (k : Fin n) : K :=
  if (k : ℕ) = 0 then x else if (k : ℕ) = 1 then x⁻¹ else 1

@[expose] def diagB {n : ℕ} {K : Type*} [Field K] (x : K) (k : Fin n) : K :=
  if (k : ℕ) = 2 then x else if (k : ℕ) = 3 then x⁻¹ else 1

theorem prod_eq_mul_of_two {n : ℕ} {M : Type*} [CommMonoid M] {i j : Fin n} (hij : i ≠ j)
    (v : Fin n → M) (hv : ∀ k, k ≠ i → k ≠ j → v k = 1) : ∏ k, v k = v i * v j := by
  rw [← Finset.prod_pair (f := v) hij]
  refine (Finset.prod_subset (Finset.subset_univ _) fun k _ hk => ?_).symm
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  exact hv k hk.1 hk.2

@[expose] def diagSL {n : ℕ} {K : Type*} [Field K] (v : Fin n → K) (hv : ∏ k, v k = 1) :
    SpecialLinearGroup (Fin n) K :=
  ⟨diagonal v, by rw [Matrix.det_diagonal, hv]⟩

theorem det_diagA {n : ℕ} {K : Type*} [Field K] (hn : 4 ≤ n) {x : K} (hx : x ≠ 0) :
    ∏ k : Fin n, diagA (n := n) x k = 1 := by
  have hne : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hv : ∀ k : Fin n, k ≠ ⟨0, by omega⟩ → k ≠ ⟨1, by omega⟩ → diagA x k = 1 := by
    intro k hk0 hk1
    have e0 : (k : ℕ) ≠ 0 := fun h => hk0 (Fin.ext h)
    have e1 : (k : ℕ) ≠ 1 := fun h => hk1 (Fin.ext h)
    simp [diagA, e0, e1]
  rw [prod_eq_mul_of_two hne (diagA x) hv]
  simp [diagA, mul_inv_cancel₀ hx]

theorem det_diagB {n : ℕ} {K : Type*} [Field K] (hn : 4 ≤ n) {x : K} (hx : x ≠ 0) :
    ∏ k : Fin n, diagB (n := n) x k = 1 := by
  have hne : (⟨2, by omega⟩ : Fin n) ≠ ⟨3, by omega⟩ := by
    intro h
    have := congrArg Fin.val h
    simp at this
  have hv : ∀ k : Fin n, k ≠ ⟨2, by omega⟩ → k ≠ ⟨3, by omega⟩ → diagB x k = 1 := by
    intro k hk2 hk3
    have e2 : (k : ℕ) ≠ 2 := fun h => hk2 (Fin.ext h)
    have e3 : (k : ℕ) ≠ 3 := fun h => hk3 (Fin.ext h)
    simp [diagB, e2, e3]
  rw [prod_eq_mul_of_two hne (diagB x) hv]
  simp [diagB, mul_inv_cancel₀ hx]

theorem diagA_pow_eq_one {n p : ℕ} {K : Type*} [Field K] {x : K} (hxp : x ^ p = 1) (k : Fin n) :
    diagA x k ^ p = 1 := by
  unfold diagA
  split_ifs <;> simp [hxp, inv_pow]

theorem diagB_pow_eq_one {n p : ℕ} {K : Type*} [Field K] {x : K} (hxp : x ^ p = 1) (k : Fin n) :
    diagB x k ^ p = 1 := by
  unfold diagB
  split_ifs <;> simp [hxp, inv_pow]

theorem diagonal_pow_mul_diagonal_apply {n : ℕ} {K : Type*} [Field K] (v w : Fin n → K)
    (i j : ℕ) (k : Fin n) : (diagonal v ^ i * diagonal w ^ j) k k = v k ^ i * w k ^ j := by
  simp [Matrix.diagonal_pow]

theorem two_mul_pow_eq_one_of {K : Type*} [Field K] {x c : K} (hx : x ≠ 0) {a : ℕ}
    (e0 : x ^ a = c) (e1 : x⁻¹ ^ a = c) : x ^ (2 * a) = 1 := by
  have hprod : x ^ a * x⁻¹ ^ a = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
  rw [two_mul, pow_add, ← hprod, e1, e0]

theorem dvd_of_dvd_two_mul {p a : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2 * a) : p ∣ a := by
  rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h2
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2) hp2
  · exact h2

theorem two_le_pRank_caseA {K : Type*} [Field K] [Finite K] {n : ℕ} (hn : 4 ≤ n) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {x : K} (hx : x ≠ 0) (hxp : x ^ p = 1)
    (hkey : ∀ m : ℕ, x ^ m = 1 → p ∣ m) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (projectiveSL n K)) := by
  obtain ⟨A, hAc⟩ : ∃ A : SpecialLinearGroup (Fin n) K,
      (A : Matrix (Fin n) (Fin n) K) = diagonal (diagA (n := n) x) :=
    ⟨diagSL (diagA (n := n) x) (det_diagA hn hx), rfl⟩
  obtain ⟨B, hBc⟩ : ∃ B : SpecialLinearGroup (Fin n) K,
      (B : Matrix (Fin n) (Fin n) K) = diagonal (diagB (n := n) x) :=
    ⟨diagSL (diagB (n := n) x) (det_diagB hn hx), rfl⟩
  have hAB : A * B = B * A := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hAc, hBc,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext k
    exact mul_comm _ _)
  have hApow : A ^ p = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hAc,
      Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact diagA_pow_eq_one hxp k)
  have hBpow : B ^ p = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hBc,
      Matrix.diagonal_pow, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact diagB_pow_eq_one hxp k)
  have hu : proj n K A ^ p = 1 := by rw [← map_pow (proj n K) A p, hApow, map_one]
  have hv : proj n K B ^ p = 1 := by rw [← map_pow (proj n K) B p, hBpow, map_one]
  have hcomm : Commute (proj n K A) (proj n K B) := by
    show proj n K A * proj n K B = proj n K B * proj n K A
    rw [← map_mul, ← map_mul, hAB]
  have hind : ∀ i j : ℕ, proj n K A ^ i * proj n K B ^ j = 1 → p ∣ i ∧ p ∣ j := by
    intro i j h
    have h' : proj n K (A ^ i * B ^ j) = 1 := by
      rw [map_mul, map_pow, map_pow]
      exact h
    rw [proj_eq_one_iff, mem_scalars] at h'
    obtain ⟨c, -, hM⟩ := h'
    have hM' : diagonal (diagA (n := n) x) ^ i * diagonal (diagB (n := n) x) ^ j
        = scalar (Fin n) (c : K) := by
      rw [← hAc, ← hBc, ← Matrix.SpecialLinearGroup.coe_pow, ← Matrix.SpecialLinearGroup.coe_pow,
        ← Matrix.SpecialLinearGroup.coe_mul]
      exact hM
    have hdiag : ∀ k : Fin n, diagA x k ^ i * diagB x k ^ j = (c : K) := by
      intro k
      have := congrFun (congrFun hM' k) k
      rw [diagonal_pow_mul_diagonal_apply, Matrix.scalar_apply, Matrix.diagonal_apply_eq] at this
      exact this
    have hx0 : x ^ i = c := by
      have := hdiag ⟨0, by omega⟩
      simpa [diagA, diagB] using this
    have hxi : x⁻¹ ^ i = c := by
      have := hdiag ⟨1, by omega⟩
      simpa [diagA, diagB] using this
    have hxj : x ^ j = c := by
      have := hdiag ⟨2, by omega⟩
      simpa [diagA, diagB] using this
    have hxj' : x⁻¹ ^ j = c := by
      have := hdiag ⟨3, by omega⟩
      simpa [diagA, diagB] using this
    exact ⟨dvd_of_dvd_two_mul hp hp2 (hkey _ (two_mul_pow_eq_one_of hx hx0 hxi)),
      dvd_of_dvd_two_mul hp hp2 (hkey _ (two_mul_pow_eq_one_of hx hxj hxj'))⟩
  exact two_le_pRank_of_commute hp hcomm hu hv hind

@[expose] def cyc3 (K : Type*) [Field K] : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, 1; 1, 0, 0; 0, 1, 0]

@[expose] def dg3 {K : Type*} [Field K] (x : K) : Matrix (Fin 3) (Fin 3) K :=
  diagonal ![1, x, x ^ 2]

theorem det_cyc3 {K : Type*} [Field K] : (cyc3 K).det = 1 := by
  simp [cyc3, Matrix.det_fin_three]

theorem cyc3_00 {K : Type*} [Field K] : cyc3 K 0 0 = 0 := by
  simp [cyc3]

theorem cyc3_sq_00 {K : Type*} [Field K] : (cyc3 K ^ 2) 0 0 = 0 := by
  simp [pow_two, cyc3, Matrix.mul_apply, Fin.sum_univ_three]

theorem cyc3_pow_three {K : Type*} [Field K] : cyc3 K ^ 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc3, pow_three, Matrix.mul_apply, Fin.sum_univ_three]

theorem prod_dg3 {K : Type*} [Field K] {x : K} (hx3 : x ^ 3 = 1) :
    ∏ k : Fin 3, (![1, x, x ^ 2] : Fin 3 → K) k = 1 := by
  rw [Fin.prod_univ_three]
  simp
  linear_combination hx3

theorem dg3_pow_three {K : Type*} [Field K] {x : K} (hx3 : x ^ 3 = 1) : dg3 x ^ 3 = 1 := by
  unfold dg3
  rw [Matrix.diagonal_pow, ← Matrix.diagonal_one]
  congr 1
  funext k
  fin_cases k
  · simp
  · simp [hx3]
  · simp
    linear_combination (x ^ 3 + 1) * hx3

theorem cyc3_mul_dg3 {K : Type*} [Field K] {x : K} (hx3 : x ^ 3 = 1) :
    cyc3 K * dg3 x = scalar (Fin 3) (x ^ 2) * (dg3 x * cyc3 K) := by
  have h1 : x ^ 2 * x = 1 := by linear_combination hx3
  have h2 : x ^ 2 * x ^ 2 = x := by linear_combination x * hx3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cyc3, dg3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, h1, h2]

theorem two_le_pRank_caseB {K : Type*} [Field K] [Finite K] {x : K} (hx : x ≠ 0)
    (hx3 : x ^ 3 = 1) (hkey : ∀ m : ℕ, x ^ m = 1 → 3 ∣ m) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (projectiveSL 3 K)) := by
  obtain ⟨D, hDc⟩ : ∃ D : SpecialLinearGroup (Fin 3) K,
      (D : Matrix (Fin 3) (Fin 3) K) = dg3 x :=
    ⟨diagSL ![1, x, x ^ 2] (prod_dg3 hx3), rfl⟩
  obtain ⟨C, hCc⟩ : ∃ C : SpecialLinearGroup (Fin 3) K,
      (C : Matrix (Fin 3) (Fin 3) K) = cyc3 K :=
    ⟨⟨cyc3 K, det_cyc3⟩, rfl⟩
  have hs3 : (Units.mk0 x hx ^ 2) ^ 3 = 1 := by
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    rw [pow_right_comm, hx3, one_pow]
  obtain ⟨s, hsM, hsmem⟩ : ∃ s : SpecialLinearGroup (Fin 3) K,
      (s : Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (x ^ 2) ∧ s ∈ scalars 3 K :=
    ⟨scalarElement (Units.mk0 x hx ^ 2) hs3, by simp, scalarElement_mem_scalars _ _⟩
  have hDpow : D ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hDc]
    exact dg3_pow_three hx3)
  have hCpow : C ^ 3 = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hCc]
    exact cyc3_pow_three)
  have hCDs : C * D = s * (D * C) := Subtype.ext (by
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    rw [hsM, hCc, hDc]
    exact cyc3_mul_dg3 hx3)
  have hu : proj 3 K D ^ 3 = 1 := by rw [← map_pow (proj 3 K) D 3, hDpow, map_one]
  have hv : proj 3 K C ^ 3 = 1 := by rw [← map_pow (proj 3 K) C 3, hCpow, map_one]
  have hcomm : Commute (proj 3 K D) (proj 3 K C) := by
    show proj 3 K D * proj 3 K C = proj 3 K C * proj 3 K D
    rw [← map_mul, ← map_mul, hCDs, map_mul (proj 3 K) s (D * C), proj_eq_one_iff.2 hsmem,
      one_mul]
  have hind : ∀ i j : ℕ, proj 3 K D ^ i * proj 3 K C ^ j = 1 → 3 ∣ i ∧ 3 ∣ j := by
    intro i j h
    have h' : proj 3 K (D ^ i * C ^ j) = 1 := by
      rw [map_mul, map_pow, map_pow]
      exact h
    rw [proj_eq_one_iff, mem_scalars] at h'
    obtain ⟨c, -, hM⟩ := h'
    have hM' : dg3 x ^ i * cyc3 K ^ j = scalar (Fin 3) (c : K) := by
      rw [← hDc, ← hCc, ← Matrix.SpecialLinearGroup.coe_pow, ← Matrix.SpecialLinearGroup.coe_pow,
        ← Matrix.SpecialLinearGroup.coe_mul]
      exact hM
    rw [pow_eq_pow_mod j cyc3_pow_three] at hM'
    have hcases : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · rw [h0, pow_zero, mul_one] at hM'
      have e0 : (1 : K) = (c : K) := by
        have := congrFun (congrFun hM' 0) 0
        simpa [dg3, Matrix.diagonal_pow, Matrix.scalar_apply] using this
      have e1 : x ^ i = (c : K) := by
        have := congrFun (congrFun hM' 1) 1
        simpa [dg3, Matrix.diagonal_pow, Matrix.scalar_apply] using this
      have hxi : x ^ i = 1 := by rw [e1, ← e0]
      exact ⟨hkey i hxi, Nat.dvd_of_mod_eq_zero h0⟩
    · exfalso
      rw [h1, pow_one] at hM'
      have e : (0 : K) = (c : K) := by
        have := congrFun (congrFun hM' 0) 0
        simpa [dg3, Matrix.diagonal_pow, Matrix.diagonal_mul, Matrix.scalar_apply,
          cyc3_00] using this
      exact Units.ne_zero c e.symm
    · exfalso
      rw [h2] at hM'
      have e : (0 : K) = (c : K) := by
        have := congrFun (congrFun hM' 0) 0
        simpa [dg3, Matrix.diagonal_pow, Matrix.diagonal_mul, Matrix.scalar_apply,
          cyc3_00, cyc3_sq_00] using this
      exact Units.ne_zero c e.symm
  exact two_le_pRank_of_commute Nat.prime_three hcomm hu hv hind

theorem two_le_pRank_projectiveSL_of_dvd {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ Nat.gcd n (Nat.card K - 1)) :
    2 ≤ CFSG.Open.pRank p
      (⊤ : Subgroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL n K)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvdK : p ∣ Nat.card Kˣ := by
    rw [Nat.card_units]
    exact hpd.trans (Nat.gcd_dvd_right _ _)
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' p hdvdK
  have hωK : (ω : K) ^ p = 1 := by
    have h := congrArg Units.val (pow_orderOf_eq_one ω)
    rw [hω] at h
    simpa using h
  have hkey : ∀ m : ℕ, (ω : K) ^ m = 1 → p ∣ m := by
    intro m hm
    rw [← hω, orderOf_dvd_iff_pow_eq_one]
    ext
    simpa using hm
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · have hn3 : n = 3 := by omega
    subst hn3
    have hp3 : p = 3 := by
      have h3 : p ∣ 3 := hpd.trans (Nat.gcd_dvd_left _ _)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h3
    subst hp3
    exact two_le_pRank_caseB (Units.ne_zero ω) hωK hkey
  · exact two_le_pRank_caseA hge hp hp2 (Units.ne_zero ω) hωK hkey

end GL83.I713

end

