module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalSplit
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalConj

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open scoped Matrix

section Represents

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem Represents.mul {x y : G} {X Y : GL ι K} (hx : Represents e x X)
    (hy : Represents e y Y) : Represents e (x * y) (X * Y) := by
  obtain ⟨hxA, hXH, hX⟩ := hx
  obtain ⟨hyA, hYH, hY⟩ := hy
  refine ⟨mul_mem hxA hyA, mul_mem hXH hYH, ?_⟩
  have h1 : (⟨x * y, mul_mem hxA hyA⟩ : ↥A) = ⟨x, hxA⟩ * ⟨y, hyA⟩ := rfl
  have h2 : (⟨X * Y, mul_mem hXH hYH⟩ : ↥H) = ⟨X, hXH⟩ * ⟨Y, hYH⟩ := rfl
  rw [h1, h2, QuotientGroup.mk_mul, QuotientGroup.mk_mul, map_mul, hX, hY]

theorem Represents.inv {x : G} {X : GL ι K} (hx : Represents e x X) :
    Represents e x⁻¹ X⁻¹ := by
  obtain ⟨hxA, hXH, hX⟩ := hx
  refine ⟨inv_mem hxA, inv_mem hXH, ?_⟩
  have h1 : (⟨x⁻¹, inv_mem hxA⟩ : ↥A) = (⟨x, hxA⟩ : ↥A)⁻¹ := rfl
  have h2 : (⟨X⁻¹, inv_mem hXH⟩ : ↥H) = (⟨X, hXH⟩ : ↥H)⁻¹ := rfl
  rw [h1, h2, QuotientGroup.mk_inv, QuotientGroup.mk_inv, map_inv, hX]

theorem represents_one : Represents e (1 : G) (1 : GL ι K) := by
  refine ⟨one_mem A, one_mem H, ?_⟩
  have h1 : (⟨1, one_mem A⟩ : ↥A) = 1 := rfl
  have h2 : (⟨1, one_mem H⟩ : ↥H) = 1 := rfl
  rw [h1, h2, QuotientGroup.mk_one, map_one, QuotientGroup.mk_one]

theorem exists_represents_of_mem {X : GL ι K} (hX : X ∈ H) : ∃ a : G, Represents e a X := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm (QuotientGroup.mk ⟨X, hX⟩))
  refine ⟨a, a.2, hX, ?_⟩
  have h1 : (⟨(a : G), a.2⟩ : ↥A) = a := rfl
  rw [h1, ha, MulEquiv.apply_symm_apply]

theorem Represents.exists_scalar {x : G} {X X' : GL ι K} (hX : Represents e x X)
    (hX' : Represents e x X') : ∃ c : Kˣ, X' = X * Matrix.GeneralLinearGroup.scalar ι c := by
  obtain ⟨hx, hXH, hX⟩ := hX
  obtain ⟨hx', hXH', hX'⟩ := hX'
  have hq : (QuotientGroup.mk ⟨X, hXH⟩ : StatedProj H) = QuotientGroup.mk ⟨X', hXH'⟩ :=
    hX.symm.trans hX'
  rw [QuotientGroup.eq, mem_subgroupOf] at hq
  obtain ⟨c, hc⟩ := hq
  refine ⟨c, ?_⟩
  have h : ((⟨X, hXH⟩⁻¹ * ⟨X', hXH'⟩ : ↥H) : GL ι K) = X⁻¹ * X' := rfl
  rw [h] at hc
  rw [hc]
  group

theorem eq_one_of_odd_of_pow {M : Type*} [Monoid M] {z : M} (hodd : Odd (orderOf z)) {k : ℕ}
    (hk : z ^ 2 ^ k = 1) : z = 1 := by
  have hdvd := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf z) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem eq_of_represents (hZ : Odd (Nat.card (center ↥A))) {y y' : G} {X : GL ι K}
    (hy : Represents e y X) (hy' : Represents e y' X) {k k' : ℕ} (h2 : y ^ 2 ^ k = 1)
    (h2' : y' ^ 2 ^ k' = 1) : y = y' := by
  obtain ⟨hyA, hXH, hX⟩ := hy
  obtain ⟨hyA', hXH', hX'⟩ := hy'
  have hq : (QuotientGroup.mk ⟨y, hyA⟩ : rankTwoQuot A) = QuotientGroup.mk ⟨y', hyA'⟩ :=
    e.injective (hX.trans hX'.symm)
  rw [QuotientGroup.eq] at hq
  set z : ↥A := (⟨y, hyA⟩ : ↥A)⁻¹ * ⟨y', hyA'⟩ with hz
  have hodd : Odd (orderOf z) := by
    have h1 : orderOf (⟨z, hq⟩ : center ↥A) ∣ Nat.card (center ↥A) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hZ h1
  have hcomm : Commute (⟨y, hyA⟩ : ↥A) z := mem_center_iff.mp hq _
  have hy'eq : (⟨y', hyA'⟩ : ↥A) = ⟨y, hyA⟩ * z := by rw [hz]; group
  have e1 : (⟨y, hyA⟩ : ↥A) ^ 2 ^ (k + k') = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_add, pow_mul, h2, one_pow, Subgroup.coe_one]
  have e2 : (⟨y', hyA'⟩ : ↥A) ^ 2 ^ (k + k') = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, pow_add, mul_comm, pow_mul, h2', one_pow, Subgroup.coe_one]
  rw [hy'eq, hcomm.mul_pow, e1, one_mul] at e2
  have hz1 : z = 1 := eq_one_of_odd_of_pow hodd e2
  have h3 : (⟨y', hyA'⟩ : ↥A) = ⟨y, hyA⟩ := by rw [hy'eq, hz1, mul_one]
  exact (congrArg Subtype.val h3).symm

theorem exists_represents_sq_eq_one (hZ : Odd (Nat.card (center ↥A))) {X : GL ι K}
    (hX : X ∈ H) (hX2 : X ^ 2 = 1) : ∃ y : G, y ^ 2 = 1 ∧ Represents e y X := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e.symm (QuotientGroup.mk ⟨X, hX⟩))
  have ha2 : a ^ 2 ∈ center ↥A := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ha, ← map_pow,
      ← QuotientGroup.mk_pow]
    have : (⟨X, hX⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using hX2)
    rw [this, QuotientGroup.mk_one, map_one]
  obtain ⟨j, hj⟩ : Odd (orderOf (a ^ 2)) := by
    have h1 : orderOf (⟨a ^ 2, ha2⟩ : center ↥A) ∣ Nat.card (center ↥A) := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hZ h1
  have h1 : (a ^ 2) ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one _
  set b : ↥A := a * ((a ^ 2) ^ (j + 1))⁻¹ with hb
  have hc : Commute a ((a ^ 2) ^ (j + 1))⁻¹ := ((Commute.self_pow a 2).pow_right (j + 1)).inv_right
  have hb2 : b ^ 2 = 1 := by
    rw [hb, hc.mul_pow, inv_pow, ← pow_mul, show (j + 1) * 2 = 2 * j + 1 + 1 by ring,
      pow_succ (a ^ 2) (2 * j + 1), h1, one_mul, mul_inv_cancel]
  have hbq : (QuotientGroup.mk b : rankTwoQuot A) = QuotientGroup.mk a := by
    rw [hb, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (inv_mem (pow_mem ha2 _)),
      mul_one]
  refine ⟨b, by rw [← Subgroup.coe_pow, hb2, Subgroup.coe_one], b.2, hX, ?_⟩
  have h2 : (⟨(b : G), b.2⟩ : ↥A) = b := rfl
  rw [h2, hbq, ha, MulEquiv.apply_symm_apply]

theorem commute_of_represents (hZ : Odd (Nat.card (center ↥A))) {y y' : G} {X X' : GL ι K}
    (hy : Represents e y X) (hy' : Represents e y' X') (h2' : y' ^ 2 = 1)
    (hXX : X * X' = X' * X) : y * y' = y' * y := by
  have h1 : Represents e (y * y' * y⁻¹) X' := by
    have h := (hy.mul hy').mul hy.inv
    rwa [show X * X' * X⁻¹ = X' by rw [hXX]; group] at h
  have h3 : (y * y' * y⁻¹) ^ 2 ^ 1 = 1 := by rw [pow_one, conj_pow, h2', mul_one, mul_inv_cancel]
  have h4 := eq_of_represents hZ h1 hy' h3 (k' := 1) (by rw [pow_one]; exact h2')
  calc y * y' = (y * y' * y⁻¹) * y := by group
    _ = y' * y := by rw [h4]

end Represents

section Unipotent

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]

@[expose] def unipGL (E : Matrix ι ι K) (hE : E * E = 0) (a : K) : GL ι K where
  val := 1 + a • E
  inv := 1 - a • E
  val_inv := by simp [add_mul, mul_sub, hE]
  inv_val := by simp [sub_mul, mul_add, hE]

variable {E : Matrix ι ι K} (hE : E * E = 0)

theorem coe_unipGL (a : K) : (unipGL E hE a : Matrix ι ι K) = 1 + a • E := rfl

theorem unipGL_mul (a b : K) : unipGL E hE a * unipGL E hE b = unipGL E hE (a + b) := by
  apply Units.ext
  simp only [Units.val_mul, coe_unipGL]
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, hE, smul_zero, add_zero, add_smul]
  abel

theorem unipGL_zero : unipGL E hE 0 = 1 := Units.ext (by simp [coe_unipGL])

theorem unipGL_sq [CharP K 2] (a : K) : unipGL E hE a ^ 2 = 1 := by
  rw [sq, unipGL_mul, CharTwo.add_self_eq_zero, unipGL_zero]

theorem unipGL_ne_one {a : K} (ha : a ≠ 0) (hE0 : E ≠ 0) : unipGL E hE a ≠ 1 := by
  intro h
  have h1 := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) h
  simp only [coe_unipGL, Units.val_one, add_eq_left, smul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact ha h1
  · exact hE0 h1

theorem orderOf_unipGL [CharP K 2] {a : K} (ha : a ≠ 0) (hE0 : E ≠ 0) :
    orderOf (unipGL E hE a) = 2 :=
  orderOf_eq_prime (unipGL_sq hE a) (unipGL_ne_one hE ha hE0)

theorem commRank_unipGL {a : K} (ha : a ≠ 0) : commRank (unipGL E hE a) = E.rank := by
  rw [commRank, coe_unipGL, add_sub_cancel_left,
    Matrix.rank_smul_of_mem_nonZeroDivisors E (mem_nonZeroDivisors_of_ne_zero ha)]

theorem unipGL_comm {E' : Matrix ι ι K} (hE' : E' * E' = 0) (h12 : E * E' = 0)
    (h21 : E' * E = 0) (a b : K) :
    unipGL E hE a * unipGL E' hE' b = unipGL E' hE' b * unipGL E hE a := by
  apply Units.ext
  simp only [Units.val_mul, coe_unipGL]
  rw [add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, h12, smul_zero, add_zero,
    add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, h21, smul_zero, add_zero]
  abel

theorem unipGL_conj (D : GL ι K) {b : K}
    (hD : ((D⁻¹ : GL ι K) : Matrix ι ι K) * E * D = b • E) (a : K) :
    D⁻¹ * unipGL E hE a * D = unipGL E hE (a * b) := by
  apply Units.ext
  simp only [Units.val_mul, coe_unipGL]
  rw [mul_add, add_mul, mul_one, Units.inv_mul, mul_smul_comm, smul_mul_assoc, hD, smul_smul]

end Unipotent

section Split

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι]
  [Field K] {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem eq_zero_of_unip_eq_scalar {E : Matrix ι ι K} (hE : E * E = 0) (hE0 : E ≠ 0) {a c : K}
    (h : (1 : Matrix ι ι K) + a • E = c • 1) : a = 0 := by
  have h1 : E = c • E := by
    have := congrArg (· * E) h
    simp only [add_mul, one_mul, smul_mul_assoc, hE, smul_zero, add_zero] at this
    exact this
  have hc : c = 1 := by
    by_contra hc
    have h2 : (1 - c) • E = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact hc (sub_eq_zero.mp h3).symm
    · exact hE0 h3
  rw [hc, one_smul, add_eq_left, smul_eq_zero] at h
  exact h.resolve_right hE0

theorem splitAt_of_matrices_of [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {F : Type}
    [Field F] [Finite F] (σ : F →+* K) {p : G} {M : GL ι K} (hpM : Represents e p M)
    (hM2 : orderOf M = 2) {E₁ E₂ : Matrix ι ι K} (hsum : (M : Matrix ι ι K) - 1 = E₁ + E₂)
    (h11 : E₁ * E₁ = 0) (h12 : E₁ * E₂ = 0) (h21 : E₂ * E₁ = 0) (h22 : E₂ * E₂ = 0)
    (hv : ∃ v, E₁ *ᵥ v ≠ 0 ∧ E₂ *ᵥ v = 0) (hE₂ : E₂ ≠ 0)
    (hH₁ : ∀ a : F, unipGL E₁ h11 (σ a) ∈ H) (hH₂ : ∀ a : F, unipGL E₂ h22 (σ a) ∈ H)
    (hσ : ∀ N ∈ H, ∀ a : K, (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1) →
      ∃ d, σ d = a)
    (hD : ∀ c : F, c ≠ 0 → ∃ D ∈ H, ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₁ * D = E₁ ∧
      ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₂ * D = σ c • E₂)
    (P₁ P₂ : G → Prop)
    (hP₁ : ∀ a : F, a ≠ 0 → ∀ x : G, orderOf x = 2 → Represents e x (unipGL E₁ h11 (σ a)) →
      P₁ x)
    (hP₂ : ∀ a : F, a ≠ 0 → ∀ x : G, orderOf x = 2 → Represents e x (unipGL E₂ h22 (σ a)) →
      P₂ x) :
    SplitAt A (alphaGroup e p) (Nat.card F) P₁ P₂ := by
  classical
  obtain ⟨v, hv1, hv2⟩ := hv
  have hE₁ : E₁ ≠ 0 := fun h => hv1 (by rw [h, Matrix.zero_mulVec])
  choose ι₁ hι₁2 hι₁ using fun d : F =>
    exists_represents_sq_eq_one (e := e) hZ (hH₁ d) (unipGL_sq h11 _)
  choose ι₂ hι₂2 hι₂ using fun d : F =>
    exists_represents_sq_eq_one (e := e) hZ (hH₂ d) (unipGL_sq h22 _)
  have hι₁2' : ∀ d, ι₁ d ^ 2 ^ 1 = 1 := fun d => by rw [pow_one]; exact hι₁2 d
  have hι₂2' : ∀ d, ι₂ d ^ 2 ^ 1 = 1 := fun d => by rw [pow_one]; exact hι₂2 d
  have hι₁0 : ι₁ 0 = 1 := eq_of_represents hZ (hι₁ 0)
    (by rw [map_zero, unipGL_zero]; exact represents_one) (hι₁2' 0) (k' := 0) (by simp)
  have hι₂0 : ι₂ 0 = 1 := eq_of_represents hZ (hι₂ 0)
    (by rw [map_zero, unipGL_zero]; exact represents_one) (hι₂2' 0) (k' := 0) (by simp)
  have hcomm₁ : ∀ x y, ι₁ x * ι₁ y = ι₁ y * ι₁ x := fun x y =>
    commute_of_represents hZ (hι₁ x) (hι₁ y) (hι₁2 y)
      (by rw [unipGL_mul, unipGL_mul, add_comm])
  have hcomm₂ : ∀ x y, ι₂ x * ι₂ y = ι₂ y * ι₂ x := fun x y =>
    commute_of_represents hZ (hι₂ x) (hι₂ y) (hι₂2 y)
      (by rw [unipGL_mul, unipGL_mul, add_comm])
  have hcomm : ∀ x y, Commute (ι₁ x) (ι₂ y) := fun x y =>
    commute_of_represents hZ (hι₁ x) (hι₂ y) (hι₂2 y)
      (unipGL_comm h11 h22 h12 h21 _ _)
  have hadd₁ : ∀ x y, ι₁ (x + y) = ι₁ x * ι₁ y := by
    intro x y
    have hrep : Represents e (ι₁ x * ι₁ y) (unipGL E₁ h11 (σ (x + y))) := by
      rw [map_add, ← unipGL_mul]
      exact (hι₁ x).mul (hι₁ y)
    have hsq : (ι₁ x * ι₁ y) ^ 2 ^ 1 = 1 := by
      rw [pow_one, (show Commute (ι₁ x) (ι₁ y) from hcomm₁ x y).mul_pow, hι₁2, hι₁2, one_mul]
    exact eq_of_represents hZ (hι₁ (x + y)) hrep (hι₁2' _) hsq
  have hadd₂ : ∀ x y, ι₂ (x + y) = ι₂ x * ι₂ y := by
    intro x y
    have hrep : Represents e (ι₂ x * ι₂ y) (unipGL E₂ h22 (σ (x + y))) := by
      rw [map_add, ← unipGL_mul]
      exact (hι₂ x).mul (hι₂ y)
    have hsq : (ι₂ x * ι₂ y) ^ 2 ^ 1 = 1 := by
      rw [pow_one, (show Commute (ι₂ x) (ι₂ y) from hcomm₂ x y).mul_pow, hι₂2, hι₂2, one_mul]
    exact eq_of_represents hZ (hι₂ (x + y)) hrep (hι₂2' _) hsq
  have hscal : ∀ {y : G} {X : GL ι K}, Represents e y X → y = 1 →
      ∃ c : K, (X : Matrix ι ι K) = c • 1 := by
    intro y X hX hy1
    rw [hy1] at hX
    obtain ⟨c, hc⟩ := represents_one.exists_scalar hX
    refine ⟨c, ?_⟩
    rw [hc, one_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal]
    rfl
  have hinj₁ : ∀ x, ι₁ x = 1 → x = 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := hscal (hι₁ x) hx
    rw [coe_unipGL] at hc
    exact (map_eq_zero σ).mp (eq_zero_of_unip_eq_scalar h11 hE₁ hc)
  have hinj₂ : ∀ x, ι₂ x = 1 → x = 0 := by
    intro x hx
    obtain ⟨c, hc⟩ := hscal (hι₂ x) hx
    rw [coe_unipGL] at hc
    exact (map_eq_zero σ).mp (eq_zero_of_unip_eq_scalar h22 hE₂ hc)
  let φ : Multiplicative F →* G :=
    { toFun := fun d => ι₁ d.toAdd * ι₂ d.toAdd
      map_one' := by simp [hι₁0, hι₂0]
      map_mul' := fun a b => by
        simp only [toAdd_mul, hadd₁, hadd₂]
        calc ι₁ a.toAdd * ι₁ b.toAdd * (ι₂ a.toAdd * ι₂ b.toAdd) =
            ι₁ a.toAdd * (ι₁ b.toAdd * ι₂ a.toAdd) * ι₂ b.toAdd := by group
          _ = ι₁ a.toAdd * (ι₂ a.toAdd * ι₁ b.toAdd) * ι₂ b.toAdd := by
            rw [(hcomm b.toAdd a.toAdd).eq]
          _ = ι₁ a.toAdd * ι₂ a.toAdd * (ι₁ b.toAdd * ι₂ b.toAdd) := by group }
  have hprod : ∀ d : F, ((unipGL E₁ h11 (σ d) * unipGL E₂ h22 (σ d) : GL ι K) :
      Matrix ι ι K) = 1 + σ d • ((M : Matrix ι ι K) - 1) := by
    intro d
    simp only [Units.val_mul, coe_unipGL]
    rw [hsum, add_mul, one_mul, mul_add, mul_one, smul_mul_smul_comm, h12, smul_zero, add_zero,
      smul_add]
    abel
  have hsqd : ∀ d, (ι₁ d * ι₂ d) ^ 2 ^ 1 = 1 := fun d => by
    rw [pow_one, (hcomm d d).mul_pow, hι₁2, hι₂2, one_mul]
  have hmem : ∀ j, j ∈ alphaGroup e p ↔ ∃ d, j = ι₁ d * ι₂ d := by
    intro j
    constructor
    · intro hj
      have hle : alphaGroup e p ≤ φ.range := by
        rw [alphaGroup, closure_le]
        rintro y ⟨⟨k, hk⟩, M', N, hM', hM'2, hyN, a, ha⟩
        obtain rfl := hpM.eq_of_orderOf_eq_two hM' hM2 hM'2
        obtain ⟨d, rfl⟩ := hσ N hyN.2.1 a ha
        refine ⟨Multiplicative.ofAdd d, ?_⟩
        have hN : N = unipGL E₁ h11 (σ d) * unipGL E₂ h22 (σ d) := by
          apply Units.ext
          rw [hprod, ← ha, add_sub_cancel]
        rw [hN] at hyN
        exact eq_of_represents hZ ((hι₁ d).mul (hι₂ d)) hyN (hsqd d) hk
      obtain ⟨d, rfl⟩ := hle hj
      exact ⟨d.toAdd, rfl⟩
    · rintro ⟨d, rfl⟩
      apply Subgroup.subset_closure
      refine ⟨⟨1, hsqd d⟩, M, unipGL E₁ h11 (σ d) * unipGL E₂ h22 (σ d), hpM, hM2,
        (hι₁ d).mul (hι₂ d), σ d, ?_⟩
      rw [hprod, add_sub_cancel_left]
  refine ⟨F, inferInstance, inferInstance, ι₁, ι₂, rfl, ?_⟩
  refine
    { map_add₁ := hadd₁
      map_add₂ := hadd₂
      inj₁ := hinj₁
      inj₂ := hinj₂
      mem₁ := fun x => (hι₁ x).1
      mem₂ := fun x => (hι₂ x).1
      comm := hcomm
      inf := ?_
      mem_iff := hmem
      prop₁ := ?_
      prop₂ := ?_
      scalar := ?_ }
  ·
    intro x y hxy
    have h1 : Represents e (ι₂ y) (unipGL E₁ h11 (σ x)) := hxy ▸ hι₁ x
    obtain ⟨c, hc⟩ := h1.exists_scalar (hι₂ y)
    have h2 : (1 : Matrix ι ι K) + σ y • E₂ = (c : K) • (1 + σ x • E₁) := by
      have h := congrArg (fun N : GL ι K => (N : Matrix ι ι K)) hc
      simp only [Units.val_mul, coe_unipGL, Matrix.GeneralLinearGroup.coe_scalar] at h
      rw [h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one]
    have h3 : E₁ = (c : K) • E₁ := by
      have h := congrArg (· * E₁) h2
      simp only [add_mul, one_mul, smul_mul_assoc, h21, h11, smul_zero, add_zero] at h
      exact h
    have hc1 : (c : K) = 1 := by
      by_contra hc
      have h4 : (1 - (c : K)) • E₁ = 0 := by rw [sub_smul, one_smul, ← h3, sub_self]
      rcases smul_eq_zero.mp h4 with h5 | h5
      · exact hc (sub_eq_zero.mp h5).symm
      · exact hE₁ h5
    rw [hc1, one_smul] at h2
    have h5 : ((1 : Matrix ι ι K) + σ y • E₂) *ᵥ v = (1 + σ x • E₁) *ᵥ v := by rw [h2]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
      Matrix.smul_mulVec, hv2, smul_zero, add_zero, left_eq_add, smul_eq_zero] at h5
    exact (map_eq_zero σ).mp (h5.resolve_right hv1)
  · intro x hx
    exact hP₁ x hx _ (orderOf_eq_prime (hι₁2 x) fun h => hx (hinj₁ x h)) (hι₁ x)
  · intro x hx
    exact hP₂ x hx _ (orderOf_eq_prime (hι₂2 x) fun h => hx (hinj₂ x h)) (hι₂ x)
  · intro c hc
    obtain ⟨D, hDH, hD1, hD2⟩ := hD c hc
    obtain ⟨a, haD⟩ := exists_represents_of_mem (e := e) hDH
    refine ⟨a, haD.1, fun x => ⟨?_, ?_⟩⟩
    · have hrep : Represents e (a⁻¹ * ι₁ x * a) (unipGL E₁ h11 (σ x)) := by
        have h := (hι₁ x).conj haD.inv
        rw [inv_inv, inv_inv, unipGL_conj h11 D (b := 1) (by rw [hD1, one_smul]), mul_one] at h
        exact h
      have hsq : (a⁻¹ * ι₁ x * a) ^ 2 ^ 1 = 1 := by
        rw [pow_one, show a⁻¹ * ι₁ x * a = a⁻¹ * ι₁ x * a⁻¹⁻¹ by rw [inv_inv], conj_pow, hι₁2,
          mul_one, mul_inv_cancel]
      exact eq_of_represents hZ hrep (hι₁ x) hsq (hι₁2' x)
    · have hrep : Represents e (a⁻¹ * ι₂ x * a) (unipGL E₂ h22 (σ (c * x))) := by
        have h := (hι₂ x).conj haD.inv
        rw [inv_inv, inv_inv, unipGL_conj h22 D hD2, ← map_mul, mul_comm x c] at h
        exact h
      have hsq : (a⁻¹ * ι₂ x * a) ^ 2 ^ 1 = 1 := by
        rw [pow_one, show a⁻¹ * ι₂ x * a = a⁻¹ * ι₂ x * a⁻¹⁻¹ by rw [inv_inv], conj_pow, hι₂2,
          mul_one, mul_inv_cancel]
      exact eq_of_represents hZ hrep (hι₂ (c * x)) hsq (hι₂2' _)

theorem splitAt_of_matrices [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {F : Type} [Field F]
    [Finite F] (σ : F →+* K) {p : G} {M : GL ι K} (hpM : Represents e p M) (hM2 : orderOf M = 2)
    {E₁ E₂ : Matrix ι ι K} (hsum : (M : Matrix ι ι K) - 1 = E₁ + E₂) (h11 : E₁ * E₁ = 0)
    (h12 : E₁ * E₂ = 0) (h21 : E₂ * E₁ = 0) (h22 : E₂ * E₂ = 0)
    (hv : ∃ v, E₁ *ᵥ v ≠ 0 ∧ E₂ *ᵥ v = 0) (hE₂ : E₂ ≠ 0)
    (hH₁ : ∀ a : F, unipGL E₁ h11 (σ a) ∈ H) (hH₂ : ∀ a : F, unipGL E₂ h22 (σ a) ∈ H)
    (hσ : ∀ N ∈ H, ∀ a : K, (N : Matrix ι ι K) - 1 = a • ((M : Matrix ι ι K) - 1) →
      ∃ d, σ d = a)
    (hD : ∀ c : F, c ≠ 0 → ∃ D ∈ H, ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₁ * D = E₁ ∧
      ((D⁻¹ : GL ι K) : Matrix ι ι K) * E₂ * D = σ c • E₂) :
    SplitAt A (alphaGroup e p) (Nat.card F) (fun x => IsInvolutionOfRank e x E₁.rank)
      (fun x => IsInvolutionOfRank e x E₂.rank) := by
  have hE₁ : E₁ ≠ 0 := by
    obtain ⟨v, hv1, -⟩ := hv
    exact fun h => hv1 (by rw [h, Matrix.zero_mulVec])
  refine splitAt_of_matrices_of hZ σ hpM hM2 hsum h11 h12 h21 h22 hv hE₂ hH₁ hH₂ hσ hD _ _
    (fun a ha x hx2 hx => ?_) (fun a ha x hx2 hx => ?_)
  · have hσa : σ a ≠ 0 := (map_ne_zero σ).mpr ha
    exact ⟨hx2, unipGL E₁ h11 (σ a), hx, orderOf_unipGL h11 hσa hE₁, commRank_unipGL h11 hσa⟩
  · have hσa : σ a ≠ 0 := (map_ne_zero σ).mpr ha
    exact ⟨hx2, unipGL E₂ h22 (σ a), hx, orderOf_unipGL h22 hσa hE₂, commRank_unipGL h22 hσa⟩

end Split

end CFSG.ComponentClassification.RankTwoClassical
