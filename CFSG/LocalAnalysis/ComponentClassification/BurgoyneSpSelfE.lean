module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBInvolution

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.Sp

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.TBLit CFSG.ComponentClassification.Burgoyne.PSL
open CFSG.ComponentClassification.Burgoyne.Proj
open scoped commutatorElement MatrixGroups

variable {r : ℕ} {K : Type} [Field K]

theorem pow_orderOf_succ_commute [Finite K] (hr : 1 ≤ r) {A D : gsp r K} {d : K} (hd : d ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hc : conjAut r K D * conjAut r K A = conjAut r K A * conjAut r K D)
    (hodd : Odd (orderOf (conjAut r K D))) :
    (((D ^ (orderOf (conjAut r K D) + 1) : gsp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        (((D ^ (orderOf (conjAut r K D) + 1) : gsp r K) : GL (Fin r ⊕ Fin r) K) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  set a : GL (Fin r ⊕ Fin r) K := (A : GL (Fin r ⊕ Fin r) K) with ha
  set x : GL (Fin r ⊕ Fin r) K := (D : GL (Fin r ⊕ Fin r) K) with hx
  have hcent : ∀ (c : Kˣ) (g : GL (Fin r ⊕ Fin r) K),
      GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c * g =
        g * GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c := fun c g => by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  have h1 : conjAut r K (D * A * D⁻¹ * A⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  obtain ⟨κ, hκ⟩ := (conjAut_eq_one_iff hr _).1 h1
  set sc := GeneralLinearGroup.scalar (Fin r ⊕ Fin r) κ with hsc
  have hκ' : x * a * x⁻¹ * a⁻¹ = sc := hκ
  have hxa : x * a = sc * a * x := by
    calc x * a = (x * a * x⁻¹ * a⁻¹) * a * x := by group
      _ = sc * a * x := by rw [hκ']
  have hpow : ∀ m : ℕ, x ^ m * a = sc ^ m * a * x ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc x ^ (m + 1) * a = x ^ m * (x * a) := by rw [pow_succ, mul_assoc]
        _ = x ^ m * (sc * a * x) := by rw [hxa]
        _ = sc * (x ^ m * a) * x := by
            rw [← mul_assoc, ← mul_assoc, ← hcent κ (x ^ m)]
            simp only [mul_assoc]
            rfl
        _ = sc ^ (m + 1) * a * x ^ (m + 1) := by
            rw [ih, pow_succ', pow_succ]
            group
  have haa : a * a = GeneralLinearGroup.scalar (Fin r ⊕ Fin r) (Units.mk0 d hd) := by
    apply Units.ext
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar]
    exact hAA.trans (by rw [Matrix.smul_one_eq_diagonal]; rfl)
  have hsq : sc ^ 2 = 1 := by
    have e1 : x * (a * a) = sc ^ 2 * (a * a) * x := by
      rw [← mul_assoc, hxa]
      calc sc * a * x * a = sc * a * (x * a) := by group
        _ = sc * a * (sc * a * x) := by rw [hxa]
        _ = sc ^ 2 * (a * a) * x := by
            rw [pow_two]
            have := hcent κ a
            calc sc * a * (sc * a * x) = sc * (a * sc) * a * x := by group
              _ = sc * (sc * a) * a * x := by rw [this]
              _ = sc * sc * (a * a) * x := by group
    have e2 : x * (a * a) = (a * a) * x := by rw [haa, (hcent _ x).symm]
    rw [e2] at e1
    have e3 : sc ^ 2 * ((a * a) * x) = 1 * ((a * a) * x) := by
      rw [← mul_assoc, one_mul]
      exact e1.symm
    exact mul_right_cancel e3
  obtain ⟨m, hm⟩ := hodd
  have hk : orderOf (conjAut r K D) + 1 = 2 * (m + 1) := by omega
  have e : x ^ (orderOf (conjAut r K D) + 1) * a = a * x ^ (orderOf (conjAut r K D) + 1) := by
    rw [hpow, hk, pow_mul, hsq, one_pow, one_mul]
  have e' := congrArg Units.val e
  simpa only [Units.val_mul, Subgroup.coe_pow, hx, ha] using e'

theorem conjAut_pow_orderOf_succ (D : gsp r K) :
    conjAut r K (D ^ (orderOf (conjAut r K D) + 1)) = conjAut r K D := by
  rw [map_pow, pow_succ, pow_orderOf_eq_one, one_mul]

theorem exists_commute_of_odd [Finite K] (hr : 1 ≤ r) {A D : gsp r K} {d : K} (hd : d ≠ 0)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hc : conjAut r K D * conjAut r K A = conjAut r K A * conjAut r K D)
    (hodd : Odd (orderOf (conjAut r K D))) :
    ∃ D' : gsp r K, (∃ m : ℕ, D' = D ^ m) ∧ conjAut r K D' = conjAut r K D ∧
      ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) :=
  ⟨_, ⟨_, rfl⟩, conjAut_pow_orderOf_succ D, pow_orderOf_succ_commute hr hd hAA hc hodd⟩

abbrev bJ (u w : Fin r ⊕ Fin r → K) : K := (u ᵥ* formJ r K) ⬝ᵥ w

theorem bJ_eq (u w : Fin r ⊕ Fin r → K) : bJ u w = pairedSympForm K r u w := by
  rw [bJ, pairedSympForm_eq, dotProduct_mulVec]

theorem bJ_swap (u w : Fin r ⊕ Fin r → K) : bJ u w = -bJ w u := by
  rw [bJ_eq, bJ_eq]
  exact (LinearMap.BilinForm.IsAlt.neg_eq pairedSympForm_isAlt w u).symm

theorem formJ_mulVec (u : Fin r ⊕ Fin r → K) : formJ r K *ᵥ u = -(u ᵥ* formJ r K) := by
  rw [← vecMul_transpose, formJ_transpose, vecMul_neg]

abbrev symN (a b : Fin r ⊕ Fin r → K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  vecMulVec a (b ᵥ* formJ r K) + vecMulVec b (a ᵥ* formJ r K)

theorem vecMulVec_mulVec' {ι : Type} [Fintype ι] (u w x : ι → K) :
    vecMulVec u w *ᵥ x = (w ⬝ᵥ x) • u := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem symN_mulVec (a b x : Fin r ⊕ Fin r → K) :
    symN a b *ᵥ x = bJ b x • a + bJ a x • b := by
  rw [symN, add_mulVec, vecMulVec_mulVec', vecMulVec_mulVec']

theorem symN_conds {a b : Fin r ⊕ Fin r → K} (hab : bJ a b = 0) :
    (symN a b)ᵀ * formJ r K + formJ r K * symN a b = 0 ∧
      (symN a b)ᵀ * formJ r K * symN a b = 0 ∧ symN a b * symN a b = 0 := by
  have haa : (a ᵥ* formJ r K) ⬝ᵥ a = 0 := vecMul_formJ_dotProduct_self a
  have hbb : (b ᵥ* formJ r K) ⬝ᵥ b = 0 := vecMul_formJ_dotProduct_self b
  have hab' : (a ᵥ* formJ r K) ⬝ᵥ b = 0 := hab
  have hba : (b ᵥ* formJ r K) ⬝ᵥ a = 0 := by
    have := bJ_swap b a
    rw [hab, neg_zero] at this
    exact this
  have e1 : (symN a b)ᵀ * formJ r K =
      vecMulVec (b ᵥ* formJ r K) (a ᵥ* formJ r K) +
        vecMulVec (a ᵥ* formJ r K) (b ᵥ* formJ r K) := by
    rw [symN, transpose_add, transpose_vecMulVec, transpose_vecMulVec, Matrix.add_mul,
      vecMulVec_mul, vecMulVec_mul]
  have e2 : formJ r K * symN a b =
      -(vecMulVec (a ᵥ* formJ r K) (b ᵥ* formJ r K) +
        vecMulVec (b ᵥ* formJ r K) (a ᵥ* formJ r K)) := by
    rw [symN, Matrix.mul_add, mul_vecMulVec, mul_vecMulVec, formJ_mulVec, formJ_mulVec]
    ext i j
    simp only [Matrix.add_apply, Matrix.neg_apply, vecMulVec_apply, Pi.neg_apply]
    ring
  refine ⟨by rw [e1, e2, add_comm (vecMulVec (b ᵥ* formJ r K) _), add_neg_cancel], ?_, ?_⟩
  · rw [e1, symN, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, vecMulVec_mul_vecMulVec,
      vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, haa, hab', hba,
      hbb]
    simp
  · rw [symN, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, vecMulVec_mul_vecMulVec,
      vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, vecMulVec_mul_vecMulVec, haa, hab', hba,
      hbb]
    simp

@[expose] def symSp {a b : Fin r ⊕ Fin r → K} (hab : bJ a b = 0) (c : K) : StatedSp r K :=
  unipSp (symN_conds hab).1 (symN_conds hab).2.1 (symN_conds hab).2.2 c

theorem coe_symSp {a b : Fin r ⊕ Fin r → K} (hab : bJ a b = 0) (c : K) :
    (((symSp hab c : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + c • symN a b :=
  rfl

section NonSplit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι K} {d : K}

theorem quadMul_conj (hMM : M * M = d • 1) (c₁ c₂ : K) :
    (c₁ • 1 + c₂ • M) * (c₁ • 1 - c₂ • M) = (c₁ ^ 2 - c₂ ^ 2 * d) • 1 := by
  have h : (c₂ • M) * (c₂ • M) = (c₂ ^ 2 * d) • 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hMM, smul_smul, smul_smul, pow_two]
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, h]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  rw [mul_comm c₂ c₁]
  module

theorem norm_ne_zero (hd : ∀ l : K, l ^ 2 ≠ d) {c₁ c₂ : K} (h : c₁ ≠ 0 ∨ c₂ ≠ 0) :
    c₁ ^ 2 - c₂ ^ 2 * d ≠ 0 := by
  intro h0
  rcases h with h | h
  · by_cases hc₂ : c₂ = 0
    · rw [hc₂] at h0
      simp at h0
      exact h h0
    · apply hd (c₁ / c₂)
      field_simp
      linear_combination h0
  · apply hd (c₁ / c₂)
    field_simp
    linear_combination h0

theorem eq_zero_of_add_smul (hd : ∀ l : K, l ^ 2 ≠ d) (hMM : M * M = d • 1) {v : ι → K}
    (hv : v ≠ 0) {p q : K} (h : p • v + q • (M *ᵥ v) = 0) : p = 0 ∧ q = 0 := by
  by_contra hpq
  rw [not_and_or] at hpq
  have hn := norm_ne_zero hd (c₁ := p) (c₂ := q) (by tauto)
  apply hv
  have e : (p • 1 - q • M) *ᵥ ((p • 1 + q • M) *ᵥ v) = (p ^ 2 - q ^ 2 * d) • v := by
    rw [mulVec_mulVec]
    have h1 : (p • (1 : Matrix ι ι K) - q • M) * (p • 1 + q • M) =
        (p ^ 2 - (-q) ^ 2 * d) • 1 := by
      rw [← quadMul_conj hMM p (-q), neg_smul, sub_neg_eq_add, sub_eq_add_neg, ← neg_smul]
    rw [h1, neg_sq, smul_mulVec, one_mulVec]
  have h' : (p • 1 + q • M) *ᵥ v = 0 := by
    rw [add_mulVec, smul_mulVec, smul_mulVec, one_mulVec]
    exact h
  rw [h', mulVec_zero] at e
  exact (smul_eq_zero.1 e.symm).resolve_left hn

theorem exists_eq_add_smul [Nonempty ι] (hd : ∀ l : K, l ^ 2 ≠ d) (hMM : M * M = d • 1)
    {D : Matrix ι ι K} (hDM : D * M = M * D)
    (h : ∀ v, ∃ p q : K, D *ᵥ v = p • v + q • (M *ᵥ v)) :
    ∃ α β : K, D = α • 1 + β • M := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  set v₀ : ι → K := Pi.single i 1 with hv₀
  have hv₀0 : v₀ ≠ 0 := by
    intro h0
    have := congrFun h0 i
    simp [hv₀] at this
  obtain ⟨α, β, hαβ⟩ := h v₀
  refine ⟨α, β, ?_⟩
  set D' := D - (α • 1 + β • M) with hD'
  have hD'M : D' * M = M * D' := by
    rw [hD', Matrix.sub_mul, Matrix.mul_sub, hDM, Matrix.add_mul, Matrix.mul_add]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hD'v₀ : D' *ᵥ v₀ = 0 := by
    rw [hD', sub_mulVec, hαβ, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, sub_self]
  have hD'Mv₀ : D' *ᵥ (M *ᵥ v₀) = 0 := by
    rw [mulVec_mulVec, hD'M, ← mulVec_mulVec, hD'v₀, mulVec_zero]
  have hD'h : ∀ v, ∃ p q : K, D' *ᵥ v = p • v + q • (M *ᵥ v) := by
    intro v
    obtain ⟨p, q, hpq⟩ := h v
    refine ⟨p - α, q - β, ?_⟩
    rw [hD', sub_mulVec, hpq, add_mulVec, smul_mulVec, smul_mulVec, one_mulVec, sub_smul,
      sub_smul]
    abel
  have hzero : ∀ v, D' *ᵥ v = 0 := by
    intro v
    by_cases hv : v = 0
    · rw [hv, mulVec_zero]
    obtain ⟨p, q, hpq⟩ := hD'h v
    obtain ⟨p', q', hpq'⟩ := hD'h (v + v₀)
    rw [mulVec_add, hD'v₀, add_zero, mulVec_add] at hpq'
    have hst : (p - p') • v + (q - q') • (M *ᵥ v) = p' • v₀ + q' • (M *ᵥ v₀) := by
      rw [hpq] at hpq'
      rw [sub_smul, sub_smul]
      rw [smul_add, smul_add] at hpq'
      linear_combination (norm := module) hpq'
    have happ : (p - p') • (D' *ᵥ v) + (q - q') • (M *ᵥ (D' *ᵥ v)) = 0 := by
      have := congrArg (D' *ᵥ ·) hst
      simp only [mulVec_add, mulVec_smul, hD'v₀, hD'Mv₀, smul_zero, add_zero] at this
      rw [mulVec_mulVec, hD'M, ← mulVec_mulVec] at this
      exact this
    have hMMv : M *ᵥ (M *ᵥ v) = d • v := by rw [mulVec_mulVec, hMM, smul_mulVec, one_mulVec]
    rw [hpq, mulVec_add, mulVec_smul, mulVec_smul, hMMv] at happ
    have e2 : ((p - p') * p + (q - q') * q * d) • v + ((p - p') * q + (q - q') * p) • (M *ᵥ v) =
        0 := by
      rw [← happ]
      module
    obtain ⟨e3, e4⟩ := eq_zero_of_add_smul hd hMM hv e2
    by_cases hst0 : p - p' = 0 ∧ q - q' = 0
    · obtain ⟨h1, h2⟩ := hst0
      rw [h1, h2, zero_smul, zero_smul, add_zero] at hst
      obtain ⟨h3, h4⟩ := eq_zero_of_add_smul hd hMM hv₀0 hst.symm
      rw [hpq, show p = 0 by linear_combination h1 + h3, show q = 0 by linear_combination h2 + h4,
        zero_smul, zero_smul, add_zero]
    · have hn := norm_ne_zero hd (c₁ := p - p') (c₂ := q - q') (by tauto)
      have hp : p = 0 := by
        have : (((p - p') ^ 2 - (q - q') ^ 2 * d)) * p = 0 := by
          linear_combination (p - p') * e3 - (q - q') * d * e4
        exact (mul_eq_zero.1 this).resolve_left hn
      have hq : q = 0 := by
        have : (((p - p') ^ 2 - (q - q') ^ 2 * d)) * q = 0 := by
          linear_combination (p - p') * e4 - (q - q') * e3
        exact (mul_eq_zero.1 this).resolve_left hn
      rw [hpq, hp, hq, zero_smul, zero_smul, add_zero]
  have : D' = 0 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, hzero v, map_zero, LinearMap.zero_apply]
  rw [hD'] at this
  exact sub_eq_zero.1 this

end NonSplit

section SelfE

variable {A : gsp r K}

theorem bJ_mulVec_left (hJA : ((A : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K =
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (u w : Fin r ⊕ Fin r → K) :
    bJ (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u) w =
      bJ u (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w) := by
  rw [bJ, bJ, ← vecMul_transpose, vecMul_vecMul, hJA, ← vecMul_vecMul, dotProduct_mulVec]

theorem exists_dual_pair {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hJA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K =
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    {v : Fin r ⊕ Fin r → K} (hv : v ≠ 0) :
    ∃ x, bJ v x = 0 ∧
      bJ (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) x = 1 := by
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  obtain ⟨b, hb⟩ : ∃ b, (v ᵥ* formJ r K) b ≠ 0 := by
    by_contra h
    push Not at h
    exact vecMul_formJ_ne_zero hv (funext h)
  set y : Fin r ⊕ Fin r → K := Pi.single b 1 with hy
  set a₁ := bJ v y with ha₁
  set b₁ := bJ v (M *ᵥ y) with hb₁
  have ha₁0 : a₁ ≠ 0 := by
    rw [ha₁, bJ, hy, dotProduct_single, mul_one]
    exact hb
  have hn : d * a₁ ^ 2 - b₁ ^ 2 ≠ 0 := by
    intro h0
    apply hd (b₁ / a₁)
    field_simp
    linear_combination -h0
  have hMMy : M *ᵥ (M *ᵥ y) = d • y := by rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  refine ⟨(a₁ / (d * a₁ ^ 2 - b₁ ^ 2)) • (M *ᵥ y - (b₁ / a₁) • y), ?_, ?_⟩
  · rw [bJ, dotProduct_smul, dotProduct_sub, dotProduct_smul]
    change (a₁ / (d * a₁ ^ 2 - b₁ ^ 2)) • (b₁ - (b₁ / a₁) • a₁) = 0
    rw [smul_eq_mul, smul_eq_mul, div_mul_cancel₀ _ ha₁0, sub_self, mul_zero]
  · rw [bJ_mulVec_left hJA, mulVec_smul, mulVec_sub, mulVec_smul, hMMy, bJ, dotProduct_smul,
      dotProduct_sub, dotProduct_smul, dotProduct_smul]
    change (a₁ / (d * a₁ ^ 2 - b₁ ^ 2)) • (d • a₁ - (b₁ / a₁) • b₁) = 1
    simp only [smul_eq_mul]
    rw [div_mul_eq_mul_div, div_eq_one_iff_eq hn]
    field_simp

theorem symN_commute {d : K}
    (hJA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K =
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (v : Fin r ⊕ Fin r → K) :
    ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        symN (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) v =
      symN (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) v *
        ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hMMv : M *ᵥ (M *ᵥ v) = d • v := by rw [mulVec_mulVec, hAA, smul_mulVec, one_mulVec]
  have hvJM : ∀ u : Fin r ⊕ Fin r → K, (u ᵥ* formJ r K) ᵥ* M = (M *ᵥ u) ᵥ* formJ r K := by
    intro u
    rw [vecMul_vecMul, ← hJA, ← vecMul_vecMul, vecMul_transpose]
  rw [symN, Matrix.mul_add, Matrix.add_mul, mul_vecMulVec, mul_vecMulVec, vecMulVec_mul,
    vecMulVec_mul, hvJM, hvJM, hMMv, add_comm]
  ext i j
  simp [vecMulVec_apply, smul_vecMul]

theorem isQuasisimple_spCent_nonsplit [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r)
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • formJ r K) :
    IsQuasisimple (spCent r K A) := by
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  have hAns' : ∀ c : K, ((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) ≠ c • 1 :=
    CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) = d * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude hJ]
  obtain ⟨-, -, hnonsplit⟩ := UnitaryHigher.odd_symplectic_scalar_square_centralizer_structure hℓ
    hℓ2 hf hKc (V := Fin r ⊕ Fin r → K) (r := r) (by omega) finrank_standard
    pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate hAns' hd0
    (linA_mul_self hAA) hAμ
  obtain ⟨-, hF, hcard, hfinrank, -, -, -, -, hpos, -⟩ := hnonsplit hd
  obtain ⟨BE, -, hBEalt, hBEnd, -, hiff⟩ := hpos (div_self hd0)
  let : Field (UnitaryHigher.scalarSquareField ((linA A : LinearMap.GeneralLinearGroup K
    (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K))) := hF.toField
  have hEodd : Odd (Nat.card (UnitaryHigher.scalarSquareField ((linA A :
      LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)))) := by
    rw [hcard]
    exact ((hℓ.odd_of_ne_two hℓ2).pow).pow
  have := CatalogueBSymplecticB.finite_of_odd_card hEodd
  have : Module.Finite (UnitaryHigher.scalarSquareField ((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K))) (Fin r ⊕ Fin r → K) :=
    CatalogueBOrthogonalScalarSquareField.evaluationModule_finite _
  have h3 : Nat.card (UnitaryHigher.scalarSquareField ((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K))) ≠ 3 := by
    rw [hcard]
    intro h
    have h1 : 2 ≤ ℓ ^ f := hℓ.two_le.trans (Nat.le_self_pow (by omega) ℓ)
    nlinarith
  have hq := CatalogueBAlternatingIsometry.isometry_quasisimple BE hBEalt hBEnd
    (by rw [hfinrank]; exact hr) hEodd (Or.inr h3)
  exact LocalCores.isQuasisimple_of_mulEquiv
    ((CatalogueBSymplecticB.evaluationIsometryEquiv _ _
      (CatalogueBAlternatingIsometry.isometryGroup BE) (fun φ => ∀ v w, BE (φ v) (φ w) = BE v w)
      (CatalogueBAlternatingIsometry.mem_isometryGroup_iff BE) hiff).symm.trans
      ((CatalogueBSymplecticB.centralizerSimilitudeEquiv _ _).trans (spCentEquiv A).symm)) hq

theorem bJ_mulVec_self (h2 : (2 : K) ≠ 0)
    (hJA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K =
      formJ r K * ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K))
    (v : Fin r ⊕ Fin r → K) :
    bJ (((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) v = 0 := by
  have h1 := bJ_mulVec_left hJA v v
  have h3 := bJ_swap v (((A : GL (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v)
  have : (2 : K) * bJ (((A : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ v) v = 0 := by
    linear_combination h1 + h3
  exact (mul_eq_zero.1 this).resolve_left h2

theorem exists_ne_zero_entry {ι : Type} {N : Matrix ι ι K} (hN : N ≠ 0) :
    ∃ a b, N a b ≠ 0 := by
  by_contra h
  push Not at h
  exact hN (Matrix.ext h)

theorem nonsplitSelf_oddCoreIn_eq_bot [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (hf : 1 ≤ f) (hKc : Nat.card K = ℓ ^ f) (hr : 2 ≤ r)
    (hinj : Function.Injective
      (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))))
    {B : Subgroup (MulAut (StatedProj (StatedSp r K)))}
    (hB : (MulAut.conj : StatedProj (StatedSp r K) →* MulAut (StatedProj (StatedSp r K))).range ≤
      B)
    (hAns : ∀ c : Kˣ, (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c)
    {d : K} (hd : ∀ l : K, l ^ 2 ≠ d)
    (hAA : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • 1)
    (hJ : ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)ᵀ * formJ r K *
      ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = d • formJ r K) :
    oddCoreIn B (conjAut r K A) = ⊥ := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have : NeZero r := ⟨by omega⟩
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have hd0 : d ≠ 0 := fun h => hd 0 (by rw [h]; ring)
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hJA : Mᵀ * formJ r K = formJ r K * M := transpose_mul_formJ hd0 hJ hAA
  have hq := isQuasisimple_spCent_nonsplit hℓ hℓ2 hf hKc hr hAns hd hAA hJ
  have hqim := isQuasisimple_map_conjProjH hinj hq
  have hmem : ∀ v c, symSp (bJ_mulVec_self h2 hJA v) c ∈ spCent r K A := by
    intro v c
    rw [mem_spCent, coe_symSp, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.mul_smul, Matrix.smul_mul, symN_commute hJA hAA v]
  rw [eq_bot_iff]
  intro y hy
  rw [mem_bot]
  have hoddy := odd_orderOf_of_mem_oddCoreIn hy
  have hyt := commute_of_mem_oddCoreIn hy
  obtain ⟨D, τ, rfl⟩ := CatalogueBSymplecticRepresentation.automorphism_standard hK hr y
  have hfix : ∀ g ∈ spCent r K A, (conjAut r K D * fieldAut r K τ) (proj r K g) = proj r K g :=
    fun g hg => commute_oddCoreIn_of_normal hinj hB (conjSp r K A).toMonoidHom (conjAut_proj A)
      le_rfl (fun f hf q hq' => mul_mem (mul_mem hf hq') (inv_mem hf)) hqim hy hg
  have hperf := commutator_eq_self_of_isQuasisimple hq
  set Dm := ((D : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hDm
  have key : ∀ v : Fin r ⊕ Fin r → K, v ≠ 0 → τ = 1 ∧
      Dm * symN (M *ᵥ v) v = symN (M *ᵥ v) v * Dm := by
    intro v hv
    obtain ⟨x, hx1, hx2⟩ := exists_dual_pair hd hJA hAA hv
    have hNx : symN (M *ᵥ v) v *ᵥ x = v := by
      rw [symN_mulVec, hx1, hx2, zero_smul, one_smul, zero_add]
    have hN0 : symN (M *ᵥ v) v ≠ 0 := by
      intro h0
      rw [h0, zero_mulVec] at hNx
      exact hv hNx.symm
    obtain ⟨a, b, hab⟩ := exists_ne_zero_entry hN0
    refine fix_unipotent_family_matrix hab fun c => ?_
    have h := semilinear_eq_of_fix hperf hfix (hmem v c)
    rwa [coe_symSp, map_one_add_smul] at h
  obtain ⟨v₁, hv₁⟩ : ∃ v₁ : Fin r ⊕ Fin r → K, v₁ ≠ 0 :=
    ⟨Pi.single (Sum.inl ⟨0, by omega⟩) 1, fun h => by
      have := congrFun h (Sum.inl ⟨0, by omega⟩)
      simp at this⟩
  have hτ := (key v₁ hv₁).1
  rw [hτ, map_one, mul_one] at hoddy hyt ⊢
  obtain ⟨D', ⟨m, hm⟩, hD'D, hD'A⟩ := exists_commute_of_odd (by omega) hd0 hAA hyt hoddy
  rw [← hD'D] at hoddy ⊢
  set Dm' := ((D' : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    with hDm'
  have hDm'pow : Dm' = Dm ^ m := by
    rw [hDm', hm, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  have key' : ∀ v : Fin r ⊕ Fin r → K, v ≠ 0 →
      Dm' * symN (M *ᵥ v) v = symN (M *ᵥ v) v * Dm' := by
    intro v hv
    rw [hDm'pow]
    exact (Commute.pow_left (key v hv).2 m).eq
  have hspan : ∀ v, ∃ p q : K, Dm' *ᵥ v = p • v + q • (M *ᵥ v) := by
    intro v
    by_cases hv : v = 0
    · exact ⟨0, 0, by simp [hv]⟩
    obtain ⟨x, hx1, hx2⟩ := exists_dual_pair hd hJA hAA hv
    have hNx : symN (M *ᵥ v) v *ᵥ x = v := by
      rw [symN_mulVec, hx1, hx2, zero_smul, one_smul, zero_add]
    refine ⟨bJ (M *ᵥ v) (Dm' *ᵥ x), bJ v (Dm' *ᵥ x), ?_⟩
    have := congrArg (· *ᵥ x) (key' v hv)
    simp only [← mulVec_mulVec, hNx, symN_mulVec] at this
    rw [this, add_comm]
  obtain ⟨α, β, hαβ⟩ := exists_eq_add_smul hd hAA hD'A hspan
  have hJD := multiplier_spec D'
  rw [← hDm', hαβ] at hJD
  have e1 : (α • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + β • M)ᵀ * formJ r K =
      α • formJ r K + β • (formJ r K * M) := by
    rw [transpose_add, transpose_smul, transpose_smul, transpose_one, Matrix.add_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hJA]
  have e2 : formJ r K * M * M = d • formJ r K := by
    rw [Matrix.mul_assoc, hAA, Matrix.mul_smul, Matrix.mul_one]
  have hexp : (α • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + β • M)ᵀ * formJ r K *
      (α • 1 + β • M) = (α ^ 2 + β ^ 2 * d) • formJ r K + (2 * α * β) • (formJ r K * M) := by
    rw [e1, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_one, e2]
    module
  rw [hexp] at hJD
  have hJJ : formJ r K * formJ r K = -1 := by
    rw [formJ, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.mul_one, zero_add, add_zero, Matrix.mul_neg]
    rw [← fromBlocks_one, fromBlocks_neg, neg_zero]
  have hscal : (2 * α * β) • M = ((multiplier r K D' : K) - (α ^ 2 + β ^ 2 * d)) • 1 := by
    have h1 := congrArg (fun X => formJ r K * X) hJD
    have e3 : formJ r K * ((α ^ 2 + β ^ 2 * d) • formJ r K + (2 * α * β) • (formJ r K * M)) =
        -((α ^ 2 + β ^ 2 * d) • 1 + (2 * α * β) • M) := by
      rw [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hJJ,
        Matrix.neg_mul, Matrix.one_mul]
      module
    have e4 : formJ r K * ((multiplier r K D' : K) • formJ r K) =
        -((multiplier r K D' : K) • 1) := by
      rw [Matrix.mul_smul, hJJ, smul_neg]
    rw [e3, e4, neg_inj] at h1
    rw [sub_smul, ← h1]
    abel
  have hab0 : α * β = 0 := by
    by_contra hab
    have h2ab : (2 * α * β) ≠ 0 := by
      rw [mul_assoc]
      exact mul_ne_zero h2 hab
    set c := ((multiplier r K D' : K) - (α ^ 2 + β ^ 2 * d)) / (2 * α * β) with hc
    have hMc : M = c • 1 := by
      rw [hc, div_eq_inv_mul, ← smul_smul, ← hscal, smul_smul, inv_mul_cancel₀ h2ab, one_smul]
    have hc0 : c ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at hMc
      rw [hMc, Matrix.zero_mul] at hAA
      have := congrFun (congrFun hAA (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
      simp at this
      exact hd0 this.symm
    apply hAns (Units.mk0 c hc0)
    apply Units.ext
    rw [GeneralLinearGroup.coe_scalar]
    rw [← hM, hMc, Matrix.smul_one_eq_diagonal]
    rfl
  have hDinv : ∀ X : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K, Dm' = X → X ≠ 0 := by
    intro X hX h0
    have h1 : Dm' * (((D' : GL (Fin r ⊕ Fin r) K)⁻¹ : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 := by
      rw [hDm', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hX, h0, Matrix.zero_mul] at h1
    have := congrFun (congrFun h1 (Sum.inl ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    simp at this
  have horder : orderOf (conjAut r K A) = 2 := by
    apply orderOf_eq_prime
    · rw [pow_two, ← map_mul, conjAut_eq_one_iff (by omega)]
      refine ⟨Units.mk0 d hd0, Units.ext ?_⟩
      rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
      exact hAA.trans (by rw [Matrix.smul_one_eq_diagonal]; rfl)
    · intro h1
      obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by omega) A).1 h1
      exact hAns c hc
  rcases mul_eq_zero.1 hab0 with hα | hβ
  ·
    exfalso
    rw [hα, zero_smul, zero_add] at hαβ
    have hβ0 : β ≠ 0 := by
      intro h0
      apply hDinv _ hαβ
      rw [h0, zero_smul]
    have hq : conjAut r K (A⁻¹ * D') = 1 := by
      rw [conjAut_eq_one_iff (by omega)]
      refine ⟨Units.mk0 β hβ0, Units.ext ?_⟩
      rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar]
      change ((A⁻¹ : gsp r K) : GL (Fin r ⊕ Fin r) K).val * Dm' = _
      rw [hαβ, Matrix.mul_smul, Subgroup.coe_inv, hM, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.smul_one_eq_diagonal]
      rfl
    have hDeq : conjAut r K D' = conjAut r K A := by
      have : D' = A * (A⁻¹ * D') := by group
      rw [this, map_mul, hq, mul_one]
    rw [hDeq, horder] at hoddy
    exact absurd hoddy (by decide)
  ·
    rw [hβ, zero_smul, add_zero] at hαβ
    have hα0 : α ≠ 0 := by
      intro h0
      apply hDinv _ hαβ
      rw [h0, zero_smul]
    rw [conjAut_eq_one_iff (by omega)]
    refine ⟨Units.mk0 α hα0, Units.ext ?_⟩
    rw [GeneralLinearGroup.coe_scalar]
    exact hαβ.trans (by rw [Matrix.smul_one_eq_diagonal]; rfl)

end SelfE

end CFSG.ComponentClassification.Burgoyne.Sp
