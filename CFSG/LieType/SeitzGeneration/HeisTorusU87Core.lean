module

public import CFSG.LieType.SeitzGeneration.HeisTorusU86
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.LieType.SeitzGeneration

open Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {K : Type} [Field K] {r : ℕ} [Fact r.Prime] {ζ : K}

local notation "χ" => quadraticChar (ZMod r)

section Basic

@[expose] noncomputable def ug87_psi (hζ : IsPrimitiveRoot ζ r) : AddChar (ZMod r) K :=
  AddChar.zmodChar r hζ.pow_eq_one

theorem ug87_psi_natCast (hζ : IsPrimitiveRoot ζ r) (n : ℕ) :
    ug87_psi hζ (n : ZMod r) = ζ ^ n :=
  AddChar.zmodChar_apply' _ n

theorem ug87_psi_ne_one (hζ : IsPrimitiveRoot ζ r) : ug87_psi hζ ≠ 1 := by
  intro h
  have h1 : ug87_psi hζ ((1 : ℕ) : ZMod r) = 1 := by rw [h]; rfl
  rw [ug87_psi_natCast, pow_one] at h1
  exact hζ.ne_one (Fact.out : r.Prime).one_lt h1

theorem ug87_sum_fin {M : Type*} [AddCommMonoid M] (g : ZMod r → M) :
    ∑ i : Fin r, g ((i : ℕ) : ZMod r) = ∑ x : ZMod r, g x := by
  refine Fintype.sum_bijective (fun i : Fin r => ((i : ℕ) : ZMod r)) ?_ _ _ (fun _ => rfl)
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun i j hij => ?_, by rw [Fintype.card_fin, ZMod.card]⟩
  have h := (ZMod.natCast_eq_natCast_iff' (i : ℕ) (j : ℕ) r).mp hij
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at h
  exact Fin.ext h

theorem ug87_natCast_r [CharP K 2] (hr8 : r % 8 = 1) : (r : K) = 1 := by
  obtain ⟨m, hm⟩ : ∃ m, r = 2 * m + 1 := ⟨r / 2, by omega⟩
  rw [hm]
  simp [CharTwo.two_eq_zero]

theorem ug87_prod_zpow {ι : Type*} (s : Finset ι) {lam : K} (hlam : lam ≠ 0) (g : ι → ℤ) :
    ∏ i ∈ s, lam ^ g i = lam ^ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hlam]

theorem ug87_sum_chi_fin (hr8 : r % 8 = 1) : ∑ k : Fin r, χ ((k : ℕ) : ZMod r) = 0 := by
  rw [ug87_sum_fin (fun x : ZMod r => χ x)]
  exact quadraticChar_sum_zero (by rw [ZMod.ringChar_zmod_n]; omega)

end Basic

section Gamma

@[expose] noncomputable def ug87_gam (ζ : K) (t : ZMod r → K) : Matrix (Fin r) (Fin r) K :=
  heisFourierMat ζ * diagonal (fun k : Fin r => t ((k : ℕ) : ZMod r)) * (heisFourierMat ζ)⁻¹

theorem ug87_gam_apply [CharP K 2] (hr8 : r % 8 = 1) (hζ : IsPrimitiveRoot ζ r)
    (t : ZMod r → K) (i j : Fin r) :
    ug87_gam ζ t i j = ∑ x : ZMod r, t x *
      ug87_psi hζ ((((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r)) * x) := by
  have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
  unfold ug87_gam
  rw [heisFourierMat_inv hζ hr2, Matrix.mul_apply,
    ← ug87_sum_fin (fun x : ZMod r => t x *
      ug87_psi hζ ((((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r)) * x))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  simp only [Matrix.of_apply, heisFourierMat, ug87_natCast_r hr8, inv_one, one_mul]
  have hψ : ug87_psi hζ ((((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r)) * ((k : ℕ) : ZMod r)) =
      ζ ^ ((i : ℕ) * (k : ℕ)) * (ζ ^ ((k : ℕ) * (j : ℕ)))⁻¹ := by
    have : (((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r)) * ((k : ℕ) : ZMod r) =
        (((i : ℕ) * (k : ℕ) : ℕ) : ZMod r) + -((((k : ℕ) * (j : ℕ) : ℕ)) : ZMod r) := by
      push_cast
      ring
    rw [this, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv, ug87_psi_natCast,
      ug87_psi_natCast]
  rw [hψ]
  ring

theorem ug87_gam_mul (hζ : IsPrimitiveRoot ζ r) {t t' : ZMod r → K} (h : ∀ x, t x * t' x = 1) :
    ug87_gam ζ t * ug87_gam ζ t' = 1 := by
  have hΦ : IsUnit (heisFourierMat ζ : Matrix (Fin r) (Fin r) K).det :=
    isUnit_iff_ne_zero.mpr (det_heisFourierMat_ne_zero hζ)
  have hΨΦ : (heisFourierMat ζ : Matrix (Fin r) (Fin r) K)⁻¹ * heisFourierMat ζ = 1 :=
    Matrix.nonsing_inv_mul _ hΦ
  have hΦΨ : (heisFourierMat ζ : Matrix (Fin r) (Fin r) K) * (heisFourierMat ζ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hΦ
  have hDD : (diagonal fun k : Fin r => t ((k : ℕ) : ZMod r)) *
      diagonal (fun k : Fin r => t' ((k : ℕ) : ZMod r)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext k
    exact h _
  unfold ug87_gam
  calc _ = heisFourierMat ζ * diagonal (fun k : Fin r => t ((k : ℕ) : ZMod r)) *
        ((heisFourierMat ζ)⁻¹ * heisFourierMat ζ) *
        diagonal (fun k : Fin r => t' ((k : ℕ) : ZMod r)) * (heisFourierMat ζ)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hΨΦ, Matrix.mul_one, Matrix.mul_assoc _ (diagonal fun k : Fin r =>
          t ((k : ℕ) : ZMod r)), hDD, Matrix.mul_one, hΦΨ]

theorem ug87_gam_mulVec [CharP K 2] (hr8 : r % 8 = 1) (hζ : IsPrimitiveRoot ζ r)
    (t g : ZMod r → K) (i : Fin r) :
    ∑ j : Fin r, ug87_gam ζ t i j * g ((j : ℕ) : ZMod r) =
      ∑ x : ZMod r, t x * ug87_psi hζ (((i : ℕ) : ZMod r) * x) *
        ∑ z : ZMod r, g z * ug87_psi hζ ((-x) * z) := by
  have h1 : ∀ j : Fin r, ug87_gam ζ t i j * g ((j : ℕ) : ZMod r) =
      (fun z : ZMod r => (∑ x : ZMod r, t x *
        ug87_psi hζ ((((i : ℕ) : ZMod r) - z) * x)) * g z) ((j : ℕ) : ZMod r) :=
    fun j => by rw [ug87_gam_apply hr8 hζ]
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  refine (ug87_sum_fin (fun z : ZMod r => (∑ x : ZMod r, t x *
    ug87_psi hζ ((((i : ℕ) : ZMod r) - z) * x)) * g z)).trans ?_
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun z _ => ?_
  have : (((i : ℕ) : ZMod r) - z) * x = ((i : ℕ) : ZMod r) * x + (-x) * z := by ring
  rw [this, AddChar.map_add_eq_mul]
  ring

end Gamma

section Legendre

structure Ug87Ctx (ψ : AddChar (ZMod r) K) (σ : ℤ) : Prop where
  r8 : r % 8 = 1
  sign : σ = 1 ∨ σ = -1
  eta_pos : ug87_eta ψ σ = 1
  eta_neg : ug87_eta ψ (-σ) = 0

variable [CharP K 2] {ψ : AddChar (ZMod r) K} {σ : ℤ}

theorem Ug87Ctx.ft_chi (c : Ug87Ctx ψ σ) (φ : ℤ → K) (u : ZMod r) :
    ∑ x : ZMod r, φ (χ x) * ψ (u * x) = φ 0 + if u = 0 then 0 else φ (σ * χ u) :=
  ug87_ft_chi c.r8 c.sign c.eta_pos c.eta_neg φ u

theorem Ug87Ctx.ft_e (c : Ug87Ctx ψ σ) (φ : ℤ → K) (u : ZMod r) :
    ∑ x : ZMod r, φ (σ * χ x) * ψ (u * x) = φ 0 + if u = 0 then 0 else φ (χ u) :=
  ug87_ft_e c.r8 c.sign c.eta_pos c.eta_neg φ u

theorem Ug87Ctx.sigma_ne_zero (c : Ug87Ctx ψ σ) : σ ≠ 0 := by
  rcases c.sign with h | h <;> simp [h]

@[expose] noncomputable def ug87_tm (lam : K) (σ m : ℤ) (x : ZMod r) : K :=
  lam ^ (m * (σ * χ x))

@[expose] noncomputable def ug87_s (lam : K) (x : ZMod r) : K := lam ^ (-(χ x))

@[expose] noncomputable def ug87_v (x : ZMod r) : K := if χ x = 1 then 1 else 0

theorem ug87_ft_tm (c : Ug87Ctx ψ σ) (lam : K) (m : ℤ) (u : ZMod r) :
    ∑ x : ZMod r, ug87_tm lam σ m x * ψ (u * x) =
      1 + if u = 0 then 0 else lam ^ (m * χ u) := by
  have h := c.ft_e (fun n => lam ^ (m * n)) u
  simp only [mul_zero, zpow_zero] at h
  exact h

theorem ug87_gam_tm (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) (lam : K) (m : ℤ)
    (i j : Fin r) : ug87_gam ζ (ug87_tm lam σ m) i j =
      1 + if ((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r) = 0 then 0
        else lam ^ (m * χ (((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r))) := by
  rw [ug87_gam_apply c.r8 hζ, ug87_ft_tm c]

theorem ug87_gam_tm_symm (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) (lam : K)
    (m : ℤ) (i j : Fin r) :
    ug87_gam ζ (ug87_tm lam σ m) j i = ug87_gam ζ (ug87_tm lam σ m) i j := by
  rw [ug87_gam_tm hζ c, ug87_gam_tm hζ c]
  have h1 : ((j : ℕ) : ZMod r) - ((i : ℕ) : ZMod r) =
      -(((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r)) := by ring
  simp only [h1, ug87_chi_neg c.r8, neg_eq_zero]

theorem ug87_tm_mul (lam : K) (hlam : lam ≠ 0) (σ : ℤ) (x : ZMod r) :
    ug87_tm lam σ 1 x * ug87_tm lam σ (-1) x = 1 := by
  unfold ug87_tm
  rw [← zpow_add₀ hlam]
  have : (1 : ℤ) * (σ * χ x) + (-1) * (σ * χ x) = 0 := by ring
  rw [this, zpow_zero]

@[expose] noncomputable def ug87_D (lam : K) : Matrix (Fin r) (Fin r) K :=
  diagonal (fun k : Fin r => ug87_s lam ((k : ℕ) : ZMod r))

@[expose] noncomputable def ug87_y (ζ lam : K) (σ : ℤ) : Matrix (Fin r) (Fin r) K :=
  ug87_gam ζ (ug87_tm lam σ 1) * ug87_D lam * ug87_gam ζ (ug87_tm lam σ 1)

theorem ug87_y_apply_zero (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) {lam : K}
    (hlam : lam ≠ 0) (i : Fin r) (hi : i ≠ 0) : ug87_y ζ lam σ i 0 = 0 := by
  have hΓΓ' : ug87_gam ζ (ug87_tm lam σ 1) * ug87_gam ζ (ug87_tm lam σ (-1)) = 1 :=
    ug87_gam_mul hζ (ug87_tm_mul lam hlam σ)
  have key : ∀ j : Fin r, ug87_s lam ((j : ℕ) : ZMod r) * ug87_gam ζ (ug87_tm lam σ 1) j 0 =
      ug87_gam ζ (ug87_tm lam σ (-1)) j 0 := by
    intro j
    rw [ug87_gam_tm hζ c, ug87_gam_tm hζ c]
    simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
    by_cases hj : ((j : ℕ) : ZMod r) = 0
    · simp [ug87_s, hj, quadraticChar_zero]
    · simp only [hj, if_false]
      unfold ug87_s
      rw [mul_add, mul_one, ← zpow_add₀ hlam]
      have e1 : -(χ ((j : ℕ) : ZMod r)) + 1 * χ ((j : ℕ) : ZMod r) = 0 := by ring
      have e2 : (-1 : ℤ) * χ ((j : ℕ) : ZMod r) = -(χ ((j : ℕ) : ZMod r)) := by ring
      rw [e1, e2, zpow_zero]
      ring
  unfold ug87_y
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin r,
      (ug87_gam ζ (ug87_tm lam σ 1) * ug87_D lam : Matrix (Fin r) (Fin r) K) i j *
      ug87_gam ζ (ug87_tm lam σ 1) j 0 =
      ug87_gam ζ (ug87_tm lam σ 1) i j * ug87_gam ζ (ug87_tm lam σ (-1)) j 0 := by
    intro j
    rw [ug87_D, Matrix.mul_diagonal, mul_assoc, ← key j]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Matrix.mul_apply, hΓΓ',
    Matrix.one_apply_ne hi]

theorem ug87_gam_v (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) (lam : K)
    (i : Fin r) :
    ∑ j : Fin r, ug87_gam ζ (ug87_tm lam σ 1) i j * ug87_v ((j : ℕ) : ZMod r) =
      lam * ug87_v ((i : ℕ) : ZMod r) := by
  rw [ug87_gam_mulVec c.r8 hζ]
  have hG : ∀ x : ZMod r, ∑ z : ZMod r, ug87_v z * ug87_psi hζ ((-x) * z) =
      if σ * χ x = 1 then 1 else 0 := by
    intro x
    have h := c.ft_chi (fun n : ℤ => if n = 1 then (1 : K) else 0) (-x)
    simp only [ug87_v]
    rw [h]
    by_cases hx : x = 0
    · subst hx
      simp [quadraticChar_zero]
    · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
      simp [hnx, ug87_chi_neg c.r8]
  have hpt : ∀ x : ZMod r, ug87_tm lam σ 1 x * ug87_psi hζ (((i : ℕ) : ZMod r) * x) *
      (∑ z : ZMod r, ug87_v z * ug87_psi hζ ((-x) * z)) =
      lam * ((if σ * χ x = 1 then 1 else 0) * ug87_psi hζ (((i : ℕ) : ZMod r) * x)) := by
    intro x
    rw [hG x]
    by_cases hx : σ * χ x = 1
    · rw [if_pos hx]
      unfold ug87_tm
      rw [one_mul, hx, zpow_one]
      ring
    · rw [if_neg hx]
      ring
  rw [Finset.sum_congr rfl fun x _ => hpt x, ← Finset.mul_sum]
  have h2 := c.ft_e (fun n : ℤ => if n = 1 then (1 : K) else 0) ((i : ℕ) : ZMod r)
  rw [h2]
  by_cases hi : ((i : ℕ) : ZMod r) = 0
  · simp [ug87_v, hi, quadraticChar_zero]
  · simp [ug87_v, hi]

theorem ug87_s_v (lam : K) (x : ZMod r) :
    ug87_s lam x * ug87_v x = lam⁻¹ * ug87_v x := by
  unfold ug87_s ug87_v
  by_cases h : χ x = 1
  · simp [h]
  · rw [if_neg h]
    ring

theorem ug87_y_v (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) {lam : K}
    (hlam : lam ≠ 0) (i : Fin r) :
    ∑ j : Fin r, ug87_y ζ lam σ i j * ug87_v ((j : ℕ) : ZMod r) =
      lam * ug87_v ((i : ℕ) : ZMod r) := by
  set vF : Fin r → K := fun j => ug87_v ((j : ℕ) : ZMod r) with hvF
  have E1 : ug87_gam ζ (ug87_tm lam σ 1) *ᵥ vF = lam • vF := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hvF]
    exact ug87_gam_v hζ c lam i
  have E2 : ug87_D lam *ᵥ vF = lam⁻¹ • vF := by
    funext i
    simp only [ug87_D, Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, hvF]
    exact ug87_s_v lam _
  have E3 : ug87_y ζ lam σ *ᵥ vF = lam • vF := by
    unfold ug87_y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, E1, Matrix.mulVec_smul, E2, smul_smul,
      mul_inv_cancel₀ hlam, one_smul, E1]
  have := congrFun E3 i
  simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hvF] using this

theorem ug87_gam_sq (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) {lam : K}
    (hlam : lam ≠ 0) (i j : Fin r) :
    ug87_gam ζ (ug87_tm lam σ 1) i j * ug87_gam ζ (ug87_tm lam σ 1) i j =
      ug87_gam ζ (ug87_tm lam σ 2) i j := by
  rw [ug87_gam_tm hζ c, ug87_gam_tm hζ c]
  by_cases hu : ((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r) = 0
  · simp [hu]
  · simp only [hu, if_false]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hw : lam ^ ((2 : ℤ) * χ (((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r))) =
        lam ^ ((1 : ℤ) * χ (((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r))) *
          lam ^ ((1 : ℤ) * χ (((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r))) := by
      rw [← zpow_add₀ hlam]
      congr 1
      ring
    rw [hw]
    linear_combination (lam ^ ((1 : ℤ) * χ (((i : ℕ) : ZMod r) - ((j : ℕ) : ZMod r)))) * h2

theorem ug87_y_diag (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) {lam : K}
    (hlam : lam ≠ 0) (a : Fin r) (ha : ((a : ℕ) : ZMod r) ≠ 0) :
    ug87_y ζ lam σ a a = 1 + lam ^ (2 * χ ((a : ℕ) : ZMod r)) *
      (1 + lam ^ (-(χ ((a : ℕ) : ZMod r)))) := by
  have h1 : ug87_y ζ lam σ a a = ∑ j : Fin r,
      ug87_gam ζ (ug87_tm lam σ 2) a j * ug87_s lam ((j : ℕ) : ZMod r) := by
    unfold ug87_y
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ug87_D, Matrix.mul_diagonal, ug87_gam_tm_symm hζ c lam 1 a j,
      ← ug87_gam_sq hζ c hlam a j]
    ring
  rw [h1, ug87_gam_mulVec c.r8 hζ]
  have hS : ∀ x : ZMod r, ∑ z : ZMod r, ug87_s lam z * ug87_psi hζ ((-x) * z) =
      1 + if x = 0 then 0 else lam ^ (-(σ * χ x)) := by
    intro x
    have h := c.ft_chi (fun n : ℤ => lam ^ (-n)) (-x)
    simp only [neg_zero, zpow_zero, neg_eq_zero, ug87_chi_neg c.r8] at h
    exact h
  have hpt : ∀ x : ZMod r, ug87_tm lam σ 2 x * ug87_psi hζ (((a : ℕ) : ZMod r) * x) *
      (∑ z : ZMod r, ug87_s lam z * ug87_psi hζ ((-x) * z)) =
      (lam ^ (2 * (σ * χ x)) * (1 + if σ * χ x = 0 then 0 else lam ^ (-(σ * χ x)))) *
        ug87_psi hζ (((a : ℕ) : ZMod r) * x) := by
    intro x
    rw [hS x]
    by_cases hx : x = 0
    · subst hx
      simp [ug87_tm, quadraticChar_zero]
    · have hσχ : σ * χ x ≠ 0 :=
        mul_ne_zero c.sigma_ne_zero (fun h => hx ((ug87_chi_eq_zero_iff x).mp h))
      simp only [hx, hσχ, if_false, ug87_tm]
      ring
  rw [Finset.sum_congr rfl fun x _ => hpt x]
  have h2 := c.ft_e (fun n : ℤ => lam ^ (2 * n) * (1 + if n = 0 then 0 else lam ^ (-n)))
    ((a : ℕ) : ZMod r)
  rw [h2]
  have hχa : χ ((a : ℕ) : ZMod r) ≠ 0 := fun h => ha ((ug87_chi_eq_zero_iff _).mp h)
  rw [if_neg ha, if_neg hχa]
  simp only [mul_zero, zpow_zero, eq_self_iff_true, if_true, add_zero, mul_one, neg_zero]

theorem ug87_y_diag_one (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) {lam : K}
    (hlam : lam ≠ 0) (a : Fin r) (ha : χ ((a : ℕ) : ZMod r) = 1) :
    ug87_y ζ lam σ a a = 1 + lam + lam ^ 2 := by
  have ha0 : ((a : ℕ) : ZMod r) ≠ 0 := fun h => by
    rw [h, quadraticChar_zero] at ha
    exact zero_ne_one ha
  rw [ug87_y_diag hζ c hlam a ha0, ha, mul_one, _root_.zpow_neg, zpow_one, zpow_ofNat]
  field_simp
  ring

theorem ug87_one_add_ne_zero (hζ : IsPrimitiveRoot ζ r) (hr8 : r % 8 = 1) :
    1 + ζ + ζ ^ 2 ≠ 0 := by
  intro h
  have h3 : ζ ^ 3 = 1 := by linear_combination (ζ - 1) * h
  have h1 := Nat.le_of_dvd (by norm_num) (hζ.dvd_of_pow_eq_one 3 h3)
  have h2 := (Fact.out : r.Prime).two_le
  omega

theorem ug87_not_monomial (hζ : IsPrimitiveRoot ζ r) (c : Ug87Ctx (ug87_psi hζ) σ) {lam : K}
    (hlam : lam ≠ 0) (hlam1 : lam ≠ 1) (hlam3 : 1 + lam + lam ^ 2 ≠ 0) :
    ¬ IsMonomialMat (ug87_y (r := r) ζ lam σ) := by
  intro hmono
  have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
  set a : Fin r := ⟨1, by omega⟩ with ha_def
  have haZ : ((a : ℕ) : ZMod r) = 1 := Nat.cast_one
  have hχa : χ ((a : ℕ) : ZMod r) = 1 := by rw [haZ]; exact map_one _
  have hoff : ∀ j : Fin r, χ ((j : ℕ) : ZMod r) = 1 → ∀ i : Fin r, i ≠ j →
      ug87_y ζ lam σ i j = 0 := by
    intro j hj i hij
    by_contra hne
    have hjj : ug87_y ζ lam σ j j ≠ 0 := by
      rw [ug87_y_diag_one hζ c hlam j hj]
      exact hlam3
    exact hij (hmono j i j hne hjj)
  have hsum := ug87_y_v hζ c hlam a
  have hsingle : ∑ j : Fin r, ug87_y ζ lam σ a j * ug87_v ((j : ℕ) : ZMod r) =
      ug87_y ζ lam σ a a * ug87_v ((a : ℕ) : ZMod r) := by
    refine Finset.sum_eq_single a ?_ ?_
    · intro j _ hja
      by_cases hj : χ ((j : ℕ) : ZMod r) = 1
      · rw [hoff j hj a (Ne.symm hja), zero_mul]
      · have : (ug87_v ((j : ℕ) : ZMod r) : K) = 0 := by
          unfold ug87_v
          rw [if_neg hj]
        rw [this, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ a) h
  have hva : (ug87_v ((a : ℕ) : ZMod r) : K) = 1 := by
    unfold ug87_v
    rw [if_pos hχa]
  rw [hsingle, hva, mul_one, mul_one, ug87_y_diag_one hζ c hlam a hχa] at hsum
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : (1 + lam) ^ 2 = 0 := by linear_combination hsum + lam * h2
  have h1' : 1 + lam = 0 := (pow_eq_zero_iff two_ne_zero).mp hsq
  exact hlam1 (by linear_combination h1' - h2)

theorem ug87_zpow_pow_eq_one {lam : K} (hlam : lam ^ r = 1) (n : ℤ) : (lam ^ n) ^ r = 1 := by
  rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hlam,
    _root_.one_zpow]

theorem ug87_prod_tm (hr8 : r % 8 = 1) (lam : K) (hlam : lam ≠ 0) (σ m : ℤ) :
    ∏ k : Fin r, ug87_tm lam σ m ((k : ℕ) : ZMod r) = 1 := by
  unfold ug87_tm
  rw [ug87_prod_zpow _ hlam]
  have : ∑ k : Fin r, m * (σ * χ ((k : ℕ) : ZMod r)) = 0 := by
    rw [← Finset.mul_sum, ← Finset.mul_sum, ug87_sum_chi_fin hr8, mul_zero, mul_zero]
  rw [this, zpow_zero]

theorem ug87_prod_s (hr8 : r % 8 = 1) (lam : K) (hlam : lam ≠ 0) :
    ∏ k : Fin r, ug87_s lam ((k : ℕ) : ZMod r) = 1 := by
  unfold ug87_s
  rw [ug87_prod_zpow _ hlam, Finset.sum_neg_distrib, ug87_sum_chi_fin hr8, neg_zero, zpow_zero]

theorem ug87_core (hr8 : r % 8 = 1) (hζ : IsPrimitiveRoot ζ r) :
    ∃ t s : Fin r → K, (∀ k, t k ^ r = 1) ∧ (∀ k, s k ^ r = 1) ∧ ∏ k, t k = 1 ∧
      ∏ k, s k = 1 ∧
      (∀ i : Fin r, i ≠ 0 →
        (heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹ * diagonal s *
          (heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹) :
            Matrix (Fin r) (Fin r) K) i 0 = 0) ∧
      ¬ IsMonomialMat (heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹ * diagonal s *
          (heisFourierMat ζ * diagonal t * (heisFourierMat ζ)⁻¹) : Matrix (Fin r) (Fin r) K) := by
  have hr2 := (Fact.out : r.Prime).two_le
  obtain ⟨σ, hσ, h1, h0⟩ := ug87_exists_sigma hr8 (ug87_psi_ne_one hζ)
  have c : Ug87Ctx (ug87_psi hζ) σ := ⟨hr8, hσ, h1, h0⟩
  have hlam : ζ ≠ 0 := hζ.ne_zero (by omega)
  have hlam1 : ζ ≠ 1 := hζ.ne_one (by omega)
  refine ⟨fun k => ug87_tm ζ σ 1 ((k : ℕ) : ZMod r), fun k => ug87_s ζ ((k : ℕ) : ZMod r),
    fun k => ug87_zpow_pow_eq_one hζ.pow_eq_one _, fun k => ug87_zpow_pow_eq_one hζ.pow_eq_one _,
    ug87_prod_tm hr8 ζ hlam σ 1, ug87_prod_s hr8 ζ hlam, ?_, ?_⟩
  · intro i hi
    exact ug87_y_apply_zero hζ c hlam i hi
  · exact ug87_not_monomial hζ c hlam hlam1 (ug87_one_add_ne_zero hζ hr8)

end Legendre

end CFSG.LieType.SeitzGeneration

end
