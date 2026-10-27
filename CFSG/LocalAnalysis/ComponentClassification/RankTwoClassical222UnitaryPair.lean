module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassical222UnitaryDelta
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Module Matrix Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.RankTwoStandard
open CFSG.LocalAnalysis.ComponentInitial
open scoped Matrix

section Swap

variable {G : Type} [Group G] {A : Subgroup G} {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
  {H : Subgroup (GL ι K)} {e : rankTwoQuot A ≃* StatedProj H}

theorem Represents.mul_comm_of_commute_of_sq [CharP K 2] {x p : G} {X P : GL ι K}
    (hx : Represents e x X) (hp : Represents e p P) {c₀ : K}
    (hP2 : (P : Matrix ι ι K) * P = c₀ • 1) (hxp : x * p = p * x) :
    (X : Matrix ι ι K) * P = P * X := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.elim _ _
  have h1 : Represents e (p * x) (X * P) := hxp ▸ hx.mul hp
  obtain ⟨c, hc⟩ := (hp.mul hx).exists_scalar h1
  have hcm : (X : Matrix ι ι K) * P = (c : K) • ((P : Matrix ι ι K) * X) := by
    have h := congrArg (fun Y : GL ι K => (Y : Matrix ι ι K)) hc
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [h, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, mul_one]
  have hX : c₀ • (X : Matrix ι ι K) = ((c : K) ^ 2 * c₀) • (X : Matrix ι ι K) := by
    calc c₀ • (X : Matrix ι ι K) = X * (P * P) := by rw [hP2, Matrix.mul_smul, mul_one]
      _ = (X * P) * P := by rw [mul_assoc]
      _ = ((c : K) • ((P : Matrix ι ι K) * X)) * P := by rw [hcm]
      _ = (c : K) • ((P : Matrix ι ι K) * (X * P)) := by rw [Matrix.smul_mul, mul_assoc]
      _ = (c : K) • ((P : Matrix ι ι K) * ((c : K) • ((P : Matrix ι ι K) * X))) := by rw [hcm]
      _ = ((c : K) ^ 2 * c₀) • (X : Matrix ι ι K) := by
          rw [Matrix.mul_smul, smul_smul, ← mul_assoc, hP2, Matrix.smul_mul, Matrix.one_mul,
            smul_smul, pow_two]
  have hX0 : (X : Matrix ι ι K) ≠ 0 := fun h0 => not_isUnit_zero (h0 ▸ Units.isUnit X)
  have hc₀ : c₀ ≠ 0 := by
    rintro rfl
    have hu : IsUnit ((P : Matrix ι ι K) * P) := (Units.isUnit P).mul (Units.isUnit P)
    rw [hP2, zero_smul] at hu
    exact not_isUnit_zero hu
  have hc2 : (c : K) ^ 2 = 1 := by
    have h2 : (c₀ * (1 - (c : K) ^ 2)) • (X : Matrix ι ι K) = 0 := by
      rw [mul_sub, mul_one, sub_smul, hX, mul_comm, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hc₀)).symm
    · exact absurd h hX0
  have hc1 : (c : K) = 1 := by
    have h : ((c : K) + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, hc2, one_pow, CharTwo.add_self_eq_zero]
    have h' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [← CharTwo.sub_eq_add] at h'
    exact sub_eq_zero.mp h'
  rw [hcm, hc1, one_smul]

variable [CharP K 2] (hZ : Odd (Nat.card (center ↥A))) {p : G} (hp2 : p ^ 2 = 1)
  {M : GL ι K} (hpM : Represents e p M) {u : G}
  (horb : ∀ a ∈ A ⊓ centralizer ({p} : Set G), a * u * a⁻¹ = u ∨ a * u * a⁻¹ = u * p)
  {U : GL ι K} (hU : Represents e u U) {c₀ : K} (hU2 : (U : Matrix ι ι K) * U = c₀ • 1)
include hZ hp2 hpM horb hU hU2

theorem commute_trichotomy {R₁ R₂ : GL ι K} (h1H : R₁ ∈ H) (h2H : R₂ ∈ H)
    (h1M : R₁ * M = M * R₁) (h2M : R₂ * M = M * R₂) :
    (R₁ : Matrix ι ι K) * U = U * R₁ ∨ (R₂ : Matrix ι ι K) * U = U * R₂ ∨
      ((R₁ * R₂ : GL ι K) : Matrix ι ι K) * U = U * (R₁ * R₂ : GL ι K) := by
  have hpp : p * p = 1 := by rw [← pow_two]; exact hp2
  obtain ⟨r₁, hr₁⟩ := exists_represents_of_mem (e := e) h1H
  obtain ⟨r₂, hr₂⟩ := exists_represents_of_mem (e := e) h2H
  have hr₁p := commute_of_represents hZ hr₁ hpM hp2 h1M
  have hr₂p := commute_of_represents hZ hr₂ hpM hp2 h2M
  have hr₁C : r₁ ∈ A ⊓ centralizer ({p} : Set G) :=
    mem_inf.mpr ⟨hr₁.1, mem_centralizer_singleton_iff.mpr hr₁p⟩
  have hr₂C : r₂ ∈ A ⊓ centralizer ({p} : Set G) :=
    mem_inf.mpr ⟨hr₂.1, mem_centralizer_singleton_iff.mpr hr₂p⟩
  have hfix : ∀ (r : G) (R : GL ι K), Represents e r R → r * u * r⁻¹ = u →
      (R : Matrix ι ι K) * U = U * R := by
    intro r R hr hru
    have hru' : r * u = u * r :=
      calc r * u = r * u * r⁻¹ * r := by group
        _ = u * r := by rw [hru]
    exact hr.mul_comm_of_commute_of_sq hU hU2 hru'
  rcases pairOrbit_conj hpp hr₁p (horb r₁ hr₁C) with ⟨h1, -⟩ | ⟨-, -, h1, -⟩
  · exact Or.inl (hfix r₁ R₁ hr₁ h1)
  rcases pairOrbit_conj hpp hr₂p (horb r₂ hr₂C) with ⟨h2, -⟩ | ⟨h2, -⟩
  · exact Or.inr (Or.inl (hfix r₂ R₂ hr₂ h2))
  refine Or.inr (Or.inr (hfix (r₁ * r₂) (R₁ * R₂) (hr₁.mul hr₂) ?_))
  calc r₁ * r₂ * u * (r₁ * r₂)⁻¹ = r₁ * (r₂ * u * r₂⁻¹) * r₁⁻¹ := by group
    _ = u := by rw [h2, h1]

theorem commute_sq_of_pairOrbit {R : GL ι K} (hRH : R ∈ H) (hRM : R * M = M * R) :
    ((R * R : GL ι K) : Matrix ι ι K) * U = U * (R * R : GL ι K) := by
  have hpp : p * p = 1 := by rw [← pow_two]; exact hp2
  obtain ⟨r, hr⟩ := exists_represents_of_mem (e := e) hRH
  have hrp := commute_of_represents hZ hr hpM hp2 hRM
  have hrC : r ∈ A ⊓ centralizer ({p} : Set G) :=
    mem_inf.mpr ⟨hr.1, mem_centralizer_singleton_iff.mpr hrp⟩
  have hfix : r * r * u * (r * r)⁻¹ = u := by
    rcases pairOrbit_conj hpp hrp (horb r hrC) with ⟨h1, -⟩ | ⟨h1, -, h3, -⟩
    · calc r * r * u * (r * r)⁻¹ = r * (r * u * r⁻¹) * r⁻¹ := by group
        _ = u := by rw [h1, h1]
    · calc r * r * u * (r * r)⁻¹ = r * (r * u * r⁻¹) * r⁻¹ := by group
        _ = u := by rw [h1, h3]
  have hru' : r * r * u = u * (r * r) :=
    calc r * r * u = r * r * u * (r * r)⁻¹ * (r * r) := by group
      _ = u * (r * r) := by rw [hfix]
  exact (hr.mul hr).mul_comm_of_commute_of_sq hU hU2 hru'

end Swap

section Roots

variable {K : Type} [Field K] {σ : K →+* K} {ℓ r : ℕ}

variable (σ) in
@[expose] def symP (u v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  tv2 σ u v + tv2 σ v u

theorem symP_adj (hσ : ∀ x, σ (σ x) = x) (u v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    adjM σ (symP σ u v) * unitGram K ℓ r = unitGram K ℓ r * symP σ u v := by
  rw [symP, adjM_add, Matrix.add_mul, adjM_tv2_mul_unitGram hσ, adjM_tv2_mul_unitGram hσ,
    ← Matrix.mul_add, add_comm]

theorem symP_mul_self (u v : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) :
    symP σ u v * symP σ u v = hJ σ v u • tv2 σ u v + hJ σ v v • tv2 σ u u +
      hJ σ u u • tv2 σ v v + hJ σ u v • tv2 σ v u := by
  rw [symP, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, tv2_mul_tv2', tv2_mul_tv2',
    tv2_mul_tv2', tv2_mul_tv2']
  abel

theorem adjM_one_add_smul_mul_unitGram [CharP K 2]
    {E : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K}
    (hE : adjM σ E * unitGram K ℓ r = unitGram K ℓ r * E) (hE2 : E * E = 0) {t : K}
    (ht : σ t = t) :
    adjM σ (1 + t • E) * unitGram K ℓ r * (1 + t • E) = unitGram K ℓ r := by
  refine adjM_one_add_mul_unitGram ?_ ?_
  · rw [adjM_smul, ht, Matrix.smul_mul, hE, Matrix.mul_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, hE2, smul_zero, smul_zero]

theorem symP_w_w (i j : Fin ℓ) (s : K) :
    symP σ (s • Pi.single (.inr (.inl i)) 1) (Pi.single (.inr (.inl j)) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) =
      s • Matrix.single (.inr (.inl i)) (.inl j) 1 +
        σ s • Matrix.single (.inr (.inl j)) (.inl i) 1 := by
  simp only [symP, tv2_smul_left, tv2_smul_right, tv2_single, swapXW]

theorem symP_w_w_mul_self (i j : Fin ℓ) (s : K) :
    symP σ (s • Pi.single (.inr (.inl i)) 1) (Pi.single (.inr (.inl j)) 1 :
        Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) *
      symP σ (s • Pi.single (.inr (.inl i)) 1) (Pi.single (.inr (.inl j)) 1) = 0 := by
  rw [symP_mul_self]
  simp [hJ_smul_left, hJ_smul_right, hJ_single, swapXW]

theorem symP_w_w_commute (i j : Fin ℓ) (s : K) :
    Commute (symP σ (s • Pi.single (.inr (.inl i)) 1) (Pi.single (.inr (.inl j)) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K)) (sqZeroStd ℓ r) := by
  rw [Commute, SemiconjBy, symP, Matrix.add_mul, Matrix.mul_add, tv2_mul_sqZeroStd,
    tv2_mul_sqZeroStd, sqZeroStd_mul_tv2, sqZeroStd_mul_tv2]
  simp only [Matrix.mulVec_smul, sqZeroStd_mulVec_single_inr, smul_zero, tv2_zero_right,
    tv2_zero_left]

theorem symP_xw (i j : Fin ℓ) (ζ : K) :
    symP σ (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1)
        (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1 :
          Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) =
      (Matrix.single (.inl i) (.inl i) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl i)) 1) +
      σ ζ • (Matrix.single (.inl i) (.inl j) 1 + Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) +
      ζ • (Matrix.single (.inl j) (.inl i) 1 + Matrix.single (.inr (.inl j)) (.inr (.inl i)) 1) +
      (ζ * σ ζ) •
        (Matrix.single (.inl j) (.inl j) 1 + Matrix.single (.inr (.inl j)) (.inr (.inl j)) 1) := by
  simp only [symP, tv2_add_left, tv2_add_right, tv2_smul_left, tv2_smul_right, tv2_single,
    swapXW]
  module

theorem symP_xw_mul_self [CharP K 2] {i j : Fin ℓ} (hij : i ≠ j) {ζ : K} (hζ : σ ζ * ζ = 1) :
    symP σ (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1)
        (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1 :
          Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) *
      symP σ (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1)
        (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1) = 0 := by
  have hζ' : ζ * σ ζ = 1 := by rw [mul_comm]; exact hζ
  have h1 : hJ σ (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1) = 0 := by
    simp only [hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
    simp [hij, Ne.symm hij, hζ', CharTwo.add_self_eq_zero]
  have h2 : hJ σ (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1) =
        0 := by
    simp only [hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
    simp [hij, Ne.symm hij, hζ', CharTwo.add_self_eq_zero]
  have h3 : hJ σ (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1) = 0 := by
    simp [hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
  have h4 : hJ σ (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K)
        (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1) = 0 := by
    simp [hJ_add_left, hJ_add_right, hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
  rw [symP_mul_self, h1, h2, h3, h4]
  simp

theorem symP_xw_commute (i j : Fin ℓ) (ζ : K) :
    Commute (symP σ (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1)
        (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1 :
          Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K)) (sqZeroStd ℓ r) := by
  have hSx : sqZeroStd ℓ r *ᵥ (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) =
        Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1 := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, sqZeroStd_mulVec_single_inl]
  have hSw : sqZeroStd ℓ r *ᵥ (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1 :
      Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) = 0 := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, sqZeroStd_mulVec_single_inr, smul_zero,
      add_zero]
  rw [Commute, SemiconjBy, symP, Matrix.add_mul, Matrix.mul_add, tv2_mul_sqZeroStd,
    tv2_mul_sqZeroStd, sqZeroStd_mul_tv2, sqZeroStd_mul_tv2, hSx, hSw, tv2_zero_right,
    tv2_zero_left, zero_add, add_zero]

variable (σ) in
@[expose] def zY (j : Fin ℓ) (k : Fin r) (t c : K) :
    Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
  symP σ (t • Pi.single (.inr (.inr k)) 1) (Pi.single (.inr (.inl j)) 1) +
    c • tv2 σ (Pi.single (.inr (.inl j)) 1) (Pi.single (.inr (.inl j)) 1)

theorem zY_eq (j : Fin ℓ) (k : Fin r) (t c : K) :
    zY σ j k t c = t • Matrix.single (.inr (.inr k)) (.inl j) 1 +
      σ t • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1 +
      c • Matrix.single (.inr (.inl j)) (.inl j) 1 := by
  simp only [zY, symP, tv2_smul_left, tv2_smul_right, tv2_single, swapXW]

theorem zY_mul_zY (j : Fin ℓ) (k : Fin r) (t c t' c' : K) :
    zY σ j k t c * zY σ j k t' c' =
      (σ t * t') • tv2 σ (Pi.single (.inr (.inl j)) 1) (Pi.single (.inr (.inl j)) 1) := by
  simp only [zY, symP, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    tv2_mul_tv2', hJ_smul_left, hJ_smul_right, hJ_single, swapXW]
  simp [tv2_smul_left, tv2_smul_right, smul_smul]
  rw [mul_comm]

theorem one_add_zY_mul (j : Fin ℓ) (k : Fin r) (t c t' c' : K) :
    (1 + zY σ j k t c) * (1 + zY σ j k t' c') = 1 + zY σ j k (t + t') (c + c' + σ t * t') := by
  have h := zY_mul_zY (σ := σ) j k t c t' c'
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, h]
  simp only [zY, symP, add_smul, tv2_add_left, tv2_add_right, tv2_smul_left, tv2_smul_right]
  module

theorem zY_commute (j : Fin ℓ) (k : Fin r) (t c : K) :
    Commute (zY σ j k t c) (sqZeroStd ℓ r) := by
  rw [Commute, SemiconjBy, zY, symP, Matrix.add_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, tv2_mul_sqZeroStd, tv2_mul_sqZeroStd,
    tv2_mul_sqZeroStd, sqZeroStd_mul_tv2, sqZeroStd_mul_tv2, sqZeroStd_mul_tv2]
  simp only [Matrix.mulVec_smul, sqZeroStd_mulVec_single_inr, smul_zero, tv2_zero_right,
    tv2_zero_left]

theorem adjM_one_add_zY [CharP K 2] (hσ : ∀ x, σ (σ x) = x) (j : Fin ℓ) (k : Fin r)
    {t c : K} (htc : c + σ c = σ t * t) :
    adjM σ (1 + zY σ j k t c) * unitGram K ℓ r * (1 + zY σ j k t c) = unitGram K ℓ r := by
  set P := symP σ (t • Pi.single (.inr (.inr k)) 1)
    (Pi.single (.inr (.inl j)) 1 : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) with hP
  set D := tv2 σ (Pi.single (.inr (.inl j)) 1)
    (Pi.single (.inr (.inl j)) 1 : Fin ℓ ⊕ (Fin ℓ ⊕ Fin r) → K) with hD
  have hPJ : adjM σ P * unitGram K ℓ r = unitGram K ℓ r * P := symP_adj hσ _ _
  have hDJ : adjM σ D * unitGram K ℓ r = unitGram K ℓ r * D := adjM_tv2_mul_unitGram hσ _ _
  have hPP : P * P = (σ t * t) • D := by
    rw [hP, symP_mul_self]
    simp [hJ_smul_left, hJ_smul_right, hJ_single, swapXW, hD]
    rw [mul_comm]
  have hPD : P * D = 0 := by
    rw [hP, hD, symP, Matrix.add_mul, tv2_mul_tv2', tv2_mul_tv2']
    simp [hJ_smul_left, hJ_single, swapXW]
  have hDP : D * P = 0 := by
    rw [hP, hD, symP, Matrix.mul_add, tv2_mul_tv2', tv2_mul_tv2']
    simp [hJ_smul_right, hJ_single, swapXW]
  have hDD : D * D = 0 := by
    rw [hD, tv2_mul_tv2', hJ_single]
    simp [swapXW]
  have hZ : zY σ j k t c = P + c • D := rfl
  rw [hZ, adjM_add, adjM_add, adjM_one, adjM_smul]
  have e1 : (1 + (adjM σ P + σ c • adjM σ D)) * unitGram K ℓ r =
      unitGram K ℓ r + unitGram K ℓ r * P + σ c • (unitGram K ℓ r * D) := by
    rw [Matrix.add_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, hPJ, hDJ, add_assoc]
  rw [e1]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_assoc, hPP, hPD, hDP, hDD, smul_zero, Matrix.mul_zero, add_zero]
  have h2 : unitGram K ℓ r * P + unitGram K ℓ r * P = 0 := matrix_add_self _
  have h3 : (c + σ c + σ t * t) • (unitGram K ℓ r * D) = 0 := by
    rw [htc, CharTwo.add_self_eq_zero, zero_smul]
  calc _ = unitGram K ℓ r + (unitGram K ℓ r * P + unitGram K ℓ r * P) +
        (c + σ c + σ t * t) • (unitGram K ℓ r * D) := by module
    _ = unitGram K ℓ r := by rw [h2, h3, add_zero, add_zero]

end Roots

section Unitary

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem pairOrbitFree_unitary : PairOrbitFree .unitary := by
  intro G _ _ A D hD _ hZ hq p ℓ0 hp
  cases D with
  | unitary n m hn hm K hK e =>
    have hU : UnitaryFieldData 2 m K := ⟨Nat.prime_two, hm, by rw [hK, ← pow_mul, mul_comm]⟩
    have : CharP K 2 := hU.charP
    have : Finite K := hU.finite
    obtain ⟨hpo, M, hpM, hM2, -⟩ := hp
    have hp2' : p ^ 2 = 1 := by rw [← hpo]; exact pow_orderOf_eq_one p
    have hMsq : M ^ 2 = 1 := by rw [← hM2]; exact pow_orderOf_eq_one M
    set σ := hU.bar with hσdef
    have hσ : ∀ x, σ (σ x) = x := hU.bar_bar
    have hσq : ∀ x, σ x = x ^ 2 ^ m := hU.bar_apply
    have htr : ∀ c, σ c = c → ∃ d, d + σ d = c := by
      intro c hc
      obtain ⟨d, hd⟩ := hU.traceLin_surjective ⟨c, (hU.mem_fixedField).mpr hc⟩
      exact ⟨d, congrArg Subtype.val hd⟩
    have hMu := adjM_mul_self_of_mem_statedSU hσ hσq hpM.2.1
    have hMM : (M : Matrix (Fin n) (Fin n) K) * M = 1 := by
      rw [← Units.val_mul, ← sq, ← hM2, pow_orderOf_eq_one, Units.val_one]
    have hMadj : adjM σ (M : Matrix (Fin n) (Fin n) K) = M := by
      calc adjM σ (M : Matrix (Fin n) (Fin n) K) =
          adjM σ (M : Matrix (Fin n) (Fin n) K) * (M * M) := by rw [hMM, mul_one]
        _ = M := by rw [← mul_assoc, hMu, one_mul]
    have hNh : adjM σ ((M : Matrix (Fin n) (Fin n) K) - 1) =
        (M : Matrix (Fin n) (Fin n) K) - 1 := by
      rw [adjM_sub, hMadj, adjM_one]
    have hN := sub_one_mul_self_eq_zero hM2
    have hM1 : M ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hM2
      omega
    have hN0 := sub_one_ne_zero hM1
    obtain ⟨z, hz, hz1⟩ := exists_norm_one_ne_one hK
    have hz' : σ z * z = 1 := by rw [hσq]; exact hz
    obtain ⟨θ, hθ⟩ := hU.exists_bar_ne
    obtain ⟨μ, hμσ, hμ0, hμ1⟩ : ∃ μ : K, σ μ = μ ∧ μ ≠ 0 ∧ μ ≠ 1 := by
      have h4 : 4 ≤ 2 ^ m := hq
      obtain ⟨μ₀, h0, h1⟩ := exists_scalar_ne_zero_ne_one (K := hU.fixedField)
        (by rw [hU.card_fixedField]; omega)
      refine ⟨μ₀, (hU.mem_fixedField).mp μ₀.2, fun h => h0 ?_, fun h => h1 ?_⟩
      · exact Subtype.ext h
      · exact Subtype.ext h
    have h2two : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    have hσz1 : σ z ≠ 1 := fun h => hz1 (by rw [← hσ z, h, map_one])
    have hzσz : z ≠ σ z := fun h => mul_self_ne_one_of_ne_one hz1 (by
      have h2 := hz'
      rw [← h] at h2
      exact h2)
    have hz2 : σ (z * z) * (z * z) = 1 := by
      rw [map_mul]
      calc σ z * σ z * (z * z) = (σ z * z) * (σ z * z) := by ring
        _ = 1 := by rw [hz', one_mul]
    have hzz : z * σ z = 1 := by rw [mul_comm]; exact hz'
    have hzz2 : z * z * (σ z * σ z) = 1 := by
      calc z * z * (σ z * σ z) = (σ z * z) * (σ z * z) := by ring
        _ = 1 := by rw [hz', one_mul]
    have hone : σ 1 * (1 : K) = 1 := by rw [map_one, one_mul]
    have hθ0 : θ - σ θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ)
    have h1μ : (1 : K) + μ ≠ 0 := fun h => hμ1 (by
      have h' := eq_neg_of_add_eq_zero_right h
      rw [CharTwo.neg_eq] at h'
      exact h')
    obtain ⟨ℓ, r, φ, hℓ0, hn', hφN, hdet, hunit⟩ := exists_unitary_adapted hU hN hNh hN0
    have hφM : φ (M : Matrix (Fin n) (Fin n) K) = 1 + sqZeroStd ℓ r := by
      rw [show (M : Matrix (Fin n) (Fin n) K) = 1 + ((M : Matrix (Fin n) (Fin n) K) - 1) from
        (add_sub_cancel 1 _).symm, map_add, map_one, hφN]
    intro u hu hu2 horb a ha
    obtain ⟨U, hUr⟩ := exists_represents e (mem_inf.mp hu).1
    have hup : u * p = p * u := mem_centralizer_singleton_iff.mp (mem_inf.mp hu).2
    have hUM := hUr.mul_comm_of_commute hpM hMsq hup
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : K, (U : Matrix (Fin n) (Fin n) K) * U = c₀ • 1 := by
      have h1 : Represents e (u * u) (U * U) := hUr.mul hUr
      rw [← sq, hu2] at h1
      obtain ⟨c, hc⟩ := represents_one.exists_scalar h1
      refine ⟨c, ?_⟩
      have h := congrArg (fun Y : GL (Fin n) K => (Y : Matrix (Fin n) (Fin n) K)) hc
      simp only [Units.val_mul, one_mul, Matrix.GeneralLinearGroup.coe_scalar] at h
      rw [h, Matrix.smul_one_eq_diagonal]
      rfl
    have hBS : Commute (φ (U : Matrix (Fin n) (Fin n) K)) (sqZeroStd ℓ r) := by
      have h2 := congrArg φ hUM
      rw [map_mul, map_mul, hφM, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
        Matrix.one_mul] at h2
      exact add_left_cancel h2
    have hlift : ∀ R : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
        adjM σ R * unitGram K ℓ r * R = unitGram K ℓ r → R.det = 1 →
        Commute R (sqZeroStd ℓ r) →
        ∃ Rv : GL (Fin n) K, Rv ∈ StatedSU n (2 ^ m) K ∧ Rv * M = M * Rv ∧
          φ (Rv : Matrix (Fin n) (Fin n) K) = R := by
      intro R hRJ hRdet hRS
      have hdet' : (φ.symm R).det ≠ 0 := by rw [hdet, hRdet]; exact one_ne_zero
      refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet',
        mem_statedSU_of hσq (by rw [show ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet' :
          GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = φ.symm R from rfl, hdet, hRdet])
          (hunit R hRJ), Units.ext (φ.injective ?_), AlgEquiv.apply_symm_apply φ R⟩
      rw [Units.val_mul, Units.val_mul, map_mul, map_mul,
        show ((Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet' : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) = φ.symm R from rfl, AlgEquiv.apply_symm_apply, hφM,
        Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, hRS.eq]
    have hT : ∀ R₁ R₂ : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
        adjM σ R₁ * unitGram K ℓ r * R₁ = unitGram K ℓ r → R₁.det = 1 →
        Commute R₁ (sqZeroStd ℓ r) →
        adjM σ R₂ * unitGram K ℓ r * R₂ = unitGram K ℓ r → R₂.det = 1 →
        Commute R₂ (sqZeroStd ℓ r) →
        Commute (φ (U : Matrix (Fin n) (Fin n) K)) R₁ ∨
          Commute (φ (U : Matrix (Fin n) (Fin n) K)) R₂ ∨
          Commute (φ (U : Matrix (Fin n) (Fin n) K)) (R₁ * R₂) := by
      intro R₁ R₂ h1J h1d h1S h2J h2d h2S
      obtain ⟨Rv₁, h1H, h1M, h1φ⟩ := hlift R₁ h1J h1d h1S
      obtain ⟨Rv₂, h2H, h2M, h2φ⟩ := hlift R₂ h2J h2d h2S
      rcases commute_trichotomy hZ hp2' hpM horb hUr hc₀ h1H h2H h1M h2M with h | h | h
      · left
        have h' := congrArg φ h
        rw [map_mul, map_mul, h1φ] at h'
        exact h'.symm
      · right; left
        have h' := congrArg φ h
        rw [map_mul, map_mul, h2φ] at h'
        exact h'.symm
      · right; right
        have h' := congrArg φ h
        simp only [Units.val_mul, map_mul, h1φ, h2φ] at h'
        exact h'.symm
    have hSq : ∀ R : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
        adjM σ R * unitGram K ℓ r * R = unitGram K ℓ r → R.det = 1 →
        Commute R (sqZeroStd ℓ r) → Commute (φ (U : Matrix (Fin n) (Fin n) K)) (R * R) := by
      intro R hRJ hRd hRS
      obtain ⟨Rv, hH, hM, hφR⟩ := hlift R hRJ hRd hRS
      have h' := congrArg φ (commute_sq_of_pairOrbit hZ hp2' hpM horb hUr hc₀ hH hM)
      simp only [Units.val_mul, map_mul, hφR] at h'
      exact h'.symm
    have hEc : ∀ E : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K,
        E * E = 0 → adjM σ E * unitGram K ℓ r = unitGram K ℓ r * E →
        Commute E (sqZeroStd ℓ r) → Commute (φ (U : Matrix (Fin n) (Fin n) K)) E := by
      intro E hE2 hEJ hES
      have hR : ∀ t : K, σ t = t →
          adjM σ (1 + t • E) * unitGram K ℓ r * (1 + t • E) = unitGram K ℓ r ∧
            (1 + t • E).det = 1 ∧ Commute (1 + t • E) (sqZeroStd ℓ r) := by
        intro t ht
        have hE2' : (t • E) * (t • E) = 0 := by
          rw [Matrix.smul_mul, Matrix.mul_smul, hE2, smul_zero, smul_zero]
        refine ⟨adjM_one_add_smul_mul_unitGram hEJ hE2 ht, ?_, ?_⟩
        · have h := det_unipGL hE2' (1 : K)
          rwa [coe_unipGL, one_smul] at h
        · exact (Commute.one_left _).add_left (hES.smul_left t)
      obtain ⟨h1J, h1d, h1S⟩ := hR 1 (map_one σ)
      obtain ⟨h2J, h2d, h2S⟩ := hR μ hμσ
      have hone' : Commute (φ (U : Matrix (Fin n) (Fin n) K)) 1 := Commute.one_right _
      rcases hT _ _ h1J h1d h1S h2J h2d h2S with h | h | h
      · have h' := h.sub_right hone'
        rw [add_sub_cancel_left, one_smul] at h'
        exact h'
      · have h' := h.sub_right hone'
        rw [add_sub_cancel_left] at h'
        exact commute_of_smul_ne_zero hμ0 h'
      · have hprod : (1 + (1 : K) • E) * (1 + μ • E) = 1 + (1 + μ) • E := by
          rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
            Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, hE2, smul_zero, smul_zero,
            add_zero, add_smul]
          abel
        rw [hprod] at h
        have h' := h.sub_right hone'
        rw [add_sub_cancel_left] at h'
        exact commute_of_smul_ne_zero h1μ h'
    have hC1 : ∀ i j : Fin ℓ, i ≠ j →
        Commute (φ (U : Matrix (Fin n) (Fin n) K)) (Matrix.single (.inr (.inl i)) (.inl j) 1) := by
      intro i j hij
      have hs : ∀ s : K, Commute (φ (U : Matrix (Fin n) (Fin n) K))
          (s • Matrix.single (.inr (.inl j)) (.inl i) 1 +
            σ s • Matrix.single (.inr (.inl i)) (.inl j) 1) := fun s => by
        rw [← symP_w_w]
        exact hEc _ (symP_w_w_mul_self j i s) (symP_adj hσ _ _) (symP_w_w_commute j i s)
      have h : Commute (φ (U : Matrix (Fin n) (Fin n) K))
          ((θ - σ θ) • Matrix.single (.inr (.inl i)) (.inl j) 1) := by
        refine commute_of_eq (((hs 1).smul_right θ).sub_right (hs θ)) ?_
        rw [map_one]
        module
      exact commute_of_smul_ne_zero hθ0 h
    have hC4 : ∀ i j : Fin ℓ, i ≠ j →
        Commute (φ (U : Matrix (Fin n) (Fin n) K)) (Matrix.single (.inl i) (.inl j) 1 +
          Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1) := by
      intro i j hij
      have hG : ∀ ζ : K, σ ζ * ζ = 1 → Commute (φ (U : Matrix (Fin n) (Fin n) K))
          (symP σ (Pi.single (.inl i) 1 + ζ • Pi.single (.inl j) 1)
            (Pi.single (.inr (.inl i)) 1 + ζ • Pi.single (.inr (.inl j)) 1)) := fun ζ hζ =>
        hEc _ (symP_xw_mul_self hij hζ) (symP_adj hσ _ _) (symP_xw_commute i j ζ)
      have h1 := hG 1 hone
      have h : Commute (φ (U : Matrix (Fin n) (Fin n) K))
          (((1 - σ z) * (z - σ z)) • (Matrix.single (.inl i) (.inl j) 1 +
            Matrix.single (.inr (.inl i)) (.inr (.inl j)) 1)) := by
        refine commute_of_eq (((h1.sub_right (hG z hz')).smul_right (1 + z)).sub_right
          (h1.sub_right (hG (z * z) hz2))) ?_
        rw [symP_xw, symP_xw, symP_xw, map_one, map_mul, hzz, hzz2]
        module
      exact commute_of_smul_ne_zero
        (mul_ne_zero (sub_ne_zero.mpr (Ne.symm hσz1)) (sub_ne_zero.mpr hzσz)) h
    have hY : ∀ (j : Fin ℓ) (k : Fin r),
        Commute (φ (U : Matrix (Fin n) (Fin n) K)) (Matrix.single (.inr (.inr k)) (.inl j) 1) ∧
        Commute (φ (U : Matrix (Fin n) (Fin n) K))
          (Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
      intro j k
      have hZd : ∀ t c : K, c + σ c = σ t * t →
          adjM σ (1 + zY σ j k t c) * unitGram K ℓ r * (1 + zY σ j k t c) = unitGram K ℓ r ∧
            (1 + zY σ j k t c).det = 1 ∧ Commute (1 + zY σ j k t c) (sqZeroStd ℓ r) := by
        intro t c htc
        refine ⟨adjM_one_add_zY hσ j k htc, ?_, (Commute.one_left _).add_left (zY_commute j k t c)⟩
        set D : Matrix (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) (Fin ℓ ⊕ (Fin ℓ ⊕ Fin r)) K :=
          Matrix.single (.inr (.inl j)) (.inl j) 1 with hDdef
        have hsq : (1 + zY σ j k t c) * (1 + zY σ j k t c) = 1 + (σ t * t) • D := by
          rw [one_add_zY_mul, zY_eq, hDdef]
          simp only [CharTwo.add_self_eq_zero, zero_add, zero_smul, map_zero]
        have hD2 : ((σ t * t) • D) * ((σ t * t) • D) = 0 := by
          rw [Matrix.smul_mul, Matrix.mul_smul, hDdef,
            single_mul_single_of_ne (1 : K) _ _ _ (by simp) 1, smul_zero, smul_zero]
        have hdsq : ((1 + zY σ j k t c) * (1 + zY σ j k t c)).det = 1 := by
          rw [hsq]
          have h := det_unipGL hD2 (1 : K)
          rwa [coe_unipGL, one_smul] at h
        rw [Matrix.det_mul] at hdsq
        exact eq_one_of_sq_eq_one_of_charTwo (by rw [sq]; exact hdsq)
      obtain ⟨c₁, hc₁⟩ := htr (σ 1 * 1) (by rw [map_mul, map_one, map_one])
      obtain ⟨h1J, h1d, h1S⟩ := hZd 1 c₁ hc₁
      have hD : Commute (φ (U : Matrix (Fin n) (Fin n) K))
          (Matrix.single (.inr (.inl j)) (.inl j) 1) := by
        have h := hSq _ h1J h1d h1S
        rw [one_add_zY_mul, zY_eq, h2two, CharTwo.add_self_eq_zero c₁, hone] at h
        simp only [zero_add, zero_smul, map_zero, one_smul] at h
        have h' := h.sub_right (Commute.one_right _)
        rwa [add_sub_cancel_left] at h'
      have hP : ∀ t : K, Commute (φ (U : Matrix (Fin n) (Fin n) K))
          (t • Matrix.single (.inr (.inr k)) (.inl j) 1 +
            σ t • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
        intro t
        obtain ⟨c₁, hc₁⟩ := htr (σ t * t) (by rw [map_mul, hσ, mul_comm])
        obtain ⟨c₂, hc₂⟩ := htr (σ (μ * t) * (μ * t)) (by rw [map_mul, hσ, mul_comm])
        obtain ⟨h1J, h1d, h1S⟩ := hZd t c₁ hc₁
        obtain ⟨h2J, h2d, h2S⟩ := hZd (μ * t) c₂ hc₂
        have hlin : ∀ (κ c : K), σ κ = κ → κ ≠ 0 →
            Commute (φ (U : Matrix (Fin n) (Fin n) K)) (1 + zY σ j k (κ * t) c) →
            Commute (φ (U : Matrix (Fin n) (Fin n) K))
              (t • Matrix.single (.inr (.inr k)) (.inl j) 1 +
                σ t • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
          intro κ c hκ hκ0 h
          have h' := (h.sub_right (Commute.one_right _)).sub_right (hD.smul_right c)
          have e : 1 + zY σ j k (κ * t) c - 1 - c • Matrix.single (.inr (.inl j)) (.inl j) 1 =
              κ • (t • Matrix.single (.inr (.inr k)) (.inl j) 1 +
                σ t • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
            rw [zY_eq, map_mul, hκ]
            module
          rw [e] at h'
          exact commute_of_smul_ne_zero hκ0 h'
        rcases hT _ _ h1J h1d h1S h2J h2d h2S with h | h | h
        · exact hlin 1 c₁ (map_one σ) one_ne_zero (by rwa [one_mul])
        · exact hlin μ c₂ hμσ hμ0 h
        · rw [one_add_zY_mul] at h
          refine hlin (1 + μ) (c₁ + c₂ + σ t * (μ * t)) (by rw [map_add, map_one, hμσ]) h1μ ?_
          rwa [add_mul, one_mul]
      have hA := hP 1
      have hB' := hP θ
      have hw : Commute (φ (U : Matrix (Fin n) (Fin n) K))
          ((θ - σ θ) • Matrix.single (.inr (.inl j)) (.inr (.inr k)) 1) := by
        refine commute_of_eq ((hA.smul_right θ).sub_right hB') ?_
        rw [map_one]
        module
      have hw' := commute_of_smul_ne_zero hθ0 hw
      refine ⟨commute_of_eq (hA.sub_right hw') ?_, hw'⟩
      rw [map_one]
      module
    obtain ⟨c, d, hcd⟩ := commutant_kappa hℓ0 (by omega) hBS hC1 (fun k j => (hY j k).1)
      (fun i k => (hY i k).2) hC4
    set N := (M : Matrix (Fin n) (Fin n) K) - 1 with hNdef
    have hUcd : (U : Matrix (Fin n) (Fin n) K) = c • 1 + d • N := by
      apply φ.injective
      rw [hcd, map_add, map_smul, map_smul, map_one, hφN]
    have hUu := adjM_mul_self_of_mem_statedSU hσ hσq hUr.2.1
    rw [hUcd, adjM_add, adjM_smul, adjM_smul, adjM_one, hNh] at hUu
    have hexp : (σ c • (1 : Matrix (Fin n) (Fin n) K) + σ d • N) * (c • 1 + d • N) =
        (σ c * c) • 1 + (σ c * d + σ d * c) • N := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one, hN, smul_zero, add_zero, smul_smul]
      module
    rw [hexp] at hUu
    have hcc : σ c * c = 1 := by
      have h1 := congrArg (fun Y => Y * N) hUu
      simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, hN, smul_zero,
        add_zero] at h1
      have h2 : (σ c * c - 1) • N = 0 := by rw [sub_smul, one_smul, h1, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hN0
    have hcd' : σ c * d + σ d * c = 0 := by
      rw [hcc, one_smul] at hUu
      rcases smul_eq_zero.mp (add_eq_left.mp hUu) with h | h
      · exact h
      · exact absurd h hN0
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hcc
      exact zero_ne_one hcc
    have hσc0 : σ c ≠ 0 := (map_ne_zero σ).mpr hc0
    have haσ : σ (d / c) = d / c := by
      rw [map_div₀, div_eq_div_iff hσc0 hc0]
      have h1 : σ d * c = σ c * d := by
        rw [← CharTwo.neg_eq (σ c * d)]
        exact eq_neg_of_add_eq_zero_right hcd'
      rw [h1, mul_comm]
    have hYSU : unipGL N hN (d / c) ∈ StatedSU n (2 ^ m) K := by
      refine mem_statedSU_of hσq (det_unipGL hN _) ?_
      have h1 : adjM σ (unipGL N hN (d / c) : Matrix (Fin n) (Fin n) K) =
          unipGL N hN (d / c) := by
        rw [coe_unipGL, adjM_add, adjM_one, adjM_smul, haσ, hNh]
      rw [h1, ← Units.val_mul, ← sq, unipGL_sq, Units.val_one]
    have hrep : Represents e u (unipGL N hN (d / c)) :=
      hUr.of_eq_mul_scalar hYSU (c := Units.mk0 c hc0) (Units.ext (by
        rw [hUcd, Units.val_mul, coe_unipGL, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0,
          Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, add_mul, Matrix.one_mul,
          Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
        have hcd'' : c * (d / c) = d := by field_simp
        rw [hcd'']))
    have hmem : u ∈ alphaGroup e p :=
      subset_closure ⟨⟨1, by rw [pow_one]; exact hu2⟩, M, unipGL N hN (d / c), hpM, hM2, hrep,
        d / c, by rw [coe_unipGL, add_sub_cancel_left]⟩
    have hau : a * u = u * a :=
      mem_centralizer_iff.mp (alphaGroup_le_centralizer hZ hpM hM2 hmem) a ha
    rw [hau, mul_inv_cancel_right]
  | linear => simp [ClassicalModel.family] at hD
  | symplectic => simp [ClassicalModel.family] at hD
  | orthPlus => simp [ClassicalModel.family] at hD
  | orthMinus => simp [ClassicalModel.family] at hD

end Unitary

end CFSG.ComponentClassification.RankTwoClassical
