module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdNineBasic
public import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Linear
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Assembly.LowTwoRank CFSG.SectionRank.ClassicalEven Matrix

section StatedProj

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

theorem hasElemAb_nine_statedProj {H : Subgroup (GL ι K)} {x y : GL ι K} (hxH : x ∈ H) (hyH : y ∈ H)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : ∃ c ∈ StatedScalars ι K, x * y = y * x * c)
    (hx1 : x ∉ StatedScalars ι K) (hy1 : ∀ n : ℕ, ∀ c ∈ StatedScalars ι K, x ^ n * c ≠ y) :
    HasElemAb 3 9 (StatedProj H) := by
  let N : Subgroup H := (StatedScalars ι K).subgroupOf H
  let π : H →* StatedProj H := QuotientGroup.mk' N
  have hmem : ∀ u v : H, π u = π v → ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v at h
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at h
    simpa using h
  have hmem' : ∀ u v : H, ((u : GL ι K)⁻¹ * v) ∈ StatedScalars ι K → π u = π v := fun u v h => by
    change QuotientGroup.mk' N u = QuotientGroup.mk' N v
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using h
  have hpow : ∀ (a : GL ι K) (ha : a ∈ H), a ^ 3 = 1 → π ⟨a, ha⟩ ^ 3 = 1 := fun a ha h => by
    rw [← map_pow]
    have : (⟨a, ha⟩ : H) ^ 3 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact h)
    rw [this, map_one]
  refine hasElemAb_nine_of_gens (x := π ⟨x, hxH⟩) (y := π ⟨y, hyH⟩) (hpow x hxH hx)
    (hpow y hyH hy) ?_ (fun h => hx1 ?_) (fun n h => ?_)
  · obtain ⟨c, hc, hcomm⟩ := hxy
    show π ⟨x, hxH⟩ * π ⟨y, hyH⟩ = π ⟨y, hyH⟩ * π ⟨x, hxH⟩
    rw [← map_mul, ← map_mul]
    refine hmem' _ _ ?_
    have : ((⟨x, hxH⟩ * ⟨y, hyH⟩ : H) : GL ι K)⁻¹ * ((⟨y, hyH⟩ * ⟨x, hxH⟩ : H) : GL ι K) = c⁻¹ := by
      show (x * y)⁻¹ * (y * x) = c⁻¹
      rw [hcomm]
      group
    rw [this]
    exact (StatedScalars ι K).inv_mem hc
  · have := hmem _ _ (h.trans (map_one π).symm)
    simpa using this
  · rw [← map_pow] at h
    have := hmem _ _ h
    simp only [SubgroupClass.coe_pow] at this
    exact hy1 n _ this (mul_inv_cancel_left _ _)

end StatedProj

theorem hasElemAb_nine_psl_five (K : Type) [Field K] :
    HasElemAb 3 9 (StatedProj (StatedSL 5 K)) := by
  refine hasElemAb_nine_statedProj (x := rotGL (0 : Fin 5) 1) (y := rotGL 2 3)
    (Subgroup.subset_closure (det_rotMatrix _ _)) (Subgroup.subset_closure (det_rotMatrix _ _))
    (rotGL_pow_three _ _) (rotGL_pow_three _ _)
    ⟨1, (StatedScalars _ K).one_mem, ?_⟩
    (fun hx => mul_scalar_ne (g := 1) (h := rotGL (0 : Fin 5) 1) (a := 0) (b := 1) (by decide)
      (one_mulVec _) (rotMatrix_mulVec_left _ _) hx (one_mul _))
    (fun n c hc => mul_scalar_ne (a := 2) (b := 3) (by decide)
      (rotGL_pow_mulVec_of_ne (by decide) (by decide) n) (rotMatrix_mulVec_left _ _) hc)
  rw [mul_one]
  exact (rotGL_commute (by decide) (by decide) (by decide) (by decide)).eq

theorem hasElemAb_nine_psp_four (K : Type) [Field K] :
    HasElemAb 3 9 (StatedProj (StatedSp 2 K)) := by
  refine hasElemAb_nine_statedProj (x := rotGL (Sum.inl (0 : Fin 2)) (Sum.inr 0))
    (y := rotGL (Sum.inl 1) (Sum.inr 1))
    (Subgroup.subset_closure (rotMatrix_inl_inr_symplectic _))
    (Subgroup.subset_closure (rotMatrix_inl_inr_symplectic _))
    (rotGL_pow_three _ _) (rotGL_pow_three _ _)
    ⟨1, (StatedScalars _ K).one_mem, ?_⟩
    (fun hx => mul_scalar_ne (g := 1) (h := rotGL (Sum.inl (0 : Fin 2)) (Sum.inr 0))
      (a := Sum.inl 0) (b := Sum.inr 0) (by decide)
      (one_mulVec _) (rotMatrix_mulVec_left _ _) hx (one_mul _))
    (fun n c hc => mul_scalar_ne (a := Sum.inl 1) (b := Sum.inr 1) (by decide)
      (rotGL_pow_mulVec_of_ne (by decide) (by decide) n) (rotMatrix_mulVec_left _ _) hc)
  rw [mul_one]
  exact (rotGL_commute (by decide) (by decide) (by decide) (by decide)).eq

section L34

variable {K : Type} [Field K]

@[expose] noncomputable def tMat (ω : K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.diagonal ![1, ω, ω ^ 2]

@[expose] def pMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; 0, 0, 1; 1, 0, 0]

theorem det_pMat : (pMat : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [pMat, Matrix.det_fin_three]

theorem det_tMat {ω : K} (h : ω ^ 3 = 1) : (tMat ω).det = 1 := by
  simp [tMat, Matrix.det_diagonal, Fin.prod_univ_three]
  rw [← pow_succ']
  exact h

theorem pMat_pow_three : (pMat : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
  ext i j
  simp [pMat, pow_succ]
  fin_cases i <;> fin_cases j <;> simp

theorem tMat_pow_three {ω : K} (h : ω ^ 3 = 1) : tMat ω ^ 3 = 1 := by
  rw [tMat, Matrix.diagonal_pow]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [← pow_mul]
  · rw [h]
  · rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, h, one_pow]

@[expose] noncomputable def tGL (ω : K) (h : ω ^ 3 = 1) : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mk'' (tMat ω) (by rw [det_tMat h]; exact isUnit_one)

@[expose] noncomputable def pGL : GL (Fin 3) K :=
  Matrix.GeneralLinearGroup.mk'' pMat (by rw [det_pMat]; exact isUnit_one)

theorem coe_tGL (ω : K) (h : ω ^ 3 = 1) :
    ((tGL ω h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = tMat ω :=
  rfl

theorem coe_pGL : ((pGL : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = pMat :=
  rfl

theorem tGL_pow_three (ω : K) (h : ω ^ 3 = 1) : tGL ω h ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, coe_tGL, tMat_pow_three h, Units.val_one])

theorem pGL_pow_three : (pGL : GL (Fin 3) K) ^ 3 = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, coe_pGL, pMat_pow_three, Units.val_one])

theorem tGL_mul_pGL (ω : Kˣ) (h : ((ω : Kˣ) : K) ^ 3 = 1) :
    tGL ((ω : Kˣ) : K) h * pGL =
      pGL * tGL ((ω : Kˣ) : K) h * Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_tGL, coe_pGL,
    Matrix.GeneralLinearGroup.coe_scalar]
  have hm1 : ((ω : Kˣ) : K) * ((ω : Kˣ) : K) ^ 2 = 1 := by
    rw [← pow_succ']
    exact h
  have hm2 : ((ω : Kˣ) : K) ^ 2 * ((ω : Kˣ) : K) ^ 2 = ((ω : Kˣ) : K) := by
    rw [← pow_add, show (2 + 2 : ℕ) = 3 + 1 from rfl, pow_succ, h, one_mul]
  ext i j
  simp only [tMat, Matrix.scalar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  fin_cases i <;> fin_cases j <;> simp [pMat, hm1, hm2]

theorem tGL_not_scalar (ω : Kˣ) (h : ((ω : Kˣ) : K) ^ 3 = 1) (h1 : ((ω : Kˣ) : K) ≠ 1) :
    tGL ((ω : Kˣ) : K) h ∉ (Matrix.GeneralLinearGroup.scalar (Fin 3) (R := K)).range := by
  rintro ⟨u, hu⟩
  have h00 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 0 0) hu
  have h11 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 1 1) hu
  simp [Matrix.GeneralLinearGroup.coe_scalar, coe_tGL, tMat, Matrix.scalar_apply] at h00 h11
  rw [h00, Units.val_one] at h11
  exact h1 h11.symm

theorem tGL_pow_mul_scalar_ne (ω : K) (h : ω ^ 3 = 1) (n : ℕ) (u : Kˣ) :
    tGL ω h ^ n * Matrix.GeneralLinearGroup.scalar (Fin 3) u ≠ pGL := by
  intro hh
  have h20 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) 2 0) hh
  simp [Units.val_mul, Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar, coe_tGL,
    coe_pGL, tMat, pMat, Matrix.diagonal_pow, Matrix.scalar_apply] at h20

theorem hasElemAb_nine_psl_three_four [Finite K] (hK : Nat.card K = 4) :
    HasElemAb 3 9 (StatedProj (StatedSL 3 K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK]
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [hcard])
  have h3 : ((ω : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hω, pow_orderOf_eq_one, Units.val_one]
  have h1 : ((ω : Kˣ) : K) ≠ 1 := by
    intro h
    have : ω = 1 := Units.ext h
    rw [this, orderOf_one] at hω
    omega
  refine hasElemAb_nine_statedProj (x := tGL ((ω : Kˣ) : K) h3) (y := pGL)
    (Subgroup.subset_closure (det_tMat h3)) (Subgroup.subset_closure det_pMat)
    (tGL_pow_three _ _) pGL_pow_three
    ⟨Matrix.GeneralLinearGroup.scalar (Fin 3) (ω ^ 2), ⟨ω ^ 2, rfl⟩, tGL_mul_pGL ω h3⟩
    (tGL_not_scalar ω h3 h1) (fun n c hc => by
      obtain ⟨u, rfl⟩ := hc
      exact tGL_pow_mul_scalar_ne _ h3 n u)

end L34

end CFSG.QuasithinUnique.Id2519
