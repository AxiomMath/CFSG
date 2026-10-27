module

public import CFSG.ClassicalGroups.Unitary.Form

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.BGL

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary

variable {K : Type*} [Field K] {σ : K ≃+* K}

variable (σ) in
@[expose] noncomputable def thetaMat (a b : Fin 3 → K) (τ τ' p q r s : K) :
    Matrix (Fin 3) (Fin 3) K :=
  1 + vecMulVec ((p - 1) • a + (τ' * r) • b) (fun i => σ (b i)) +
    vecMulVec ((τ * q) • a + (s - 1) • b) (fun i => σ (a i))

theorem thetaMat_mulVec (a b : Fin 3 → K) (τ τ' p q r s : K) (x : Fin 3 → K) :
    thetaMat σ a b τ τ' p q r s *ᵥ x = x + herm σ b x • ((p - 1) • a + (τ' * r) • b) +
      herm σ a x • ((τ * q) • a + (s - 1) • b) := by
  rw [thetaMat, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, op_smul_eq_smul]
  rfl

variable (σ) in
structure HypPair where
  a : Fin 3 → K
  b : Fin 3 → K
  τ : K
  τ' : K
  inv : ∀ c, σ (σ c) = c
  ha : herm σ a a = 0
  hb : herm σ b b = 0
  hab : herm σ a b = 1
  hτ : τ + σ τ = 0
  hττ' : τ * τ' = 1

namespace HypPair

variable (P : HypPair σ)

theorem hba : herm σ P.b P.a = 1 := by rw [herm_conj σ P.inv, P.hab, map_one]

theorem τ_ne_zero : P.τ ≠ 0 := left_ne_zero_of_mul_eq_one P.hττ'

theorem hτ' : P.τ' + σ P.τ' = 0 := by
  have h1 : σ P.τ * σ P.τ' = 1 := by rw [← map_mul, P.hττ', map_one]
  have h2 : σ P.τ = -P.τ := by linear_combination P.hτ
  rw [h2] at h1
  have h3 : P.τ * (P.τ' + σ P.τ') = 0 := by linear_combination P.hττ' - h1
  exact (mul_eq_zero.mp h3).resolve_left P.τ_ne_zero

@[expose] noncomputable def mat (p q r s : K) : Matrix (Fin 3) (Fin 3) K :=
  thetaMat σ P.a P.b P.τ P.τ' p q r s

theorem mat_mulVec (p q r s : K) (x : Fin 3 → K) :
    P.mat p q r s *ᵥ x = x + herm σ P.b x • ((p - 1) • P.a + (P.τ' * r) • P.b) +
      herm σ P.a x • ((P.τ * q) • P.a + (s - 1) • P.b) :=
  thetaMat_mulVec _ _ _ _ _ _ _ _ _

theorem mat_det {p q r s : K} (hdet : p * s - q * r = 1) : (P.mat p q r s).det = 1 := by
  set u : Fin 3 → K := (p - 1) • P.a + (P.τ' * r) • P.b with hu
  set u' : Fin 3 → K := (P.τ * q) • P.a + (s - 1) • P.b with hu'
  let A : Matrix (Fin 3) (Fin 2) K := Matrix.of fun i j => ![u i, u' i] j
  let B : Matrix (Fin 2) (Fin 3) K := Matrix.of fun j i => ![σ (P.b i), σ (P.a i)] j
  have hAB : P.mat p q r s = 1 + A * B := by
    ext i j
    simp [A, B, mat, thetaMat, Matrix.mul_apply, Fin.sum_univ_two, vecMulVec_apply, add_assoc, hu,
      hu']
  have hBA : B * A = !![herm σ P.b u, herm σ P.b u'; herm σ P.a u, herm σ P.a u'] := by
    ext j k
    fin_cases j <;> fin_cases k <;>
      simp [A, B, Matrix.mul_apply, herm, Fin.sum_univ_three]
  rw [hAB, Matrix.det_one_add_mul_comm, hBA]
  have e1 : herm σ P.b u = p - 1 := by
    rw [hu, herm_add_right, herm_smul_right, herm_smul_right, P.hba, P.hb]; ring
  have e2 : herm σ P.b u' = P.τ * q := by
    rw [hu', herm_add_right, herm_smul_right, herm_smul_right, P.hba, P.hb]; ring
  have e3 : herm σ P.a u = P.τ' * r := by
    rw [hu, herm_add_right, herm_smul_right, herm_smul_right, P.hab, P.ha]; ring
  have e4 : herm σ P.a u' = s - 1 := by
    rw [hu', herm_add_right, herm_smul_right, herm_smul_right, P.hab, P.ha]; ring
  rw [e1, e2, e3, e4, Matrix.det_fin_two]
  simp
  linear_combination hdet - (q * r) * P.hττ'

theorem mat_isometry {p q r s : K} (hp : σ p = p) (hq : σ q = q) (hr : σ r = r) (hs : σ s = s)
    (hdet : p * s - q * r = 1) (x y : Fin 3 → K) :
    herm σ (P.mat p q r s *ᵥ x) (P.mat p q r s *ᵥ y) = herm σ x y := by
  have hσt : σ P.τ = -P.τ := by linear_combination P.hτ
  have hσt' : σ P.τ' = -P.τ' := by linear_combination P.hτ'
  have hax : herm σ x P.a = σ (herm σ P.a x) := herm_conj σ P.inv P.a x
  have hbx : herm σ x P.b = σ (herm σ P.b x) := herm_conj σ P.inv P.b x
  rw [mat_mulVec, mat_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, P.ha, P.hb, P.hab,
    P.hba, hax, hbx, map_sub, map_one, map_mul, hp, hq, hr, hs, hσt, hσt']
  linear_combination (σ (herm σ P.a x) * herm σ P.b y + σ (herm σ P.b x) * herm σ P.a y) *
    (hdet - q * r * P.hττ')

@[expose] noncomputable def theta {p q r s : K} (hp : σ p = p) (hq : σ q = q) (hr : σ r = r)
    (hs : σ s = s) (hdet : p * s - q * r = 1) : SUid σ 3 :=
  mkSU σ (P.mat p q r s) (P.mat_det hdet) (fun x y => P.mat_isometry hp hq hr hs hdet x y)

theorem theta_smul {p q r s : K} (hp : σ p = p) (hq : σ q = q) (hr : σ r = r)
    (hs : σ s = s) (hdet : p * s - q * r = 1) (x : Fin 3 → K) :
    P.theta hp hq hr hs hdet • x = x + herm σ P.b x • ((p - 1) • P.a + (P.τ' * r) • P.b) +
      herm σ P.a x • ((P.τ * q) • P.a + (s - 1) • P.b) :=
  P.mat_mulVec p q r s x

end HypPair

variable (σ) in
@[expose] def Efix : Subfield K := RingHom.eqLocusField σ.toRingHom (RingHom.id K)

theorem mem_Efix {x : K} : x ∈ Efix σ ↔ σ x = x := Iff.rfl

theorem sl2_entries (M : Matrix.SpecialLinearGroup (Fin 2) (Efix σ)) :
    σ (M 0 0 : K) = M 0 0 ∧ σ (M 0 1 : K) = M 0 1 ∧ σ (M 1 0 : K) = M 1 0 ∧
      σ (M 1 1 : K) = M 1 1 ∧ (M 0 0 : K) * M 1 1 - (M 0 1 : K) * M 1 0 = 1 := by
  refine ⟨(M 0 0).2, (M 0 1).2, (M 1 0).2, (M 1 1).2, ?_⟩
  have h := M.det_coe
  rw [Matrix.det_fin_two] at h
  have := congrArg (fun z : Efix σ => (z : K)) h
  simpa using this

namespace HypPair

variable (P : HypPair σ)

@[expose] noncomputable def thetaSL (M : Matrix.SpecialLinearGroup (Fin 2) (Efix σ)) :
    SUid σ 3 :=
  P.theta (sl2_entries M).1 (sl2_entries M).2.1 (sl2_entries M).2.2.1
    (sl2_entries M).2.2.2.1 (sl2_entries M).2.2.2.2

theorem thetaSL_smul (M : Matrix.SpecialLinearGroup (Fin 2) (Efix σ)) (x : Fin 3 → K) :
    P.thetaSL M • x = x + herm σ P.b x • (((M 0 0 : K) - 1) • P.a + (P.τ' * (M 1 0 : K)) • P.b) +
      herm σ P.a x • ((P.τ * (M 0 1 : K)) • P.a + ((M 1 1 : K) - 1) • P.b) :=
  P.theta_smul _ _ _ _ _ x

theorem thetaSL_mul (M N : Matrix.SpecialLinearGroup (Fin 2) (Efix σ)) :
    P.thetaSL (M * N) = P.thetaSL M * P.thetaSL N := by
  apply ext_smul
  intro x
  rw [mul_smul, thetaSL_smul, thetaSL_smul, thetaSL_smul]
  simp only [herm_add_right, herm_smul_right, P.ha, P.hb, P.hab, P.hba, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Subfield.coe_add, Subfield.coe_mul, mul_zero, mul_one, add_zero]
  have hτ0 := P.τ_ne_zero
  have hτ' : P.τ' = P.τ⁻¹ := eq_inv_of_mul_eq_one_right P.hττ'
  match_scalars
  all_goals
    try rw [hτ']
    try field_simp
    try ring

@[expose] noncomputable def thetaHom : Matrix.SpecialLinearGroup (Fin 2) (Efix σ) →* SUid σ 3 :=
  MonoidHom.mk' P.thetaSL P.thetaSL_mul

theorem thetaHom_apply (M : Matrix.SpecialLinearGroup (Fin 2) (Efix σ)) :
    P.thetaHom M = P.thetaSL M := rfl

end HypPair

end CFSG.HardMathSupport.Solomon.Coordinator.BGL
