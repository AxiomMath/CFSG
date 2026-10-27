module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.LocalAnalysis.ComponentInitial.SymplecticFour

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {K : Type} [Field K]

@[expose] def unitri (a : K) : Matrix (Fin 2) (Fin 2) K := !![1, a; 0, 1]

theorem det_unitri (a : K) : (unitri a).det = 1 := by
  simp [unitri, det_fin_two]

theorem isUnitriangular_unitri (a : K) : IsUnitriangular (unitri a) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [unitri]
  · fin_cases i <;> simp [unitri]

theorem unitri_mul (a b : K) : unitri a * unitri b = unitri (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitri, mul_apply, Fin.sum_univ_two, add_comm]

theorem unitri_zero : unitri (0 : K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitri, one_apply]

theorem inv_unitri (a : K) : (unitri a)⁻¹ = unitri (-a) := by
  refine inv_eq_left_inv ?_
  rw [unitri_mul, neg_add_cancel, unitri_zero]

@[expose] noncomputable def tau {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : StatedSp 2 K :=
  upperUnipotentSp 2 K hC

theorem coe_tau {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    (((tau hC : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks 1 C 0 1 :=
  coe_upperUnipotentSp hC

@[expose] noncomputable def lam (a : K) : StatedSp 2 K :=
  blockElt (by rw [det_unitri]; exact isUnit_one) (transpose_zero (m := Fin 2) (n := Fin 2))
    (A := unitri a)

theorem coe_lam (a : K) :
    (((lam a : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = fromBlocks (unitri a) 0 0 (unitri (-a))ᵀ := by
  rw [lam, coe_blockElt, blockMat, Matrix.mul_zero, inv_unitri]

@[expose] def sym2 (b c d : K) : Matrix (Fin 2) (Fin 2) K := !![b, c; c, d]

omit [Field K] in
theorem sym2_transpose (b c d : K) : (sym2 b c d)ᵀ = sym2 b c d := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

omit [Field K] in
theorem eq_sym2 {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : C = sym2 (C 0 0) (C 0 1) (C 1 1) := by
  have h10 : C 1 0 = C 0 1 := by
    have := congrFun₂ hC 0 1
    simpa using this
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym2, h10]

theorem tau_mul_tau {C E : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (hE : Eᵀ = E) :
    tau hC * tau hE = tau (C := C + E) (by rw [transpose_add, hC, hE]) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_tau, coe_tau, coe_tau, fromBlocks_multiply]
  simp [add_comm]

theorem lam_mul (a b : K) : lam a * lam b = lam (a + b) := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_lam, coe_lam, coe_lam, fromBlocks_multiply]
  simp only [Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add]
  rw [unitri_mul, ← transpose_mul, unitri_mul, ← neg_add_rev]

theorem lam_zero : lam (0 : K) = 1 := by
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_lam, neg_zero, unitri_zero, transpose_one, fromBlocks_one]
  rfl

theorem inv_lam (a : K) : (lam a)⁻¹ = lam (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [lam_mul, add_neg_cancel, lam_zero])

theorem lam_mul_tau_mul_inv (a : K) {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    lam a * tau hC * (lam a)⁻¹ = tau (C := unitri a * C * (unitri a)ᵀ)
      (by rw [transpose_mul, transpose_mul, transpose_transpose, hC, Matrix.mul_assoc]) := by
  rw [inv_lam]
  apply SymplecticTorusWeyl.statedSp_ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_lam, coe_tau,
    coe_lam, coe_tau, fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.mul_one, Matrix.mul_zero, add_zero, Matrix.zero_mul, zero_add, neg_neg]
  rw [unitri_mul, add_neg_cancel, unitri_zero, ← transpose_mul, unitri_mul, add_neg_cancel,
    unitri_zero, transpose_one]

variable (K) in
@[expose] noncomputable def radical : Subgroup (StatedSp 2 K) where
  carrier := {g | ∃ C : Matrix (Fin 2) (Fin 2) K, ∃ hC : Cᵀ = C, g = tau hC}
  one_mem' := ⟨0, transpose_zero, SymplecticTorusWeyl.statedSp_ext (by
    rw [coe_tau, fromBlocks_one]; rfl)⟩
  mul_mem' := by
    rintro _ _ ⟨C, hC, rfl⟩ ⟨E, hE, rfl⟩
    exact ⟨_, _, tau_mul_tau hC hE⟩
  inv_mem' := by
    rintro _ ⟨C, hC, rfl⟩
    refine ⟨-C, by rw [transpose_neg, hC], inv_eq_of_mul_eq_one_right ?_⟩
    rw [tau_mul_tau]
    apply SymplecticTorusWeyl.statedSp_ext
    rw [coe_tau, add_neg_cancel, fromBlocks_one]
    rfl

theorem tau_mem_unipotent {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) :
    tau hC ∈ unipotent 2 K :=
  ⟨1, C, isUnitriangular_one, hC, by rw [coe_tau, blockMat, inv_one, transpose_one,
    Matrix.one_mul]⟩

theorem lam_mem_unipotent (a : K) : lam a ∈ unipotent 2 K :=
  ⟨unitri a, 0, isUnitriangular_unitri a, transpose_zero, coe_blockElt _ _⟩

theorem eq_unitri_of_isUnitriangular {A : Matrix (Fin 2) (Fin 2) K} (hA : IsUnitriangular A) :
    A = unitri (A 0 1) := by
  have h10 : A 1 0 = 0 := hA.1 (show (0 : Fin 2) < 1 by decide)
  have h00 := hA.2 0
  have h11 := hA.2 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [unitri, h10, h00, h11]

theorem tau_congr {C E : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (hE : Eᵀ = E) (h : C = E) :
    tau hC = tau hE := by
  subst h
  rfl

theorem tau_injective {C E : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (hE : Eᵀ = E)
    (h : tau hC = tau hE) : C = E := by
  have h' := congrArg (fun g : StatedSp 2 K => ((g : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)) h
  simp only [coe_tau] at h'
  exact (fromBlocks_inj.1 h').2.1

theorem tau_comm {C E : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) (hE : Eᵀ = E) :
    tau hC * tau hE = tau hE * tau hC := by
  rw [tau_mul_tau, tau_mul_tau]
  exact tau_congr _ _ (add_comm _ _)

theorem unitri_mul_sym2_mul_transpose [CharP K 2] (a b c d : K) :
    unitri a * sym2 b c d * (unitri a)ᵀ = sym2 (b + a ^ 2 * d) (c + a * d) d := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitri, sym2, mul_apply, Fin.sum_univ_two, transpose_apply] <;>
    first | linear_combination (a * c) * h2 | ring

theorem mem_unipotent_iff {g : StatedSp 2 K} :
    g ∈ unipotent 2 K ↔ ∃ (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) (a : K),
      g = tau hC * lam a := by
  constructor
  · rintro ⟨A, C', hA, hC', hg⟩
    have hAu := eq_unitri_of_isUnitriangular hA
    set a := A 0 1
    refine ⟨A * C' * Aᵀ, by rw [transpose_mul, transpose_mul, transpose_transpose, hC',
      Matrix.mul_assoc], a, SymplecticTorusWeyl.statedSp_ext ?_⟩
    rw [hg, Subgroup.coe_mul, Units.val_mul, coe_tau, coe_lam, fromBlocks_multiply, blockMat,
      fromBlocks_inj]
    refine ⟨by rw [hAu]; simp, ?_, by simp, by rw [hAu, inv_unitri]; simp⟩
    simp only [Matrix.one_mul, zero_add]
    rw [hAu, Matrix.mul_assoc (unitri a * C'), ← transpose_mul, unitri_mul, neg_add_cancel,
      unitri_zero, transpose_one, Matrix.mul_one]
  · rintro ⟨C, hC, a, rfl⟩
    exact mul_mem (tau_mem_unipotent hC) (lam_mem_unipotent a)

theorem radical_le_unipotent : radical K ≤ unipotent 2 K := by
  rintro _ ⟨C, hC, rfl⟩
  exact tau_mem_unipotent hC

theorem conj_tau_mem_radical {g : StatedSp 2 K} (hg : g ∈ unipotent 2 K)
    {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : g * tau hC * g⁻¹ ∈ radical K := by
  obtain ⟨E, hE, a, rfl⟩ := mem_unipotent_iff.1 hg
  have h1 : tau hE * lam a * tau hC * (tau hE * lam a)⁻¹ =
      tau hE * (lam a * tau hC * (lam a)⁻¹) * (tau hE)⁻¹ := by group
  rw [h1, lam_mul_tau_mul_inv, tau_comm, mul_inv_cancel_right]
  exact ⟨_, _, rfl⟩

omit [Field K] in
theorem sym2_apply_zero_one (b c d : K) : sym2 b c d 0 1 = c := rfl

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem tau_sq {C : Matrix (Fin 2) (Fin 2) K} (hC : Cᵀ = C) : tau hC ^ 2 = 1 := by
  rw [sq, tau_mul_tau]
  apply SymplecticTorusWeyl.statedSp_ext
  rw [coe_tau, show C + C = 0 from by
    ext i j
    exact CharTwo.add_self_eq_zero _, fromBlocks_one]
  rfl

omit [Finite K] [CharP K 2] in
theorem card_radical : Nat.card (radical K) = Nat.card K ^ 3 := by
  let φ : K × K × K → radical K := fun x =>
    ⟨tau (sym2_transpose x.1 x.2.1 x.2.2), ⟨_, _, rfl⟩⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y hxy => ?_, ?_⟩
    · have h := tau_injective _ _ (congrArg Subtype.val hxy)
      have h0 := congrFun₂ h 0 0
      have h1 := congrFun₂ h 0 1
      have h2 := congrFun₂ h 1 1
      simp [sym2] at h0 h1 h2
      exact Prod.ext h0 (Prod.ext h1 h2)
    · rintro ⟨_, C, hC, rfl⟩
      exact ⟨(C 0 0, C 0 1, C 1 1), Subtype.ext (tau_congr _ _ (eq_sym2 hC).symm)⟩
  rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Nat.card_prod, Nat.card_prod]
  ring

theorem unique_symplectic_four_Sylow_center (q : ℕ) (hq : Nat.card K = q) :
    (∀ g : StatedSp 2 K, g ∈ unipotent 2 K ↔
      ∃ (C : Matrix (Fin 2) (Fin 2) K) (hC : Cᵀ = C) (a : K), g = tau hC * lam a) ∧
    (∃ S : Sylow 2 (StatedSp 2 K), (S : Subgroup (StatedSp 2 K)) = unipotent 2 K) ∧
    Nat.card (unipotent 2 K) = q ^ 4 ∧
    radical K ≤ unipotent 2 K ∧ ((radical K).subgroupOf (unipotent 2 K)).Normal ∧
    CFSG.IsElementaryAbelian 2 (radical K) ∧ Nat.card (radical K) = q ^ 3 ∧
    (∀ g : unipotent 2 K, g ∈ Subgroup.center (unipotent 2 K) ↔
      ∃ b c : K, (g : StatedSp 2 K) = tau (sym2_transpose b c 0)) ∧
    ∀ a b c d : K, lam a * tau (sym2_transpose b c d) * (lam a)⁻¹ =
      tau (sym2_transpose (b + a ^ 2 * d) (c + a * d) d) := by
  obtain ⟨-, hU, -, -, hSyl, -, -, -⟩ := symplectic_higher_order_and_Sylow (K := K) 2 q hq
    (r := 2) (by norm_num)
  have hformula : ∀ a b c d : K, lam a * tau (sym2_transpose b c d) * (lam a)⁻¹ =
      tau (sym2_transpose (b + a ^ 2 * d) (c + a * d) d) := fun a b c d => by
    rw [lam_mul_tau_mul_inv]
    exact tau_congr _ _ (unitri_mul_sym2_mul_transpose a b c d)
  refine ⟨fun g => mem_unipotent_iff, hSyl, by rw [hU]; norm_num, radical_le_unipotent,
    ⟨fun n hn g => ?_⟩, ?_, by rw [card_radical, hq], fun g => ?_, hformula⟩
  ·
    obtain ⟨C, hC, hnC⟩ := hn
    have hnC' : (n : StatedSp 2 K) = tau hC := hnC
    rw [Subgroup.mem_subgroupOf]
    change (g : StatedSp 2 K) * n * (g : StatedSp 2 K)⁻¹ ∈ radical K
    rw [hnC']
    exact conj_tau_mem_radical g.2 hC
  ·
    have hcomm : ∀ x y : radical K, x * y = y * x := by
      rintro ⟨_, C, hC, rfl⟩ ⟨_, E, hE, rfl⟩
      exact Subtype.ext (tau_comm hC hE)
    exact { is_comm := ⟨hcomm⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
              obtain ⟨_, C, hC, rfl⟩ := x
              exact Subtype.ext (tau_sq hC) }
  ·
    constructor
    · intro hg
      obtain ⟨C, hC, a, hga⟩ := mem_unipotent_iff.1 g.2
      have hcen : ∀ h ∈ unipotent 2 K, h * (g : StatedSp 2 K) = g * h := fun h hh =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hg ⟨h, hh⟩)
      have h1 : lam a * tau (sym2_transpose (0 : K) 0 1) * (lam a)⁻¹ =
          tau (sym2_transpose (0 : K) 0 1) := by
        have h := hcen _ (tau_mem_unipotent (sym2_transpose (0 : K) 0 1))
        rw [hga] at h
        calc lam a * tau (sym2_transpose (0 : K) 0 1) * (lam a)⁻¹
            = (tau hC)⁻¹ * (tau hC * lam a * tau (sym2_transpose (0 : K) 0 1)) *
                (lam a)⁻¹ := by group
          _ = (tau hC)⁻¹ * (tau (sym2_transpose (0 : K) 0 1) * (tau hC * lam a)) *
                (lam a)⁻¹ := by rw [h]
          _ = (tau hC)⁻¹ * (tau (sym2_transpose (0 : K) 0 1) * tau hC) := by group
          _ = tau (sym2_transpose (0 : K) 0 1) := by
                rw [tau_comm (sym2_transpose (0 : K) 0 1) hC, inv_mul_cancel_left]
      rw [hformula] at h1
      have ha := congrFun₂ (tau_injective _ _ h1) 0 1
      simp only [sym2_apply_zero_one, mul_one, zero_add] at ha
      have hg' : (g : StatedSp 2 K) = tau hC := by rw [hga, ha, lam_zero, mul_one]
      have h2 : lam 1 * tau hC * (lam 1)⁻¹ = tau hC := by
        have h := hcen _ (lam_mem_unipotent 1)
        rw [hg'] at h
        rw [h, mul_inv_cancel_right]
      rw [tau_congr hC (sym2_transpose _ _ _) (eq_sym2 hC), hformula] at h2
      have hd := congrFun₂ (tau_injective _ _ h2) 0 1
      simp only [sym2_apply_zero_one, one_mul, add_eq_left] at hd
      refine ⟨C 0 0, C 0 1, ?_⟩
      rw [hg']
      refine tau_congr _ _ ?_
      calc C = sym2 (C 0 0) (C 0 1) (C 1 1) := eq_sym2 hC
        _ = sym2 (C 0 0) (C 0 1) 0 := by rw [hd]
    · rintro ⟨b, c, hbc⟩
      refine Subgroup.mem_center_iff.2 fun h => Subtype.ext ?_
      obtain ⟨E, hE, a, hha⟩ := mem_unipotent_iff.1 h.2
      change (h : StatedSp 2 K) * g = g * h
      rw [hbc, hha]
      have hlam : lam a * tau (sym2_transpose b c 0) = tau (sym2_transpose b c 0) * lam a := by
        have h3 := hformula a b c 0
        simp only [mul_zero, add_zero] at h3
        calc lam a * tau (sym2_transpose b c 0)
            = lam a * tau (sym2_transpose b c 0) * (lam a)⁻¹ * lam a := by group
          _ = tau (sym2_transpose b c 0) * lam a := by rw [h3]
      rw [mul_assoc, hlam, ← mul_assoc, tau_comm hE (sym2_transpose b c 0), mul_assoc]

end CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
