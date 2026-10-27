module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Lift
public import CFSG.ClassicalInvolution.Q3.TA3SOLSp4Cent
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5Sp4Fix
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp
public import CFSG.RankThree.PartOne.AUTSL.SpTwoAut

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5Sp4

open CFSG CFSG.ClassicalInvolution CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatFactsSp4
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem trace_map_ringEquiv {n : Type*} [Fintype n] (σ : K ≃+* K) (M : Matrix n n K) :
    (M.map σ).trace = σ M.trace := by
  simp [Matrix.trace, map_sum]

theorem trace_kron_one (g : Matrix (Fin 2) (Fin 2) K) : (kron g 1).trace = 2 * g.trace := by
  simp [kron, Matrix.trace, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring

theorem smul_kron (c : K) (g h : Matrix (Fin 2) (Fin 2) K) : c • kron g h = kron g (c • h) := by
  simp only [kron, fromBlocks_smul, smul_smul, mul_comm c]

theorem transpose_mul_eq_smul {h : Matrix (Fin 2) (Fin 2) K} {μ : K}
    (hA : (kron 1 h)ᵀ * formJ 2 K * kron 1 h = μ • formJ 2 K) : hᵀ * h = μ • 1 := by
  rw [formJ_eq_kron, kron_transpose, kron_mul, kron_mul, transpose_one, Matrix.one_mul,
    Matrix.mul_one, smul_kron, Matrix.mul_one] at hA
  exact kron_left_injective _ _ hA

theorem rot_or_refl {h : Matrix (Fin 2) (Fin 2) K} {μ : K} (hμ : μ ≠ 0)
    (hh : hᵀ * h = μ • 1) :
    (h 1 1 = h 0 0 ∧ h 1 0 = -h 0 1) ∨ (h 1 1 = -h 0 0 ∧ h 1 0 = h 0 1) := by
  have e00 := congrFun (congrFun hh 0) 0
  have e01 := congrFun (congrFun hh 0) 1
  have e11 := congrFun (congrFun hh 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  by_cases ha : h 0 0 = 0
  · rw [ha] at e00 e01
    have hc : h 1 0 ≠ 0 := fun hc => hμ (by rw [← e00, hc]; ring)
    have hd : h 1 1 = 0 := (mul_eq_zero.mp (by linear_combination e01 :
      h 1 0 * h 1 1 = 0)).resolve_left hc
    have hb2 : (h 0 1 - h 1 0) * (h 0 1 + h 1 0) = 0 := by
      rw [hd] at e11
      linear_combination e11 - e00
    rcases mul_eq_zero.mp hb2 with hb | hb
    · right
      exact ⟨by rw [hd, ha, neg_zero], by linear_combination -hb⟩
    · left
      exact ⟨by rw [hd, ha], by linear_combination hb⟩
  · have hd2 : (h 1 1 - h 0 0) * (h 1 1 + h 0 0) = 0 := by
      have : (h 1 1 ^ 2 - h 0 0 ^ 2) * μ = 0 := by
        linear_combination -(h 1 1) ^ 2 * e00 + (h 0 0) ^ 2 * e11 +
          (h 1 0 * h 1 1 - h 0 0 * h 0 1) * e01
      have h2 := (mul_eq_zero.mp this).resolve_right hμ
      linear_combination h2
    rcases mul_eq_zero.mp hd2 with hd | hd
    · left
      refine ⟨by linear_combination hd, ?_⟩
      have : h 0 0 * (h 0 1 + h 1 0) = 0 := by linear_combination e01 - h 1 0 * hd
      have := (mul_eq_zero.mp this).resolve_left ha
      linear_combination this
    · right
      refine ⟨by linear_combination hd, ?_⟩
      have : h 0 0 * (h 0 1 - h 1 0) = 0 := by linear_combination e01 - h 1 0 * hd
      have := (mul_eq_zero.mp this).resolve_left ha
      linear_combination -this

variable (K) in
@[expose] def rotAut : Set (MulAut (StatedProj (StatedSp 2 K))) :=
  {β | ∃ (A : gsp 2 K) (h : Matrix (Fin 2) (Fin 2) K),
    ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = kron 1 h ∧
      (h 1 1 = h 0 0 ∧ h 1 0 = -h 0 1) ∧ β = SymplecticHigher.conjAut 2 K A}

theorem rotAut_comm : ∀ α ∈ rotAut K, ∀ β ∈ rotAut K, α * β = β * α := by
  rintro _ ⟨A, h, hA, hr, rfl⟩ _ ⟨A', h', hA', hr', rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, hA, hA', kron_mul, Matrix.one_mul,
    TA3.Sp4.rot_comm hr hr']

theorem conjAut_eq_one_of_scalar (A : gsp 2 K) {c : K}
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = c • 1) :
    SymplecticHigher.conjAut 2 K A = 1 := by
  refine MulEquiv.ext fun y => ?_
  obtain ⟨x, rfl⟩ := proj_surjective y
  have h := proj_lift A (RingEquiv.refl K) x
  rw [show fieldAut 2 K (RingEquiv.refl K) = 1 from map_one _,
    show fieldSp 2 K (RingEquiv.refl K) = 1 from map_one _, mul_one, mul_one] at h
  rw [h, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  rw [coe_conjSp]
  have hc : (A : GL (Fin 2 ⊕ Fin 2) K) * (x : GL (Fin 2 ⊕ Fin 2) K) =
      (x : GL (Fin 2 ⊕ Fin 2) K) * (A : GL (Fin 2 ⊕ Fin 2) K) := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hA, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one])
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

variable [Finite K]

theorem dichotomy_of_fix_Lsub (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K)
    (β : MulAut (StatedProj (StatedSp 2 K))) (hβ : ∀ x ∈ Lsub K, β x = x) :
    β ∈ rotAut K ∨ β * β = 1 := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_odd_card hodd
  obtain ⟨-, hform⟩ := RankThree.PartOne.AUTSL.SpTwo.automorphism_generation_two (K := K) h2
  obtain ⟨A, σ, rfl⟩ := hform β
  have : Group.IsPerfect SL(2, K) := sl2_isPerfect h4
  have := Group.IsPerfect.range (diagSL K)
  have hfix := lift_fix_of_perfect (conjSp 2 K A * fieldSp 2 K σ) _ (proj_lift A σ)
    (diagSL K).range fun m hm =>
    hβ _ (by obtain ⟨g, rfl⟩ := hm; exact ⟨diagSL K g, ⟨g, rfl⟩, rfl⟩)
  set B := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hB
  set Bi := (((A : GL (Fin 2 ⊕ Fin 2) K)⁻¹ : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hBi
  have hBiB : Bi * B = 1 := by rw [hB, hBi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hM : ∀ g : SL(2, K), B * (kron (g : Matrix (Fin 2) (Fin 2) K) 1).map σ * Bi =
      kron (g : Matrix (Fin 2) (Fin 2) K) 1 := fun g => by
    have := congrArg (fun y : ↥(StatedSp 2 K) =>
      ((y : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))
      (hfix _ ⟨g, rfl⟩)
    simpa only [GH74.Generic.coe_tau, coe_diagSL] using this
  have hσ : ∀ x : K, σ x = x := by
    intro x
    have ht := congrArg Matrix.trace (hM (GH74.Generic.companionSL x))
    rw [Matrix.trace_mul_cycle, hBiB, Matrix.one_mul, trace_map_ringEquiv, trace_kron_one] at ht
    have htr : ((GH74.Generic.companionSL x : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).trace = x := by
      simp [GH74.Generic.companionSL, trace_fin_two]
    rw [htr, map_mul, map_ofNat] at ht
    exact mul_left_cancel₀ h2 ht
  obtain rfl : σ = RingEquiv.refl K := RingEquiv.ext hσ
  have hmap : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K, M.map (RingEquiv.refl K) = M :=
    fun M => by ext; simp
  have hcomm : ∀ g : SL(2, K), B * kron (g : Matrix (Fin 2) (Fin 2) K) 1 =
      kron (g : Matrix (Fin 2) (Fin 2) K) 1 * B := fun g => by
    have := hM g
    rw [hmap] at this
    calc B * kron (g : Matrix (Fin 2) (Fin 2) K) 1 =
        B * kron (g : Matrix (Fin 2) (Fin 2) K) 1 * Bi * B := by
          rw [Matrix.mul_assoc _ Bi, hBiB, Matrix.mul_one]
      _ = kron (g : Matrix (Fin 2) (Fin 2) K) 1 * B := by rw [this]
  have hk := TA3.Sp4.eq_kron_one_of_commute one_ne_zero one_ne_zero (hcomm TA3.Sp4.upperSL)
    (hcomm TA3.Sp4.lowerSL)
  obtain ⟨μ, hμ⟩ := mem_gsp.mp A.2
  rw [← hB, hk] at hμ
  have hh := transpose_mul_eq_smul hμ
  rw [show fieldAut 2 K (RingEquiv.refl K) = 1 from map_one _, mul_one]
  rcases rot_or_refl μ.ne_zero hh with hr | hr
  · exact Or.inl ⟨A, _, hk, hr, rfl⟩
  · right
    set h := B.toBlocks₁₁ with hhdef
    have hsq : h * h = (h 0 0 ^ 2 + h 0 1 ^ 2) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hr.1, hr.2] <;>
        ring
    rw [← map_mul]
    refine conjAut_eq_one_of_scalar (A * A) (c := h 0 0 ^ 2 + h 0 1 ^ 2) ?_
    rw [Subgroup.coe_mul, Units.val_mul, ← hB, hk, kron_mul, Matrix.one_mul, hsq, ← smul_kron,
      kron_one_one]

theorem noQ8Fix_Lsub (hodd : Odd (Nat.card K)) (h4 : 4 ≤ Nat.card K) :
    NoQ8Fix (StatedProj (StatedSp 2 K)) (Lsub K) :=
  noQ8Fix_of_dichotomy (rotAut K) rotAut_comm (dichotomy_of_fix_Lsub hodd h4)

end CFSG.ClassicalInvolution.Q3.TA3.Q5Sp4
