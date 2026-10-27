module

public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceLinearBlocks
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSpBasic
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RootSp2

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Sp

open CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply)
open CFSG.ClassicalInvolution.Balance
open scoped Matrix MatrixGroups

variable {F : Type} [Field F]

section Components

theorem isQuasisimple_longRootSp2 [Finite F] (h4 : 4 ≤ Nat.card F) (a : Fin 2) :
    CFSG.Open.IsQuasisimple (longRootSp2 F 2 a) :=
  Components.quasisimple_of_equiv (MonoidHom.ofInjective (longBlock_injective a)).symm
    (CFSG.ClassicalInvolution.Balance.StrongBalance.Linear.isQuasisimple_SL_of_two_le le_rfl h4)

theorem fixedGroup_conj_eq {G : Type*} [Group G] (x : G) :
    fixedGroup (MulAut.conj x) = Subgroup.centralizer ({x} : Set G) := by
  ext y
  rw [mem_fixedGroup, Subgroup.mem_centralizer_singleton_iff, MulAut.conj_apply,
    mul_inv_eq_iff_eq_mul, eq_comm]

theorem longInv_one_eq : longInv F 2 1 = negOne * longInv F 2 0 := by
  refine mat_injective ?_
  rw [map_mul, mat_negOne, mat_longInv, mat_longInv, Matrix.neg_mul, Matrix.one_mul]
  ext r t
  by_cases hrt : r = t
  · subst hrt
    rcases r with a | a <;> fin_cases a <;> simp [coords]
  · simp [hrt]

theorem centralizer_longInv_one :
    Subgroup.centralizer ({longInv F 2 1} : Set (StatedSp 2 F)) =
      Subgroup.centralizer ({longInv F 2 0} : Set (StatedSp 2 F)) := by
  have hn : negOne ∈ Subgroup.center (StatedSp 2 F) := (mem_center_iff).mpr (Or.inr rfl)
  ext c
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    longInv_one_eq]
  have hc := Subgroup.mem_center_iff.mp hn c
  constructor
  · intro h
    have : negOne * (c * longInv F 2 0) = negOne * (longInv F 2 0 * c) := by
      calc negOne * (c * longInv F 2 0) = c * (negOne * longInv F 2 0) := by
            rw [← mul_assoc, ← hc, mul_assoc]
        _ = (negOne * longInv F 2 0) * c := h
        _ = negOne * (longInv F 2 0 * c) := by rw [mul_assoc]
    exact mul_left_cancel this
  · intro h
    calc c * (negOne * longInv F 2 0) = negOne * (c * longInv F 2 0) := by
          rw [← mul_assoc, hc, mul_assoc]
      _ = negOne * (longInv F 2 0 * c) := by rw [h]
      _ = (negOne * longInv F 2 0) * c := by rw [mul_assoc]

theorem isComponentOf_longRootSp2 [Finite F] (h2 : (2 : F) ≠ 0) (h4 : 4 ≤ Nat.card F)
    (a : Fin 2) :
    CFSG.Open.IsComponentOf (longRootSp2 F 2 a)
      (fixedGroup (MulAut.conj (longInv F 2 0))) := by
  rw [fixedGroup_conj_eq]
  have hnormal := IsLongRootSp2.normal_subgroupOf_centralizer h2 (isLongRootSp2_standard a)
  have hle := (isClassicalSL2_longRootSp2 h2 a).le_centralizer
  obtain rfl | rfl : a = 0 ∨ a = 1 := by fin_cases a <;> simp
  · exact ⟨hle, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle hnormal,
      isQuasisimple_longRootSp2 h4 0⟩
  · rw [centralizer_longInv_one] at hnormal hle
    exact ⟨hle, CFSG.ClassicalInvolution.isSubnormal_of_normal_subgroupOf hle hnormal,
      isQuasisimple_longRootSp2 h4 1⟩

end Components

section Matrices

open CFSG.LieType.Steinberg (sl2Upper sl2Lower)

theorem mat_longBlock_upper (a : Fin 2) (c : F) :
    mat 2 F (longBlock F 2 a (sl2Upper c)) = Matrix.transvection (Sum.inl a) (Sum.inr a) c := by
  rw [longBlock_sl2Upper, CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt_positiveLong]

theorem mat_longBlock_lower (a : Fin 2) (c : F) :
    mat 2 F (longBlock F 2 a (sl2Lower c)) = Matrix.transvection (Sum.inr a) (Sum.inl a) c := by
  rw [longBlock_sl2Lower, CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt_negativeLong]

@[expose] def simMat (A : gsp 2 F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

@[expose] def simInv (A : gsp 2 F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)

theorem simInv_mul (A : gsp 2 F) : simInv A * simMat A = 1 := Units.inv_mul _

theorem simMat_mul (A : gsp 2 F) : simMat A * simInv A = 1 := Units.mul_inv _

theorem mat_conjSp_fieldSp (A : gsp 2 F) (σ : F ≃+* F) (s : StatedSp 2 F) :
    mat 2 F (conjSp 2 F A (fieldSp 2 F σ s)) = simMat A * (mat 2 F s).map σ * simInv A := by
  rw [mat_apply, coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]
  rfl

theorem mat_conjSp (A : gsp 2 F) (s : StatedSp 2 F) :
    mat 2 F (conjSp 2 F A s) = simMat A * mat 2 F s * simInv A := by
  rw [mat_apply, coe_conjSp, Units.val_mul, Units.val_mul]
  rfl

theorem mul_eq_of_conjSp_eq (A : gsp 2 F) (σ : F ≃+* F) {s : StatedSp 2 F}
    (h : conjSp 2 F A (fieldSp 2 F σ s) = s) :
    simMat A * (mat 2 F s).map σ = mat 2 F s * simMat A := by
  have h1 := congrArg (mat 2 F) h
  rw [mat_conjSp_fieldSp] at h1
  calc simMat A * (mat 2 F s).map σ
      = simMat A * (mat 2 F s).map σ * (simInv A * simMat A) := by rw [simInv_mul, mul_one]
    _ = (simMat A * (mat 2 F s).map σ * simInv A) * simMat A := by simp only [mul_assoc]
    _ = mat 2 F s * simMat A := by rw [h1]

theorem conjSp_eq_of_mul_eq (A : gsp 2 F) {y z : StatedSp 2 F}
    (h : simMat A * mat 2 F y = mat 2 F z * simMat A) : conjSp 2 F A y = z := by
  refine mat_injective ?_
  rw [mat_conjSp, h, mul_assoc, simMat_mul, mul_one]

theorem formJ_eq_gram : formJ 2 F = gram F 2 := rfl

theorem fieldSp_eq_self {σ : F ≃+* F} (hσ : ∀ c, σ c = c) (y : StatedSp 2 F) :
    fieldSp 2 F σ y = y := by
  refine mat_injective ?_
  rw [mat_apply, coe_fieldSp, ← mat_apply]
  ext r t
  simp [hσ]

end Matrices

section Main

variable {X : Type} [Group X]

theorem false_of_conj_eq {L : Subgroup X} {f d : X} (hfd : f * d = d * f) (hff : f * f = 1)
    (hodd : Odd (orderOf d)) (h : ∀ w ∈ L, d * w * d⁻¹ = f * w * f⁻¹)
    (hfaith : ¬ ∀ w ∈ L, f * w = w * f) : False := by
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hff
  have hc : ∀ w ∈ L, (f * d) * w = w * (f * d) := by
    intro w hw
    have h1 := h w hw
    rw [hfi, mul_inv_eq_iff_eq_mul] at h1
    calc f * d * w = f * (d * w) := by rw [mul_assoc]
      _ = f * (f * w * f * d) := by rw [h1]
      _ = (f * f) * w * f * d := by simp only [mul_assoc]
      _ = w * (f * d) := by rw [hff, one_mul, mul_assoc]
  apply hfaith
  intro w hw
  have hpow : (f * d) ^ orderOf d = f := by
    rw [(Commute.mul_pow (show Commute f d from hfd) _), pow_orderOf_eq_one, mul_one]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, pow_two, hff, one_pow, one_mul]
  have hcomm : ∀ n : ℕ, (f * d) ^ n * w = w * (f * d) ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, mul_assoc, hc w hw, ← mul_assoc, ih, mul_assoc]
  have := hcomm (orderOf d)
  rwa [hpow] at this

end Main

end CFSG.ClassicalInvolution.Balance.StrongBalance.Sp
