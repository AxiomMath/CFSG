module

public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecA.C10KG Matrix

variable {K : Type} [Field K]

theorem scalars_subgroupOf_le_center_statedSU {q : ℕ} :
    (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) ≤
      Subgroup.center ↥(StatedSU 3 q K) := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro k
  apply Subtype.ext
  obtain ⟨c, hc⟩ := hz
  have hcz : Matrix.GeneralLinearGroup.scalar (Fin 3) c = (z : GL (Fin 3) K) := hc
  have hcen : (z : GL (Fin 3) K) ∈ Subgroup.center (GL (Fin 3) K) := by
    rw [← hcz, Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  exact Subgroup.mem_center_iff.mp hcen (k : GL (Fin 3) K)

theorem statedSU_three_center_le_scalars [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Subgroup.center ↥(StatedSU 3 q K) ≤
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) := by
  intro z hz
  have hq2 := two_le_of_card_eq_sq hK
  have hq : q ≠ 0 := by omega
  obtain ⟨a, ha⟩ := exists_orderOf_eq hK
  have haq : a ^ (q + 1) = 1 := ha ▸ pow_orderOf_eq_one a
  have ha1 : (a : K) ≠ 1 := fun h => by
    have : a = 1 := Units.ext h
    rw [this, orderOf_one] at ha
    omega
  have ha2 : (a : K) ≠ ((a⁻¹ : Kˣ) : K) := fun h => by
    have h' : a ^ 2 = 1 := by
      rw [sq]
      nth_rw 2 [Units.ext h]
      exact mul_inv_cancel a
    have := orderOf_dvd_of_pow_eq_one h'
    rw [ha] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hb1 : ((a⁻¹ : Kˣ) : K) ≠ 1 := fun h => ha1 (by
    have : a⁻¹ = 1 := Units.ext h
    rw [inv_eq_one.mp this, Units.val_one])
  have hinj : Function.Injective ![(a : K), ((a⁻¹ : Kˣ) : K), 1] := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hcomm : ∀ g : ↥(StatedSU 3 q K),
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (((z : ↥(StatedSU 3 q K)) :
          GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (((z : ↥(StatedSU 3 q K)) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := fun g => by
    have := Subgroup.mem_center_iff.mp hz g
    exact congrArg (fun x : ↥(StatedSU 3 q K) => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      this
  set M : Matrix (Fin 3) (Fin 3) K := (((z : ↥(StatedSU 3 q K)) : GL (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) K) with hMdef
  have hD := hcomm ⟨diagGL a, diagGL_mem hq haq⟩
  have hdiag := eq_diagonal_of_commute hinj hD.symm
  have hP := hcomm ⟨cyc3GL, cyc3GL_mem hq⟩
  change cyc3 * M = M * cyc3 at hP
  rw [hdiag] at hP
  obtain ⟨h1, h2⟩ := eq_of_diagonal_commute_cyc3 hP.symm
  have hMs : M = Matrix.scalar (Fin 3) (M 0 0) := by
    rw [hdiag, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · exact h1
    · exact h2
  have hdet := det_eq_one_of_mem_statedSU (z : ↥(StatedSU 3 q K)).2
  change M.det = 1 at hdet
  rw [hMs, Matrix.scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin] at hdet
  have hne : M 0 0 ≠ 0 := fun h0 => by rw [h0] at hdet; simp at hdet
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range]
  refine ⟨Units.mk0 (M 0 0) hne, ?_⟩
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  exact hMs.symm

theorem center_statedSU_three_eq_scalars [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    Subgroup.center ↥(StatedSU 3 q K) =
      (StatedScalars (Fin 3) K).subgroupOf (StatedSU 3 q K) :=
  le_antisymm (statedSU_three_center_le_scalars hK) scalars_subgroupOf_le_center_statedSU

end CFSG.HardMathSupport.Solomon.Proving
