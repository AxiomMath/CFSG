module

public import CFSG.GH74.GLS.Stage2.Final.ModelLUElts
public import CFSG.GH74.GLS.Stage2.Final.ModelRefl

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelBlock

open CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5 Matrix Subgroup

variable {F : Type} [Field F]

@[expose] def dg (α : Fˣ) : GL (Fin 2) F where
  val := Matrix.diagonal ![(α : F), ((α⁻¹ : Fˣ) : F)]
  inv := Matrix.diagonal ![((α⁻¹ : Fˣ) : F), (α : F)]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

theorem coe_dg (α : Fˣ) :
    ((dg α : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      Matrix.diagonal ![(α : F), ((α⁻¹ : Fˣ) : F)] := rfl

theorem dg_mul (α β : Fˣ) : (dg α : GL (Fin 2) F) * dg β = dg (α * β) := by
  apply Units.ext
  simp only [Units.val_mul, coe_dg]
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i
  · simp
  · simp [mul_comm]

theorem dg_one : (dg (1 : Fˣ) : GL (Fin 2) F) = 1 := by
  apply Units.ext
  simp only [coe_dg, Units.val_one]
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

@[expose] def dgHom : Fˣ →* GL (Fin 2) F where
  toFun := dg
  map_one' := dg_one
  map_mul' α β := (dg_mul α β).symm

theorem dgHom_apply (α : Fˣ) : (dgHom α : GL (Fin 2) F) = dg α := rfl

theorem det_dg (α : Fˣ) : ((dg α : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [coe_dg, Matrix.det_diagonal]
  simp [Fin.prod_univ_two]

theorem dg_injective : Function.Injective (dgHom : Fˣ →* GL (Fin 2) F) := by
  intro α β h
  have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simpa [dgHom_apply, coe_dg] using Units.ext this

theorem dg_comm_dRefl (α : Fˣ) : (dg α : GL (Fin 2) F) * dRefl F = dRefl F * dg α := by
  apply Units.ext
  simp only [Units.val_mul, coe_dg, coe_dRefl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem eq_dg_of_comm (h2 : (2 : F) ≠ 0) {a : GL (Fin 2) F}
    (hdet : (a : Matrix (Fin 2) (Fin 2) F).det = 1) (hc : a * dRefl F = dRefl F * a) :
    ∃ α : Fˣ, a = dg α := by
  have hc' := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hc
  simp only [Units.val_mul, coe_dRefl] at hc'
  have e01 := congrFun₂ hc' 0 1
  have e10 := congrFun₂ hc' 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e01 e10
  have h01 : (a : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have : (2 : F) * (a : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by linear_combination -e01
    exact (mul_eq_zero.1 this).resolve_left h2
  have h10 : (a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have : (2 : F) * (a : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by linear_combination e10
    exact (mul_eq_zero.1 this).resolve_left h2
  rw [Matrix.det_fin_two, h01, h10] at hdet
  have hp : (a : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
    intro h0
    rw [h0] at hdet
    simp at hdet
  refine ⟨Units.mk0 _ hp, ?_⟩
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dg, h01, h10]
  have h1 : (a : Matrix (Fin 2) (Fin 2) F) 0 0 * (a : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    linear_combination hdet
  field_simp
  linear_combination h1

@[expose] def torusT (M : ModelData F) : Subgroup Fˣ := M.H2.comap (dgHom : Fˣ →* GL (Fin 2) F)

theorem mem_torusT {M : ModelData F} {α : Fˣ} : α ∈ torusT M ↔ dg α ∈ M.H2 := Iff.rfl

@[expose] def torusHom (M : ModelData F) : ↥(torusT M) →* ↥M.H2 :=
  ((dgHom : Fˣ →* GL (Fin 2) F).comp (torusT M).subtype).codRestrict M.H2 (fun α => α.2)

theorem torusHom_apply (M : ModelData F) (α : ↥(torusT M)) :
    ((torusHom M α : ↥M.H2) : GL (Fin 2) F) = dg (α : Fˣ) := rfl

theorem torusHom_injective (M : ModelData F) : Function.Injective (torusHom M) := by
  intro α β h
  apply Subtype.ext
  apply dg_injective
  exact congrArg Subtype.val h

@[expose] noncomputable def torusTheta (M : ModelData F) : ↥(torusT M) →* PG M :=
  (iota1 M).comp (torusHom M)

theorem torusTheta_injective (M : ModelData F) : Function.Injective (torusTheta M) :=
  (iota1_injective M).comp (torusHom_injective M)

theorem iota1_comm_dP_iff (M : ModelData F) (hd : dRefl F ∈ M.U2) (a : ↥M.H2) :
    iota1 M a * dP M (dRefl F) hd = dP M (dRefl F) hd * iota1 M a ↔
      (a : GL (Fin 2) F) * dRefl F = dRefl F * (a : GL (Fin 2) F) := by
  have hx : iota1 M a = mkP M ⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ := iota1_apply M a
  have hy : dP M (dRefl F) hd = mkP M ⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ := rfl
  rw [hx, hy, mkP_comm_iff]
  have key : ∀ κ : Fˣ,
      ((⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ : ↥M.K4) : GL (Fin 4) F)⁻¹ *
        ((⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ : ↥M.K4) : GL (Fin 4) F)⁻¹ *
        (((⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ : ↥M.K4) : GL (Fin 4) F) *
          ((⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ : ↥M.K4) : GL (Fin 4) F)) =
        Matrix.GeneralLinearGroup.scalar (Fin 4) κ ↔
      (dRefl F)⁻¹ * (a : GL (Fin 2) F)⁻¹ * (dRefl F * (a : GL (Fin 2) F)) = sc2 κ ∧ (1 : GL (Fin 2) F) = sc2 κ := by
    intro κ
    have e : ((⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ : ↥M.K4) : GL (Fin 4) F)⁻¹ *
        ((⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ : ↥M.K4) : GL (Fin 4) F)⁻¹ *
        (((⟨diagGL (dRefl F) (dRefl F)⁻¹, diag_inv_mem_K4 M hd⟩ : ↥M.K4) : GL (Fin 4) F) *
          ((⟨diagGL (a : GL (Fin 2) F) 1, M.blkL_mem_K4 a.2⟩ : ↥M.K4) : GL (Fin 4) F)) =
        diagGL ((dRefl F)⁻¹ * (a : GL (Fin 2) F)⁻¹ * (dRefl F * (a : GL (Fin 2) F))) 1 := by
      show (diagGL (dRefl F) (dRefl F)⁻¹)⁻¹ * (diagGL (a : GL (Fin 2) F) 1)⁻¹ *
        (diagGL (dRefl F) (dRefl F)⁻¹ * diagGL (a : GL (Fin 2) F) 1) = _
      rw [diagGL_inv, diagGL_inv, diagGL_mul, diagGL_mul, diagGL_mul]
      congr 1
      simp
    rw [e, scalar4_eq]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := diagGL_inj h
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [h1, ← h2]
  constructor
  · rintro ⟨κ, hκ⟩
    obtain ⟨h1, h2⟩ := (key κ).1 hκ
    have hX : (dRefl F)⁻¹ * (a : GL (Fin 2) F)⁻¹ * (dRefl F * (a : GL (Fin 2) F)) = 1 := by rw [h1, ← h2]
    exact (commute_of_inv_mul_eq_one hX).symm
  · intro h
    refine ⟨1, (key 1).2 ⟨?_, by rw [sc2_one]⟩⟩
    rw [sc2_one, ← h]
    group

theorem range_torusTheta (M : ModelData F) (h2 : (2 : F) ≠ 0) (hd : dRefl F ∈ M.U2) :
    (torusTheta M).range =
      K1 M ⊓ Subgroup.centralizer ({dP M (dRefl F) hd} : Set (PG M)) := by
  ext x
  constructor
  · rintro ⟨α, rfl⟩
    refine ⟨⟨_, rfl⟩, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      ((iota1_comm_dP_iff M hd (torusHom M α)).2 (by rw [torusHom_apply]; exact dg_comm_dRefl _))
  · rintro ⟨⟨a, rfl⟩, hc⟩
    have hcomm := (iota1_comm_dP_iff M hd a).1 (Subgroup.mem_centralizer_singleton_iff.1 hc)
    obtain ⟨α, hα⟩ := eq_dg_of_comm h2 ((M.mem_H2 _).1 a.2).2 hcomm
    have hαT : α ∈ torusT M := by rw [mem_torusT, ← hα]; exact a.2
    refine ⟨⟨α, hαT⟩, ?_⟩
    show iota1 M (torusHom M ⟨α, hαT⟩) = iota1 M a
    congr 1
    exact Subtype.ext (by rw [torusHom_apply]; exact hα.symm)

theorem isCyclic_inf_centralizer [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0)
    (hd : dRefl F ∈ M.U2) :
    IsCyclic ↥(K1 M ⊓ Subgroup.centralizer ({dP M (dRefl F) hd} : Set (PG M))) := by
  rw [← range_torusTheta M h2 hd]
  let e := MonoidHom.ofInjective (torusTheta_injective M)
  have : IsCyclic ↥(torusT M) := inferInstance
  exact isCyclic_of_surjective e.toMonoidHom e.surjective

theorem card_inf_centralizer (M : ModelData F) (h2 : (2 : F) ≠ 0) (hd : dRefl F ∈ M.U2) :
    Nat.card ↥(K1 M ⊓ Subgroup.centralizer ({dP M (dRefl F) hd} : Set (PG M))) =
      Nat.card ↥(torusT M) := by
  rw [← range_torusTheta M h2 hd]
  exact (Nat.card_congr (MonoidHom.ofInjective (torusTheta_injective M)).toEquiv).symm

end CFSG.GH74.GLS.Stage2.Final.ModelBlock
