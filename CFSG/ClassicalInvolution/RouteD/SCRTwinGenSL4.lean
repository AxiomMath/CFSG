module

public import CFSG.ClassicalInvolution.RouteD.SCRTwinGenSL4Mat
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinStmt
import CFSG.ClassicalInvolution.RouteD.SCRSp4Base

public section

namespace CFSG.ClassicalInvolution.RouteD.SCRSL4

open CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.WeakCT
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem b0_neg_one_inv : ((b0 (-1) : SL(4, F)))⁻¹ = b0 (-1) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul]
  have : ((-1 : SL(2, F)) * (-1)) = 1 := Subtype.ext (by simp)
  rw [this, map_one]

theorem sq_eq_of_center0 (B₀ : SL(2, F))
    (h : b0 B₀ * b0 B₀ * (b0 (-1))⁻¹ ∈ Subgroup.center SL(4, F)) :
    (B₀ : Matrix (Fin 2) (Fin 2) F) * B₀ = -1 := by
  rw [b0_neg_one_inv, ← map_mul, ← map_mul] at h
  obtain ⟨r, hr, hrY⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  have hY := congrArg (fun z : Matrix (Fin 4) (Fin 4) F => z) hrY
  simp only [coe_blockSL, CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.blockMat_four_zero,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
    Matrix.SpecialLinearGroup.coe_one] at hY
  have e00 := congrFun (congrFun hY 0) 0
  have e01 := congrFun (congrFun hY 0) 1
  have e10 := congrFun (congrFun hY 1) 0
  have e11 := congrFun (congrFun hY 1) 1
  have e22 := congrFun (congrFun hY 2) 2
  simp [Matrix.scalar_apply] at e00 e01 e10 e11 e22
  rw [e22] at e00 e11
  ext i j
  fin_cases i <;> fin_cases j <;> simp
  · linear_combination e00
  · exact e01
  · exact e10
  · linear_combination e11

theorem sq_eq_of_center2 (B₀ : SL(2, F))
    (h : b2 B₀ * b2 B₀ * (b0 (-1))⁻¹ ∈ Subgroup.center SL(4, F)) :
    (B₀ : Matrix (Fin 2) (Fin 2) F) * B₀ = -1 := by
  rw [b0_neg_one_inv, ← map_mul] at h
  obtain ⟨r, hr, hrY⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp h
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_b0_neg_one, coe_blockSL,
    CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.blockMat_four_two] at hrY
  have e00 := congrFun (congrFun hrY 0) 0
  have e22 := congrFun (congrFun hrY 2) 2
  have e23 := congrFun (congrFun hrY 2) 3
  have e32 := congrFun (congrFun hrY 3) 2
  have e33 := congrFun (congrFun hrY 3) 3
  simp [Matrix.scalar_apply, Matrix.mul_apply, Fin.sum_univ_four] at e00 e22 e23 e32 e33
  rw [e00] at e22 e33
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination -e22
  · linear_combination -e23
  · linear_combination -e32
  · linear_combination -e33

theorem mem_center_of_conj {G : Type*} [Group G] {g w : G}
    (h : g * w * g⁻¹ ∈ Subgroup.center G) : w ∈ Subgroup.center G := by
  have := (inferInstance : (Subgroup.center G).Normal).conj_mem _ h g⁻¹
  simpa [mul_assoc] using this

theorem sup_centralizer_conj {G : Type*} [Group G] (g x₁ x₂ x₃ : G)
    (h : Subgroup.centralizer ({x₁} : Set G) ⊔ Subgroup.centralizer ({x₂} : Set G) ⊔
      Subgroup.centralizer ({x₃} : Set G) = ⊤) :
    Subgroup.centralizer ({g * x₁ * g⁻¹} : Set G) ⊔ Subgroup.centralizer ({g * x₂ * g⁻¹} : Set G) ⊔
      Subgroup.centralizer ({g * x₃ * g⁻¹} : Set G) = ⊤ :=
  CFSG.ClassicalInvolution.RouteD.SCRSp4.sup_centralizer_conj g x₁ x₂ x₃ h

theorem sl4_gen (h2 : (2 : F) ≠ 0) {R R' : Subgroup SL(4, F)}
    (hR : R ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num))
    (hR' : R' ∈ longRootSet (K := F) (show 2 ≤ 4 by norm_num)) (hne : R ≠ R') {x x' : SL(4, F)}
    (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x) (hx1 : x ≠ 1) (hx'R' : x' ∈ R')
    (hx'c : ∀ r ∈ R', x' * r = r * x') (hx'1 : x' ≠ 1)
    (hsame : x * x'⁻¹ ∈ Subgroup.center SL(4, F)) {a a' : SL(4, F)} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center SL(4, F))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center SL(4, F)) :
    Subgroup.centralizer ({x} : Set SL(4, F)) ⊔ Subgroup.centralizer ({a * a'} : Set SL(4, F)) ⊔
      Subgroup.centralizer ({x * (a * a')} : Set SL(4, F)) = ⊤ := by
  have hx2 : x * x = 1 :=
    CFSG.ClassicalInvolution.ModelFacts.mul_self_eq_one_of_mem_center_longRootSet hR hxR hxc
  have hx'2 : x' * x' = 1 :=
    CFSG.ClassicalInvolution.ModelFacts.mul_self_eq_one_of_mem_center_longRootSet hR' hx'R' hx'c
  have hc : x' * x⁻¹ ∈ Subgroup.center SL(4, F) := by
    have := (Subgroup.center SL(4, F)).inv_mem hsame
    simpa using this
  obtain ⟨g, hRg, hR'g, hxg⟩ := CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4.twin_std h2 hR
    hR' hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc
  rw [hRg] at ha
  rw [hR'g] at ha'
  obtain ⟨a₀, ⟨A, hA⟩, hae⟩ := ha
  obtain ⟨a₀', ⟨A', hA'⟩, hae'⟩ := ha'
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hae hae'
  have hsq'' : a' * a' * x⁻¹ ∈ Subgroup.center SL(4, F) := by
    have := (Subgroup.center SL(4, F)).mul_mem hsq' hc
    simpa [mul_assoc] using this
  have hx₀ : x = g * b0 (-1) * g⁻¹ := hxg
  have hA₁ : b0 A * b0 A * (b0 (-1))⁻¹ ∈ Subgroup.center SL(4, F) := by
    refine mem_center_of_conj (g := g) ?_
    have e : g * (b0 A * b0 A * (b0 (-1))⁻¹) * g⁻¹ = a * a * x⁻¹ := by
      rw [← hae, ← hA, hx₀]; simp only [b0]; group
    rw [e]; exact hsq
  have hA₂ : b2 A' * b2 A' * (b0 (-1))⁻¹ ∈ Subgroup.center SL(4, F) := by
    refine mem_center_of_conj (g := g) ?_
    have e : g * (b2 A' * b2 A' * (b0 (-1))⁻¹) * g⁻¹ = a' * a' * x⁻¹ := by
      rw [← hae', ← hA', hx₀]; simp only [b0, b2]; group
    rw [e]; exact hsq''
  have key := sup_eq_top h2 A A' (sq_eq_of_center0 A hA₁) (sq_eq_of_center2 A' hA₂)
  have := sup_centralizer_conj g _ _ _ key
  have e2 : a * a' = g * (b0 A * b2 A') * g⁻¹ := by
    rw [← hae, ← hae', ← hA, ← hA']; simp only [b0, b2]; group
  have e3 : x * (a * a') = g * (b0 (-1) * (b0 A * b2 A')) * g⁻¹ := by
    rw [e2, hx₀]; group
  rw [e3, e2, hx₀]
  exact this

end CFSG.ClassicalInvolution.RouteD.SCRSL4

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.LieType.Universal
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem twinMFGenerationOn_psl4 (hp2 : p ≠ 2) {e : ℕ} :
    TwinMFGenerationOn .PSL (modelUniv .PSL 4 p e Fact.out) := by
  intro R R' x x' hd a ha a' ha' hsq hsq' S hS
  have h2 : (2 : GaloisField p e) ≠ 0 := CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField
    e hp2
  have hR := fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hd.mem
  have hR' := fundamentalSubgroups_psl_subset (m := 3) (by norm_num) hd.mem'
  have key := CFSG.ClassicalInvolution.RouteD.SCRSL4.sl4_gen h2 hR hR' hd.ne hd.hx hd.cx hd.nx
    hd.hx' hd.cx' hd.nx' hd.same ha ha' hsq hsq'
  exact le_top.trans key.symm.le

theorem twinMFGeneration_psl4 (hp2 : p ≠ 2) (e : ℕ) : TwinMFGeneration p e .PSL 4 :=
  twinMFGeneration_of_on (twinMFGenerationOn_psl4 hp2)

end CFSG.ClassicalInvolution.RouteD.TwinY
