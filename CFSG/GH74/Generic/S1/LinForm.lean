module

public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedGraphTools
public import CFSG.LieType.Steinberg.CentralExt.PerfectLift
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S1

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification Matrix

variable {F : Type} [Field F]

@[expose] noncomputable def slAut (α : MulAut ↥(StatedSL 4 F)) :
    MulAut (SpecialLinearGroup (Fin 4) F) :=
  MulAut.congr (specialLinearGroupEquivStatedSL 4 F).symm α

theorem coe_equiv_statedSL (g : SpecialLinearGroup (Fin 4) F) :
    ((specialLinearGroupEquivStatedSL 4 F g : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
      SpecialLinearGroup.toGL g :=
  Units.ext (specialLinearGroupEquivStatedSL_coe 4 F g)

theorem toGL_slAut (α : MulAut ↥(StatedSL 4 F)) (g : SpecialLinearGroup (Fin 4) F) :
    SpecialLinearGroup.toGL (slAut α g) =
      ((α (specialLinearGroupEquivStatedSL 4 F g) : ↥(StatedSL 4 F)) : GL (Fin 4) F) := by
  rw [← coe_equiv_statedSL]
  congr 1
  exact (specialLinearGroupEquivStatedSL 4 F).apply_symm_apply _

theorem toGL_slAut_symm (α : MulAut ↥(StatedSL 4 F)) (k : ↥(StatedSL 4 F)) :
    SpecialLinearGroup.toGL (slAut α ((specialLinearGroupEquivStatedSL 4 F).symm k)) =
      ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) := by
  rw [toGL_slAut, MulEquiv.apply_symm_apply]

theorem slAut_mul (α β : MulAut ↥(StatedSL 4 F)) : slAut (α * β) = slAut α * slAut β :=
  map_mul _ α β

theorem slAut_one : slAut (1 : MulAut ↥(StatedSL 4 F)) = 1 := map_one _

theorem eq_of_descendAut_eq {n : ℕ} (hn : 3 ≤ n) {α₁ α₂ : MulAut (SpecialLinearGroup (Fin n) F)}
    (h : descendAut n F α₁ = descendAut n F α₂) : α₁ = α₂ := by
  have : Group.IsPerfect (SpecialLinearGroup (Fin n) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect hn
  have key := CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect
    (π := LinearFlag.proj n F) (H := SpecialLinearGroup (Fin n) F)
    (by rw [ker_proj]; exact scalars_le_center n F)
    (β₁ := (α₁ : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F))
    (β₂ := (α₂ : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F)) (by
      refine MonoidHom.ext fun g => ?_
      change LinearFlag.proj n F (α₁ g) = LinearFlag.proj n F (α₂ g)
      rw [← descendAut_proj, ← descendAut_proj, h])
  exact MulEquiv.ext fun g => DFunLike.congr_fun key g

theorem sq_mod_four_ne_three (m : ℕ) : m * m % 4 ≠ 3 := by
  have h := Nat.mod_lt m (by norm_num : 4 > 0)
  rw [Nat.mul_mod]
  interval_cases (m % 4) <;> simp

theorem eq_one_of_mul_self_eq_one [Finite F] (hF : Nat.card F % 4 = 3) (τ : F ≃+* F)
    (h : τ * τ = 1) : τ = 1 := by
  by_contra hne
  obtain ⟨p, hp⟩ := CharP.exists F
  have hpp : p.Prime := CharP.char_is_prime F p
  have := Fintype.ofFinite F
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F p
  have hcard' : Nat.card F = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hcard]
  obtain ⟨hev, -⟩ := LinearFlag.even_and_eq_pow_of_involution_prime hpp n.pos hcard' hne h
  obtain ⟨m, hm⟩ := hev
  have : Nat.card F = p ^ m * p ^ m := by rw [hcard', hm, pow_add]
  exact sq_mod_four_ne_three _ (this ▸ hF)


theorem lin_involution_form [Finite F] (hF : Nat.card F % 4 = 3) (α : MulAut ↥(StatedSL 4 F))
    (hα : α * α = 1) :
    (∃ A : GL (Fin 4) F, (∃ c : Fˣ, A * A = GeneralLinearGroup.scalar (Fin 4) c) ∧
        ∀ k : ↥(StatedSL 4 F),
          ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) = A * (k : GL (Fin 4) F) * A⁻¹) ∨
    (∃ A : GL (Fin 4) F,
        (((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = (A : Matrix (Fin 4) (Fin 4) F) ∨
          ((A : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ = -(A : Matrix (Fin 4) (Fin 4) F)) ∧
        ∀ k : ↥(StatedSL 4 F),
          ((α k : ↥(StatedSL 4 F)) : GL (Fin 4) F) =
            A * GeneralLinearGroup.inverseTranspose (k : GL (Fin 4) F) * A⁻¹) := by
  classical
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨A, σ, ε, hε, hP⟩ :=
    (LinearFlag.automorphism_generation (K := F) (n := 4) hn3).2 (descendAut 4 F (slAut α))
  have hsq : descendAut 4 F (slAut α) * descendAut 4 F (slAut α) = 1 := by
    rw [← map_mul, ← slAut_mul, hα, slAut_one, map_one]
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  ·
    rw [pow_zero, mul_one] at hP
    rw [hP, conjAut_mul_fieldAut_mul] at hsq
    obtain ⟨hσσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn3 _ _ hsq
    obtain rfl := eq_one_of_mul_self_eq_one hF σ hσσ
    left
    have hslα : slAut α = CatalogueBHigherLinearAction.slConjugation 4 F A := by
      apply eq_of_descendAut_eq hn3
      rw [hP, map_one, mul_one]
      rfl
    refine ⟨A, ⟨c, ?_⟩, fun k => ?_⟩
    · rw [hc]
      ext i j
      simp
    · rw [← toGL_slAut_symm, hslα, CatalogueBHigherLinearAction.toGL_slConjugation]
      congr 2
      rw [← coe_equiv_statedSL, MulEquiv.apply_symm_apply]
  ·
    right
    rw [pow_one] at hP
    have hsq2 : (conjAut 4 F A * fieldAut 4 F σ * dualAut 4 F) ^ 2 = 1 := by
      rw [sq, ← hP]
      exact hsq
    rw [sq_conjAut_fieldAut_dualAut] at hsq2
    obtain ⟨hσσ, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one hn3 _ _ hsq2
    obtain rfl := eq_one_of_mul_self_eq_one hF σ hσσ
    have hsq3 : (conjAut 4 F A * dualAut 4 F) ^ 2 = 1 := by
      rw [map_one, mul_one] at hP
      rw [sq, ← hP]
      exact hsq
    have hslα : slAut α = CatalogueBHigherLinearAction.slConjugation 4 F A *
        CatalogueBGraphForm.slGraphAut 4 F := by
      apply eq_of_descendAut_eq hn3
      rw [map_one, mul_one] at hP
      rw [hP, map_mul]
      rfl
    refine ⟨A, transpose_eq_or_eq_neg_of_sq_conjAut_dualAut hn3 A hsq3, fun k => ?_⟩
    rw [← toGL_slAut_symm, hslα, MulAut.mul_apply, CatalogueBHigherLinearAction.toGL_slConjugation,
      CatalogueBGraphForm.toGL_slGraphAut]
    congr 2
    rw [← coe_equiv_statedSL, MulEquiv.apply_symm_apply]

end CFSG.GH74.Generic.S1
