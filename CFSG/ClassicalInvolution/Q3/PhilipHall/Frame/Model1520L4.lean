module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Orth
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterL4
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Core

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520L

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ClassicalInvolution.WeakCT
  CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem fixed_range_of_gens {n : ℕ} (α : MulAut (projectiveSL n F))
    (φ : SL(2, F) →* SL(n, F))
    (hU : ∀ c : F, α (proj n F (φ (sl2Upper c))) = proj n F (φ (sl2Upper c)))
    (hL : ∀ c : F, α (proj n F (φ (sl2Lower c))) = proj n F (φ (sl2Lower c))) :
    ∀ r ∈ φ.range, α (proj n F r) = proj n F r := by
  rintro _ ⟨A, rfl⟩
  have hcl := CFSG.LieType.Steinberg.Sp.mem_closure_sl2 A
  have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
      MonoidHom.eqLocus (((α : projectiveSL n F →* projectiveSL n F)).comp ((proj n F).comp φ))
        ((proj n F).comp φ) := by
    rw [Subgroup.closure_le]
    rintro x (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact hU c
    · exact hL c
  exact hle hcl

theorem blockSL_zero_upper (c : F) :
    blockSL F 4 2 0 (by norm_num) (sl2Upper c) = u01 c := by
  apply Subtype.ext
  rw [WeakCT.coe_blockSL, blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u01, E01, sl2Upper]

theorem blockSL_zero_lower (c : F) :
    blockSL F 4 2 0 (by norm_num) (sl2Lower c) = u10 c := by
  apply Subtype.ext
  rw [WeakCT.coe_blockSL, blockMat_four_zero]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u10, E10, sl2Lower]

theorem blockSL_two_upper (c : F) :
    blockSL F 4 2 2 (by norm_num) (sl2Upper c) = u23 c := by
  apply Subtype.ext
  rw [WeakCT.coe_blockSL, blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u23, E23, sl2Upper]

theorem blockSL_two_lower (c : F) :
    blockSL F 4 2 2 (by norm_num) (sl2Lower c) = u32 c := by
  apply Subtype.ext
  rw [WeakCT.coe_blockSL, blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [u32, E32, sl2Lower]

theorem aut_fix_blocks_three [Finite F] (hF3 : Nat.card F = 3) (α : MulAut (projectiveSL 4 F))
    (hu01 : ∀ c, α (proj 4 F (u01 c)) = proj 4 F (u01 c))
    (hu10 : ∀ c, α (proj 4 F (u10 c)) = proj 4 F (u10 c))
    (hu23 : ∀ c, α (proj 4 F (u23 c)) = proj 4 F (u23 c))
    (hu32 : ∀ c, α (proj 4 F (u32 c)) = proj 4 F (u32 c)) : α * α = 1 := by
  have h2 : (2 : F) ≠ 0 := Model1520Aux.two_ne_zero_of_card_eq_three hF3
  have hfix : ∀ r ∈ (blockSL F 4 2 0 (by norm_num)).range, α (proj 4 F r) = proj 4 F r :=
    fixed_range_of_gens α _ (fun c => by rw [blockSL_zero_upper]; exact hu01 c)
      (fun c => by rw [blockSL_zero_lower]; exact hu10 c)
  have hfix' : ∀ r ∈ (blockSL F 4 2 2 (by norm_num)).range, α (proj 4 F r) = proj 4 F r :=
    fixed_range_of_gens α _ (fun c => by rw [blockSL_two_upper]; exact hu23 c)
      (fun c => by rw [blockSL_two_lower]; exact hu32 c)
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hαeq⟩ := hform α
  interval_cases ε
  · rw [pow_zero, mul_one] at hαeq
    subst hαeq
    obtain ⟨hσ, a, b, ha, hb, hM⟩ := aut_fix_blocks_zero h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one]
    have hsq : ∀ x : F, x ≠ 0 → x * x = 1 := by
      intro x hx
      have := Fintype.ofFinite F
      have hcard : Fintype.card F = 3 := by rw [← Nat.card_eq_fintype_card, hF3]
      have h := FiniteField.pow_card_sub_one_eq_one x hx
      rw [hcard] at h
      simpa [pow_two] using h
    have hAA : A * A = 1 := by
      apply Units.ext
      rw [Units.val_mul, hM]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, hsq a ha,
        hsq b hb]
    calc conjAut 4 F A * conjAut 4 F A = conjAut 4 F (A * A) := (map_mul _ _ _).symm
      _ = 1 := by rw [hAA, map_one]
  · rw [pow_one] at hαeq
    subst hαeq
    obtain ⟨hσ, m, n, hm, hn, hM⟩ := aut_fix_blocks_one h2 A σ hfix hfix'
    subst hσ
    have h1 : fieldAut 4 F (RingEquiv.refl F) = 1 := map_one _
    rw [h1, mul_one]
    exact sq_of_antidiag A m n hm hn hM

theorem coe_rootInv_four :
    ((rootInv F (show 2 ≤ 4 by norm_num) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      !![-1, 0, 0, 0; 0, -1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  rw [coe_rootInv, negBlock_eq_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem u01_cube (h3 : (3 : F) = 0) (c : F) : u01 c ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, u01, E01] <;>
    linear_combination c * h3

theorem u10_cube (h3 : (3 : F) = 0) (c : F) : u10 c ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, u10, E10] <;>
    linear_combination c * h3

theorem u23_cube (h3 : (3 : F) = 0) (c : F) : u23 c ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, u23, E23] <;>
    linear_combination c * h3

theorem u32_cube (h3 : (3 : F) = 0) (c : F) : u32 c ^ 3 = 1 := by
  apply Subtype.ext
  rw [pow_three, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four, u32, E32] <;>
    linear_combination c * h3

theorem u01_comm (c : F) : u01 c * rootInv F (show 2 ≤ 4 by norm_num) =
    rootInv F (show 2 ≤ 4 by norm_num) * u01 c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootInv_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, u01, E01]

theorem u10_comm (c : F) : u10 c * rootInv F (show 2 ≤ 4 by norm_num) =
    rootInv F (show 2 ≤ 4 by norm_num) * u10 c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootInv_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, u10, E10]

theorem u23_comm (c : F) : u23 c * rootInv F (show 2 ≤ 4 by norm_num) =
    rootInv F (show 2 ≤ 4 by norm_num) * u23 c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootInv_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, u23, E23]

theorem u32_comm (c : F) : u32 c * rootInv F (show 2 ≤ 4 by norm_num) =
    rootInv F (show 2 ≤ 4 by norm_num) * u32 c := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_rootInv_four]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four, u32, E32]

theorem rigid3_psl4 [Finite F] (hF3 : Nat.card F = 3) :
    Rigid3 (projectiveSL 4 F) (proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))) := by
  have h3 : (3 : F) = 0 := Model1520Aux.three_eq_zero_of_card_eq_three hF3
  refine ⟨{s | ∃ c : F, s = proj 4 F (u01 c) ∨ s = proj 4 F (u10 c) ∨ s = proj 4 F (u23 c) ∨
    s = proj 4 F (u32 c)}, ?_, ?_⟩
  · rintro s ⟨c, rfl | rfl | rfl | rfl⟩
    · exact ⟨by rw [← map_pow, u01_cube h3, map_one], by rw [← map_mul, ← map_mul, u01_comm]⟩
    · exact ⟨by rw [← map_pow, u10_cube h3, map_one], by rw [← map_mul, ← map_mul, u10_comm]⟩
    · exact ⟨by rw [← map_pow, u23_cube h3, map_one], by rw [← map_mul, ← map_mul, u23_comm]⟩
    · exact ⟨by rw [← map_pow, u32_cube h3, map_one], by rw [← map_mul, ← map_mul, u32_comm]⟩
  · intro α hk hfix
    have hαα : α * α = 1 :=
      aut_fix_blocks_three hF3 α (fun c => hfix _ ⟨c, Or.inl rfl⟩)
        (fun c => hfix _ ⟨c, Or.inr (Or.inl rfl)⟩)
        (fun c => hfix _ ⟨c, Or.inr (Or.inr (Or.inl rfl))⟩)
        (fun c => hfix _ ⟨c, Or.inr (Or.inr (Or.inr rfl))⟩)
    obtain ⟨k, hk⟩ := hk
    have h2' : orderOf α ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hαα)
    have h3' : orderOf α ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hg := Nat.dvd_gcd h2' h3'
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num))] at hg
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

theorem model1520_of_PSL {G : Type} [Group G] [Finite G] [Finite F] {X : Subgroup G} {t : G}
    (htX : t ∈ X) (ht : t * t = 1) (hF3 : Nat.card F = 3)
    (e : ↥X ⧸ Subgroup.center ↥X ≃* projectiveSL 4 F)
    (het : e (QuotientGroup.mk ⟨t, htX⟩) = proj 4 F (rootInv F (show 2 ≤ 4 by norm_num))) :
    Model1520 X t := by
  have hP : Group.IsPerfect (SpecialLinearGroup (Fin 4) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)
  have : Group.IsPerfect (projectiveSL 4 F) :=
    Group.IsPerfect.ofSurjective (f := proj 4 F) (proj_surjective 4 F)
  exact model1520_of_rigid3 htX ht this e het (rigid3_psl4 hF3)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520L
