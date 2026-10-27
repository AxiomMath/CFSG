module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ5L4T2b
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4LinNSL
public import CFSG.ClassicalInvolution.Q3.TA3SOLL4U4PSL

public section

namespace CFSG.ClassicalInvolution.Q3.TA3.Q5L4

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag CFSG.ComponentClassification.CatFactsL4U4
  StabL
open CFSG.ComponentClassification.OddSelector
open CFSG.ComponentClassification.CatalogueBProjectiveQuadratic
open scoped MatrixGroups

theorem exists_ne_comm_of_perfect {H : Type*} [Group H] [Nontrivial H] [Group.IsPerfect H] :
    ∃ a b : H, a * b ≠ b * a := by
  by_contra hc
  apply Group.IsPerfect.not_isMulCommutative H
  refine IsMulCommutative.of_comm fun a b => ?_
  by_contra hab
  exact hc ⟨a, b, hab⟩

theorem card_center_SL2_le {E : Type} [Field E] [Finite E] :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) E)) ≤ 2 := by
  classical
  have key : ∀ z : Subgroup.center (SpecialLinearGroup (Fin 2) E), z ≠ 1 →
      ((z : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
        Matrix.scalar (Fin 2) (-1) := by
    intro z hz
    obtain ⟨r, hr, hrz⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp z.2
    rw [Fintype.card_fin] at hr
    have hr1 : r ≠ 1 := by
      rintro rfl
      apply hz
      apply Subtype.ext
      apply Subtype.ext
      rw [← hrz, map_one]
      rfl
    have hr2 : r = -1 := by
      have h0 : (r - 1) * (r + 1) = 0 := by linear_combination hr
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (sub_eq_zero.1 h) hr1
      · linear_combination h
    rw [← hrz, hr2]
  let g : Subgroup.center (SpecialLinearGroup (Fin 2) E) → Fin 2 := fun z => if z = 1 then 0 else 1
  have hg : Function.Injective g := by
    intro z z' hzz'
    by_cases h1 : z = 1 <;> by_cases h2 : z' = 1
    · rw [h1, h2]
    · simp [g, h1, h2] at hzz'
    · simp [g, h1, h2] at hzz'
    · apply Subtype.ext
      apply Subtype.ext
      rw [key z h1, key z' h2]
  calc Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) E)) ≤ Nat.card (Fin 2) :=
        Nat.card_le_card_of_injective g hg
    _ = 2 := by simp

variable {K : Type} [Field K] [Fintype K]

theorem exists_conj_to_k₀ (hF : Fintype.card K % 4 = 3) {g : SpecialLinearGroup (Fin 4) K}
    (hg : (g : Matrix (Fin 4) (Fin 4) K) * g = -1) :
    ∃ h : SpecialLinearGroup (Fin 4) K, MulAut.conj (proj 4 K h) (proj 4 K g) = proj 4 K k₀ := by
  have hns : ¬ IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  obtain ⟨m, hmd, hmX⟩ := exists_conj_of_sq_eq_neg_one (by omega) hns hg Blocks.stdJ_mul_stdJ
  set mS : SpecialLinearGroup (Fin 4) K := ⟨m, hmd⟩ with hmS
  refine ⟨mS, ?_⟩
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  have hmi : m * ((mS⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 :=
    congrArg (fun y : SpecialLinearGroup (Fin 4) K => (y : Matrix (Fin 4) (Fin 4) K))
      (mul_inv_cancel mS)
  change m * (g : Matrix (Fin 4) (Fin 4) K) *
    ((mS⁻¹ : SpecialLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = stdJ
  rw [hmX, Matrix.mul_assoc, hmi, Matrix.mul_one]

theorem exists_L_k₀ (hF : Fintype.card K % 4 = 3) :
    ∃ L : Subgroup (projectiveSL 4 K), L ≤ Subgroup.centralizer {proj 4 K k₀} ∧
      IsSimpleGroup L ∧ Group.IsPerfect L ∧
      Nat.card K ^ 2 * ((Nat.card K ^ 2) ^ 2 - 1) ≤ 2 * Nat.card L := by
  classical
  have hns : ¬ IsSquare (-1 : K) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_card_mod_four hF
  set μ : Kˣ := -1 with hμ
  have : Fact (¬ IsSquare (μ : K)) := ⟨by simpa [hμ] using hns⟩
  have hB2 : Matrix.SpecialLinearGroup.toGL (k₀ : SpecialLinearGroup (Fin 4) K) ^ 2 =
      GeneralLinearGroup.scalar (Fin 4) μ := toGL_k₀_sq
  have hd : (letI := matrixModule (Matrix.SpecialLinearGroup.toGL
      (k₀ : SpecialLinearGroup (Fin 4) K)) μ hB2;
      Module.finrank (extension (μ : K)) (Fin 4 → K) = 2) := by
    have h := matrixDimension_twice (Matrix.SpecialLinearGroup.toGL
      (k₀ : SpecialLinearGroup (Fin 4) K)) μ hB2
    rw [Fintype.card_fin] at h
    change matrixDimension (Matrix.SpecialLinearGroup.toGL
      (k₀ : SpecialLinearGroup (Fin 4) K)) μ hB2 = 2
    omega
  set Ψ := rowSPsi hB2 hd with hΨ
  have hU : rowSU μ Ψ = Matrix.SpecialLinearGroup.toGL (k₀ : SpecialLinearGroup (Fin 4) K) :=
    rowSU_rowSPsi hB2 hd
  have : Finite (extension (μ : K)) :=
    CFSG.ComponentClassification.CatalogueBProjectiveInvolution.quadraticExtension_finite _
  have hE : Nat.card (extension (μ : K)) = Nat.card K ^ 2 := card_extension μ
  have h4 : 4 ≤ Nat.card (extension (μ : K)) := by
    rw [hE]
    have : 3 ≤ Nat.card K := ProjectiveEigenspace.three_le_card_of_two_ne_zero h2
    nlinarith
  set φ := (proj 4 K).comp (L4U4.rowSPiSL μ Ψ) with hφ
  have hker := L4U4.ker_proj_rowSPiSL μ Ψ
  refine ⟨φ.range, ?_, L4U4.isSimpleGroup_range_of_ker_eq_center h4 φ hker,
    L4U4.isPerfect_range_of_ker_eq_center h4 φ hker, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, hφ, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_mul, map_mul, L4U4.toGL_rowSPiSL, ← hU]
    exact rowSPi_commute_rowSU μ Ψ _
  · have hmul := Subgroup.card_ker_mul_card_range φ
    rw [hker] at hmul
    have hcen := card_center_SL2_le (E := extension (μ : K))
    have hSL : Nat.card (SpecialLinearGroup (Fin 2) (extension (μ : K))) =
        Nat.card (extension (μ : K)) * (Nat.card (extension (μ : K)) ^ 2 - 1) := by
      let := Fintype.ofFinite (extension (μ : K))
      have hq : 1 < Fintype.card (extension (μ : K)) := Fintype.one_lt_card
      rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
        Nat.card_eq_fintype_card, show Fintype.card (extension (μ : K)) ^ 2 -
          Fintype.card (extension (μ : K)) = Fintype.card (extension (μ : K)) *
            (Fintype.card (extension (μ : K)) - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
        Nat.mul_div_cancel _ (by omega), mul_comm]
    rw [hSL, hE] at hmul
    calc Nat.card K ^ 2 * ((Nat.card K ^ 2) ^ 2 - 1) =
        Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) (extension (μ : K)))) *
          Nat.card φ.range := hmul.symm
      _ ≤ 2 * Nat.card φ.range := Nat.mul_le_mul_right _ hcen

theorem J₀_eq_L (hF : Fintype.card K % 4 = 3) :
    IsSimpleGroup (J₀ K) ∧ Group.IsPerfect (J₀ K) := by
  obtain ⟨L, hLC, hLs, hLp, hLc⟩ := exists_L_k₀ hF
  have hLJ : L = J₀ K := eq_J₀ hF hLC (Subgroup.isPerfect_iff.mp hLp) hLc
  rw [← hLJ]
  exact ⟨hLs, hLp⟩

omit [Fintype K] in
theorem J₀_le_centralizer : J₀ K ≤ Subgroup.centralizer {proj 4 K k₀} := by
  rintro _ ⟨x, hx, rfl⟩
  have hxC : x ∈ C₀ K := by
    have hle : S₀ K ≤ C₀ K := Subgroup.commutator_le.2 fun a ha b hb =>
      mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
    exact hle hx
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  rw [C₀, Subgroup.mem_centralizer_singleton_iff] at hxC
  rw [hxC]

theorem noOddNormal_J₀ (hF : Fintype.card K % 4 = 3) : NoOddNormal (J₀ K) := by
  obtain ⟨hs, hp⟩ := J₀_eq_L (K := K) hF
  exact noOddNormal_of_isSimpleGroup exists_ne_comm_of_perfect

theorem noQ8Fix_Nc (hF : Fintype.card K % 4 = 3) {p f : ℕ} (hp : p.Prime)
    (hK : Nat.card K = p ^ f) : NoQ8Fix (projectiveSL 4 K) (J₀ K) := by
  have hU := hasUnipotents_J₀ hF
  have hcyc := isCyclic_centralizer hF hU
  refine noQ8Fix_of_dichotomy_pow
    {α | ∃ y ∈ Subgroup.centralizer (J₀ K : Set (projectiveSL 4 K)), α = MulAut.conj y}
    ?_ fun α hfix hα8 => ?_
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : Subgroup.centralizer
      (J₀ K : Set (projectiveSL 4 K))) ⟨y', hy'⟩)
  · rcases inner_or_alternating hF hp hK α (m := 2) (by simpa using hα8) hU hfix with
      ⟨y, rfl⟩ | ⟨A, hA, rfl⟩
    · left
      refine ⟨y, ?_, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hfix x hx
      rw [MulAut.conj_apply] at this
      calc x * y = y * x * y⁻¹ * y := by rw [this]
        _ = y * x := by group
    · exact Or.inr (conjAut_mul_dualAut_sq_of_alt A hA)

end CFSG.ClassicalInvolution.Q3.TA3.Q5L4
