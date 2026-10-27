module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.QuasisimpleTwoNonab
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable (F : Type) [Field F] [Fintype F]


theorem sl3_perfect : commutator (SpecialLinearGroup (Fin 3) F) = ⊤ :=
  (CFSG.LinearGroups.special_linear_isPerfect (K := F) (n := 3) (by norm_num)
    (Or.inl le_rfl)).commutator_eq_top

theorem sl3_simple_mod_center : IsSimpleGroup (SpecialLinearGroup (Fin 3) F ⧸
    Subgroup.center (SpecialLinearGroup (Fin 3) F)) :=
  (CFSG.LinearGroups.linear_projective_simple (K := F) (n := 3) (by norm_num) (Or.inl le_rfl)).2.1

theorem sl3_card : Nat.card (SpecialLinearGroup (Fin 3) F) =
    (Fintype.card F ^ 3 - 1) * (Fintype.card F ^ 3 - Fintype.card F) * Fintype.card F ^ 2 := by
  have h := Matrix.card_SL_mul_card_units (n := Fin 3) (R := F)
  rw [Matrix.card_GL_field, Nat.card_units, Nat.card_eq_fintype_card (α := F),
    Fin.prod_univ_three] at h
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  set q := Fintype.card F with hqdef
  have hc : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
    rw [Nat.mul_sub, mul_one, ← pow_succ]
  have h' : Nat.card (SpecialLinearGroup (Fin 3) F) * (q - 1) =
      ((q ^ 3 - 1) * (q ^ 3 - q) * q ^ 2) * (q - 1) := by
    rw [h]
    have e0 : ((0 : Fin 3) : ℕ) = 0 := rfl
    have e1 : ((1 : Fin 3) : ℕ) = 1 := rfl
    have e2 : ((2 : Fin 3) : ℕ) = 2 := rfl
    rw [e0, e1, e2, pow_zero, pow_one, hc]
    ring
  exact Nat.eq_of_mul_eq_mul_right (by omega) h'

noncomputable def sl3_center_equiv :
    Subgroup.center (SpecialLinearGroup (Fin 3) F) ≃* rootsOfUnity 3 F := by
  have := SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := F) 0
  rw [Fintype.card_fin] at this
  exact this

theorem sl3_center_card_le : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F)) ≤ 3 := by
  rw [Nat.card_congr (sl3_center_equiv F).toEquiv]
  exact card_rootsOfUnity F 3

theorem sl3_center_card_le_units :
    Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F)) ≤ Fintype.card F - 1 := by
  rw [Nat.card_congr (sl3_center_equiv F).toEquiv]
  have : Nat.card (rootsOfUnity 3 F) ≤ Nat.card Fˣ :=
    Nat.card_le_card_of_injective (fun x => (x : Fˣ)) Subtype.val_injective
  rwa [Nat.card_units, Nat.card_eq_fintype_card (α := F)] at this

theorem sl3_center_odd : ∀ z ∈ Subgroup.center (SpecialLinearGroup (Fin 3) F), Odd (orderOf z) := by
  intro z hz
  have h1 : (sl3_center_equiv F ⟨z, hz⟩) ^ 3 = 1 :=
    Subtype.ext ((mem_rootsOfUnity 3 _).1 (sl3_center_equiv F ⟨z, hz⟩).2)
  have h2 : (⟨z, hz⟩ : Subgroup.center (SpecialLinearGroup (Fin 3) F)) ^ 3 = 1 := by
    apply (sl3_center_equiv F).injective
    rw [map_pow, map_one]
    exact h1
  have h3 : z ^ 3 = 1 := congrArg Subtype.val h2
  exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one h3)

theorem sl3_card_quot_gt : 120 < Nat.card (SpecialLinearGroup (Fin 3) F ⧸
    Subgroup.center (SpecialLinearGroup (Fin 3) F)) := by
  have hmul := (Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (SpecialLinearGroup (Fin 3) F)))
  have hN := sl3_card F
  have hZ3 := sl3_center_card_le F
  have hZq := sl3_center_card_le_units F
  have hZpos : 0 < Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F)) := Nat.card_pos
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  set q := Fintype.card F with hqdef
  set Z := Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) F))
  set Qc := Nat.card (SpecialLinearGroup (Fin 3) F ⧸ Subgroup.center (SpecialLinearGroup (Fin 3) F))
  by_cases h2 : q = 2
  · have hZ1 : Z = 1 := by omega
    have : Nat.card (SpecialLinearGroup (Fin 3) F) = 168 := by
      rw [hN, h2]; norm_num
    rw [hZ1, mul_one, this] at hmul
    omega
  · have hq3 : 3 ≤ q := by omega
    have h27 : 27 ≤ q ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq3 3
    have h9 : 9 ≤ q ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ q ^ 2 := Nat.pow_le_pow_left hq3 2
    have h24 : 24 ≤ q ^ 3 - q := by
      have : q ^ 3 = q * q ^ 2 := by ring
      have : q * 9 ≤ q * q ^ 2 := Nat.mul_le_mul_left q h9
      omega
    have hbig : 26 * 24 * 9 ≤ Nat.card (SpecialLinearGroup (Fin 3) F) := by
      rw [hN]
      exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) h24) h9
    nlinarith

def sl3E01 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

def sl3E12 : SpecialLinearGroup (Fin 3) F :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem sl3E01_mem : sl3E01 F ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [sl3E01]
  · fin_cases i <;> simp [sl3E01]

theorem sl3E12_mem : sl3E12 F ∈ unitriangular 3 F := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [sl3E12]
  · fin_cases i <;> simp [sl3E12]

theorem sl3E01_E12_noncomm : sl3E01 F * sl3E12 F ≠ sl3E12 F * sl3E01 F := by
  intro h
  have h' := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F)) h
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h'
  have := congrFun (congrFun h' 0) 2
  simp [sl3E01, sl3E12, Matrix.mul_apply, Fin.sum_univ_three] at this

theorem sl3_nonab_two [CharP F 2] : ∃ Q : Subgroup (SpecialLinearGroup (Fin 3) F),
    IsPGroup 2 Q ∧ ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
  refine ⟨unitriangular 3 F, ?_, sl3E01 F, sl3E01_mem F, sl3E12 F, sl3E12_mem F,
    sl3E01_E12_noncomm F⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  refine IsPGroup.of_card (n := n * 3) ?_
  rw [card_unitriangular, Nat.card_eq_fintype_card, hn, ← pow_mul]

theorem isQuasisimpleTwoNonab_sl3 [CharP F 2] :
    IsQuasisimpleTwoNonab (SpecialLinearGroup (Fin 3) F) :=
  ⟨sl3_perfect F, sl3_simple_mod_center F, sl3_card_quot_gt F, sl3_center_odd F, sl3_nonab_two F⟩

end CFSG.AGLEmbeddingD2.Tits.GN516
