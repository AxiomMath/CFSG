module

public import CFSG.ClassicalInvolution.AschTight.S19GG2Inv

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S19G

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.G2D4Models
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19F Matrix
open scoped MatrixGroups

variable {F : Type} [Field F]

section Scalar

theorem mem_range_chartB_of_scalar (b : Fin Tag.G2.rank → Fˣ) (A B : SL2 F)
    (hscal : ∃ c : F, ((diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = c • 1) :
    ∃ B' : SL2 F, rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B = g2ChartB F B' := by
  obtain ⟨c, hc⟩ := hscal
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := det_SL2 A
  have hdet' : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [e01] at hdet; simpa using hdet
  have hA00 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet'
  set u : Fˣ := Units.mk0 _ hA00 with hu
  have hA11 : (A : Matrix (Fin 2) (Fin 2) F) 1 1 = ((u⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val, hu, Units.val_mk0]
    exact eq_inv_of_mul_eq_one_right hdet'
  have hAu : A = HSL u := by
    apply SL2_ext
    · simp [coe_HSL, hu]
    · simp [coe_HSL, e01]
    · simp [coe_HSL, e10]
    · rw [hA11]; simp [coe_HSL]
  have hsu : b g2i1 = u⁻¹ * u⁻¹ := by
    have h1 : b g2i1 * u = u⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, ← hA11, hu, Units.val_mk0, e00, e11]
    exact eq_mul_inv_of_mul_eq h1
  set b' : Fin Tag.G2.rank → Fˣ := b * g2tup ((u⁻¹) ^ 3) (u ^ 2) with hb'
  have hb'1 : b' g2i1 = 1 := by
    show b g2i1 * u ^ 2 = 1
    rw [hsu]; group
  have hb'eq : b' = g2tup (b' g2i0) 1 := g2tup_ext rfl hb'1
  refine ⟨HSL (b' g2i0) * B, ?_⟩
  rw [hAu, g2ChartA_HSL, map_mul, g2ChartB_HSL, ← rootDiagUnit_mul, ← hb'eq]

variable [Finite F]

theorem mem_range_chartA_of_scalar (hodd : Odd (Nat.card F)) (b : Fin Tag.G2.rank → Fˣ)
    (A B : SL2 F)
    (hscal : ∃ c : F, ((diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) *
      Matrix.SpecialLinearGroup.toGL B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = c • 1) :
    ∃ A' : SL2 F, rootDiagUnit Tag.G2 b * g2ChartA F A * g2ChartB F B = g2ChartA F A' := by
  obtain ⟨c, hc⟩ := hscal
  rw [Units.val_mul, coe_diagGL_two, Matrix.SpecialLinearGroup.coe_GL_coe_matrix] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  have hdet := det_SL2 B
  have hdet' : (B : Matrix (Fin 2) (Fin 2) F) 0 0 * (B : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
    rw [e01] at hdet; simpa using hdet
  have hB00 : (B : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet'
  set v : Fˣ := Units.mk0 _ hB00 with hv
  have hB11 : (B : Matrix (Fin 2) (Fin 2) F) 1 1 = ((v⁻¹ : Fˣ) : F) := by
    rw [Units.val_inv_eq_inv_val, hv, Units.val_mk0]
    exact eq_inv_of_mul_eq_one_right hdet'
  have hBv : B = HSL v := by
    apply SL2_ext
    · simp [coe_HSL, hv]
    · simp [coe_HSL, e01]
    · simp [coe_HSL, e10]
    · rw [hB11]; simp [coe_HSL]
  have hsv : b g2i0 ^ 2 * b g2i1 ^ 3 = v⁻¹ * v⁻¹ := by
    have h1 : (b g2i0 ^ 2 * b g2i1 ^ 3) * v = v⁻¹ := by
      apply Units.ext
      rw [Units.val_mul, ← hB11, hv, Units.val_mk0]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      rw [e00, e11]
    exact eq_mul_inv_of_mul_eq h1
  set b' : Fin Tag.G2.rank → Fˣ := b * g2tup v 1 with hb'
  have hrel : b' g2i0 ^ 2 * b' g2i1 ^ 3 = 1 := by
    show (b g2i0 * v) ^ 2 * (b g2i1 * 1) ^ 3 = 1
    calc (b g2i0 * v) ^ 2 * (b g2i1 * 1) ^ 3 = (b g2i0 ^ 2 * b g2i1 ^ 3) * v ^ 2 := by
          apply Units.ext
          simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_one]
          ring
      _ = 1 := by rw [hsv]; group
  set w : Fˣ := (b' g2i0 * b' g2i1)⁻¹ with hw
  have hb'eq : b' = g2tup ((w⁻¹) ^ 3) (w ^ 2) := by
    have hrelF : ((b' g2i0 : Fˣ) : F) ^ 2 * ((b' g2i1 : Fˣ) : F) ^ 3 = 1 := by
      have := congrArg Units.val hrel
      simpa using this
    refine g2tup_ext ?_ ?_
    · show b' g2i0 = (w⁻¹) ^ 3
      apply Units.ext
      simp only [hw, inv_inv, Units.val_pow_eq_pow_val, Units.val_mul]
      linear_combination (-((b' g2i0 : Fˣ) : F)) * hrelF
    · show b' g2i1 = w ^ 2
      apply Units.ext
      have h0 : ((b' g2i0 : Fˣ) : F) ≠ 0 := Units.ne_zero _
      have h1 : ((b' g2i1 : Fˣ) : F) ≠ 0 := Units.ne_zero _
      simp only [hw, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp
      linear_combination hrelF
  refine ⟨HSL w * A, ?_⟩
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd A (HSL v)
  rw [hBv, mul_assoc, hcomm, ← mul_assoc, g2ChartB_HSL, ← rootDiagUnit_mul, map_mul,
    g2ChartA_HSL, ← hb'eq]

end Scalar

section Centralizer

variable [Finite F]

theorem mem_range_chartB_of_centralizing (hodd : Odd (Nat.card F)) {x : ModGL Tag.G2 F}
    (hx : x ∈ adjointGroup Tag.G2 F) (hc : ∀ C : SL2 F, x * g2ChartA F C = g2ChartA F C * x) :
    ∃ B' : SL2 F, x = g2ChartB F B' := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  have hxX : x ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨hx, ?_⟩
    rw [← g2ChartA_neg_one hodd ha, ← hc (-1)]
    group
  obtain ⟨t, ht, A, B, rfl⟩ := toralCentralizer_le_prod hodd ha hxX
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨c, -, hcs⟩ := exists_scalar_of_glConjSL_eq (D := 1)
    (E := diagGL (b g2i1) * Matrix.SpecialLinearGroup.toGL A) (fun C => by
      apply g2ChartA_injective hodd
      rw [← prod_conj_chartA hodd b A B C, glConjSL_one]
      exact (mul_inv_eq_iff_eq_mul.mpr (hc C)).symm)
  exact mem_range_chartB_of_scalar b A B ⟨c, by rw [hcs]; simp⟩

theorem mem_range_chartA_of_centralizing (hodd : Odd (Nat.card F)) {x : ModGL Tag.G2 F}
    (hx : x ∈ adjointGroup Tag.G2 F) (hc : ∀ C : SL2 F, x * g2ChartB F C = g2ChartB F C * x) :
    ∃ A' : SL2 F, x = g2ChartA F A' := by
  obtain ⟨a, ha⟩ : ∃ a : Fin Tag.G2.rank → Fˣ, a = ![-1, 1] := ⟨_, rfl⟩
  have hxX : x ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨hx, ?_⟩
    rw [← g2ChartB_neg_one hodd ha, ← hc (-1)]
    group
  obtain ⟨t, ht, A, B, rfl⟩ := toralCentralizer_le_prod hodd ha hxX
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  obtain ⟨c, -, hcs⟩ := exists_scalar_of_glConjSL_eq (D := 1)
    (E := diagGL (b g2i0 ^ 2 * b g2i1 ^ 3) * Matrix.SpecialLinearGroup.toGL B) (fun C => by
      apply g2ChartB_injective hodd
      rw [← prod_conj_chartB hodd b A B C, glConjSL_one]
      exact (mul_inv_eq_iff_eq_mul.mpr (hc C)).symm)
  exact mem_range_chartA_of_scalar hodd b A B ⟨c, by rw [hcs]; simp⟩

theorem exists_centralizer_eq_g2 (hodd : Odd (Nat.card F)) (i : Fin Tag.G2.rank) :
    ∃ Φ' : SL2 F →* adjointGroup .G2 F, Function.Injective Φ' ∧
      Subgroup.centralizer ((g2Chart F i).range : Set (adjointGroup .G2 F)) = Φ'.range := by
  have hcomm := g2ChartA_comm_g2ChartB (F := F) hodd
  rcases fin_g2_cases i with rfl | rfl
  · set N := canonicalRep (coxeterSystem Tag.G2) F g2WeylU with hN
    have hNA : N ∈ adjointGroup .G2 F :=
      canonicalRep_mem_adjointGroup (coxeterSystem Tag.G2) F g2WeylU
    set n : adjointGroup .G2 F := ⟨N, hNA⟩ with hn
    refine ⟨(MulAut.conj n⁻¹).toMonoidHom.comp
      ((g2ChartA F).codRestrict (adjointGroup .G2 F) g2ChartA_mem),
      (MulAut.conj n⁻¹).injective.comp fun A A' h =>
        g2ChartA_injective hodd (congrArg Subtype.val h), le_antisymm ?_ ?_⟩
    · intro x hx
      have hcB : ∀ C, (N * x * N⁻¹) * g2ChartB F C = g2ChartB F C * (N * x * N⁻¹) := by
        intro C
        have h := congrArg Subtype.val
          (Subgroup.mem_centralizer_iff.mp hx (g2Chart F g2i0 C) ⟨C, rfl⟩)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_g2Chart_g2i0, ← hN] at h
        calc N * x * N⁻¹ * g2ChartB F C = N * (x * (N⁻¹ * g2ChartB F C * N)) * N⁻¹ := by group
          _ = N * ((N⁻¹ * g2ChartB F C * N) * x) * N⁻¹ := by rw [h]
          _ = g2ChartB F C * (N * x * N⁻¹) := by group
      obtain ⟨A', hA'⟩ := mem_range_chartA_of_centralizing hodd
        (mul_mem (mul_mem hNA x.2) (inv_mem hNA)) hcB
      refine ⟨A', Subtype.ext ?_⟩
      change N⁻¹ * g2ChartA F A' * N⁻¹⁻¹ = x
      rw [← hA', inv_inv]
      group
    · rintro _ ⟨A, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨C, rfl⟩
      apply Subtype.ext
      change _ * (N⁻¹ * g2ChartA F A * N⁻¹⁻¹) = (N⁻¹ * g2ChartA F A * N⁻¹⁻¹) * _
      rw [coe_g2Chart_g2i0, ← hN, inv_inv]
      calc N⁻¹ * g2ChartB F C * N * (N⁻¹ * g2ChartA F A * N) =
            N⁻¹ * (g2ChartB F C * g2ChartA F A) * N := by group
        _ = N⁻¹ * (g2ChartA F A * g2ChartB F C) * N := by rw [hcomm]
        _ = _ := by group
  · refine ⟨(g2ChartB F).codRestrict (adjointGroup .G2 F) g2ChartB_mem,
      fun B B' h => g2ChartB_injective hodd (congrArg Subtype.val h), le_antisymm ?_ ?_⟩
    · intro x hx
      have hcA : ∀ C, (x : ModGL .G2 F) * g2ChartA F C = g2ChartA F C * x := by
        intro C
        have h := congrArg Subtype.val
          (Subgroup.mem_centralizer_iff.mp hx (g2Chart F g2i1 C) ⟨C, rfl⟩)
        rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_g2Chart_g2i1] at h
        exact h.symm
      obtain ⟨B', hB'⟩ := mem_range_chartB_of_centralizing hodd x.2 hcA
      exact ⟨B', Subtype.ext hB'.symm⟩
    · rintro _ ⟨B, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨C, rfl⟩
      apply Subtype.ext
      change _ * g2ChartB F B = g2ChartB F B * _
      rw [coe_g2Chart_g2i1]
      exact hcomm C B

end Centralizer

end CFSG.ClassicalInvolution.Disconnected.AschTight.S19G
