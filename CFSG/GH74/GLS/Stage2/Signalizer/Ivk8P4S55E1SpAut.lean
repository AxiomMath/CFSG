module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55E1SpRad
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Odd

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartTwo.KFacts

section Generic

variable {r : ℕ} {K : Type} [Field K]

theorem exists_smul_of_proj_eq_sp {g h : StatedSp r K}
    (e : SymplecticFlag.proj r K g = SymplecticFlag.proj r K h) :
    ∃ c : K, c ≠ 0 ∧ ((h : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      c • ((g : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
  have h1 : g⁻¹ * h ∈ spScalars r K := QuotientGroup.eq.mp e
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at h1
  obtain ⟨c, hc⟩ := h1
  refine ⟨(c : K), c.ne_zero, ?_⟩
  have h2 : (h : GL (Fin r ⊕ Fin r) K) = (g : GL (Fin r ⊕ Fin r) K) *
      ((g⁻¹ * h : StatedSp r K) : GL (Fin r ⊕ Fin r) K) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
  rw [h2, Units.val_mul, ← hc, Matrix.GeneralLinearGroup.coe_scalar, scalar_apply,
    ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]

end Generic

section Two

variable {F : Type} [Field F]

theorem comm_of_fix_sp (h4 : (4 : F) ≠ 0) {A : gsp 2 F} {σ : F ≃+* F}
    {g : StatedSp 2 F}
    (h : conjAut 2 F A (fieldAut 2 F σ (SymplecticFlag.proj 2 F g)) =
      SymplecticFlag.proj 2 F g)
    (t1 : Matrix.trace ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 4)
    (t2 : Matrix.trace (((g : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ) = 4) :
    ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ := by
  rw [fieldAut_proj, conjAut_proj] at h
  obtain ⟨c, hc0, hc⟩ := exists_smul_of_proj_eq_sp h
  have hy : (((conjSp 2 F A (fieldSp 2 F σ g) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).map σ *
        (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
    rw [coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]
  have hA' : (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 :=
    Units.inv_mul _
  rw [hy] at hc
  have htr := congrArg Matrix.trace hc
  rw [Matrix.trace_smul, smul_eq_mul, Matrix.trace_mul_cycle, hA', Matrix.one_mul] at htr
  rw [t1, t2] at htr
  have hc1 : c = 1 := by
    have : (4 : F) * c = 4 * 1 := by linear_combination -htr
    exact mul_left_cancel₀ h4 this
  rw [hc1, one_smul] at hc
  have h5 := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F =>
    M * ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) hc
  rw [h5, Matrix.mul_assoc, Matrix.mul_assoc, hA', Matrix.mul_one]

theorem trace_fromBlocks_two (A B C D : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace (fromBlocks A B C D) = Matrix.trace A + Matrix.trace D := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem comm_blocks {P Q R T C : Matrix (Fin 2) (Fin 2) F}
    (h : fromBlocks P Q R T * fromBlocks 0 C 0 0 = fromBlocks 0 C 0 0 * fromBlocks P Q R T) :
    C * R = 0 ∧ P * C = C * T ∧ R * C = 0 := by
  rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at h
  exact ⟨h.1.symm, h.2.1, h.2.2.2⟩

theorem solve_two (P R T : Matrix (Fin 2) (Fin 2) F)
    (e1 : !![(1 : F), 0; 0, 0] * R = 0 ∧ P * !![(1 : F), 0; 0, 0] = !![(1 : F), 0; 0, 0] * T ∧
      R * !![(1 : F), 0; 0, 0] = 0)
    (e2 : !![(0 : F), 0; 0, 1] * R = 0 ∧ P * !![(0 : F), 0; 0, 1] = !![(0 : F), 0; 0, 1] * T ∧
      R * !![(0 : F), 0; 0, 1] = 0)
    (e3 : !![(0 : F), 1; 1, 0] * R = 0 ∧ P * !![(0 : F), 1; 1, 0] = !![(0 : F), 1; 1, 0] * T ∧
      R * !![(0 : F), 1; 1, 0] = 0) :
    R = 0 ∧ ∃ l : F, P = l • 1 ∧ T = l • 1 := by
  obtain ⟨a1, b1, c1⟩ := e1
  obtain ⟨a2, b2, c2⟩ := e2
  obtain ⟨a3, b3, c3⟩ := e3
  have ent : ∀ {M N : Matrix (Fin 2) (Fin 2) F}, M = N → ∀ i j, M i j = N i j :=
    fun h i j => by rw [h]
  have a1' := ent a1
  have a2' := ent a2
  have b1' := ent b1
  have b2' := ent b2
  have b3' := ent b3
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a1' a2' b1' b2' b3'
  obtain ⟨r00, r01⟩ := a1'
  obtain ⟨r10, r11⟩ := a2'
  obtain ⟨⟨p00, t01⟩, p10⟩ := b1'
  obtain ⟨p01, t10, p11⟩ := b2'
  obtain ⟨⟨-, p00'⟩, p11', -⟩ := b3'
  refine ⟨?_, P 0 0, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [r00, r01, r10, r11]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact p01
    · exact p10
    · linear_combination p11' - p00
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact p00.symm
    · exact t01.symm
    · exact t10.symm
    · linear_combination -p00'

theorem solve_one (P Q R T : Matrix (Fin 2) (Fin 2) F)
    (e1 : !![(1 : F), 0; 0, 0] * R = 0 ∧ P * !![(1 : F), 0; 0, 0] = !![(1 : F), 0; 0, 0] * T ∧
      R * !![(1 : F), 0; 0, 0] = 0)
    (e3 : !![(0 : F), 1; 1, 0] * R = 0 ∧ P * !![(0 : F), 1; 1, 0] = !![(0 : F), 1; 1, 0] * T ∧
      R * !![(0 : F), 1; 1, 0] = 0)
    (hL : Q * !![(1 : F), 0; -1, 1] = !![(1 : F), 1; 0, 1] * Q) :
    R = 0 ∧ ∃ l x p q : F, P = !![l, x; 0, l] ∧ T = !![l, 0; x, l] ∧ Q = !![p, q; -q, 0] := by
  obtain ⟨a1, b1, c1⟩ := e1
  obtain ⟨a3, b3, c3⟩ := e3
  have ent : ∀ {M N : Matrix (Fin 2) (Fin 2) F}, M = N → ∀ i j, M i j = N i j :=
    fun h i j => by rw [h]
  have a1' := ent a1
  have a3' := ent a3
  have b1' := ent b1
  have b3' := ent b3
  have hL' := ent hL
  simp [Matrix.mul_apply, Fin.sum_univ_two] at a1' a3' b1' b3' hL'
  obtain ⟨r00, r01⟩ := a1'
  obtain ⟨⟨r10, r11⟩, -, -⟩ := a3'
  obtain ⟨⟨p00, t01⟩, p10⟩ := b1'
  obtain ⟨⟨p01, p00'⟩, p11', -⟩ := b3'
  obtain ⟨q10, q11⟩ := hL'
  refine ⟨?_, P 0 0, P 0 1, Q 0 0, Q 0 1, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [r00, r01, r10, r11]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact p10
    · linear_combination p11' - p00
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact p00.symm
    · exact t01.symm
    · exact p01.symm
    · linear_combination -p00'
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
    · linear_combination -q10
    · exact q11

theorem siegel_eq_one_add (c : F) :
    fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) (c • !![(1 : F), 0; 0, 0])
      (0 : Matrix (Fin 2) (Fin 2) F) (1 : Matrix (Fin 2) (Fin 2) F) =
      1 + c • fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(1 : F), 0; 0, 0] 0 0 := by
  rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
  simp

theorem siegel_map (σ : F ≃+* F) (c : F) :
    (fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) (c • !![(1 : F), 0; 0, 0])
      (0 : Matrix (Fin 2) (Fin 2) F) (1 : Matrix (Fin 2) (Fin 2) F)).map σ =
      1 + σ c • fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(1 : F), 0; 0, 0] 0 0 := by
  rw [← siegel_eq_one_add, fromBlocks_map]
  congr 1
  · exact Matrix.map_one σ (map_zero σ) (map_one σ)
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · exact Matrix.map_zero σ (map_zero σ)
  · exact Matrix.map_one σ (map_zero σ) (map_one σ)

theorem sigma_id_of_comm (A A' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (hA' : A' * A = 1)
    (σ : F ≃+* F)
    (hc : ∀ c : F, fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) (c • !![(1 : F), 0; 0, 0])
      (0 : Matrix (Fin 2) (Fin 2) F) (1 : Matrix (Fin 2) (Fin 2) F) * A =
      A * (fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) (c • !![(1 : F), 0; 0, 0])
      (0 : Matrix (Fin 2) (Fin 2) F) (1 : Matrix (Fin 2) (Fin 2) F)).map σ) :
    ∀ c, σ c = c := by
  set X : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
    fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(1 : F), 0; 0, 0] 0 0 with hX
  intro c
  have h1 := hc 1
  have hc' := hc c
  rw [siegel_map, siegel_eq_one_add, map_one, one_smul] at h1
  rw [siegel_map, siegel_eq_one_add] at hc'
  have hXA : X * A = A * X := by
    rw [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one] at h1
    exact add_left_cancel h1
  have h2 : c • (X * A) = σ c • (A * X) := by
    rw [add_mul, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul] at hc'
    exact add_left_cancel hc'
  rw [hXA] at h2
  have h3 : (c - σ c) • (A * X) = 0 := by rw [sub_smul, h2, sub_self]
  have h4 : (c - σ c) • X = 0 := by
    have := congrArg (fun M => A' * M) h3
    simpa [Matrix.mul_smul, ← Matrix.mul_assoc, hA'] using this
  have h5 := congrFun (congrFun h4 (Sum.inl 0)) (Sum.inr 0)
  simp [hX] at h5
  exact (sub_eq_zero.mp h5).symm

theorem nilp_of_comm_two (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (h1 : A * fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(1 : F), 0; 0, 0]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) =
      fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(1 : F), 0; 0, 0]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) * A)
    (h2 : A * fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(0 : F), 0; 0, 1]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) =
      fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(0 : F), 0; 0, 1]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) * A)
    (h3 : A * fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(0 : F), 1; 1, 0]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) =
      fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(0 : F), 1; 1, 0]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) * A) :
    ∃ (l : F) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F), A = l • 1 + M ∧ M * M = 0 := by
  obtain ⟨P, Q, R, T, rfl⟩ : ∃ P Q R T : Matrix (Fin 2) (Fin 2) F, A = fromBlocks P Q R T :=
    ⟨A.toBlocks₁₁, A.toBlocks₁₂, A.toBlocks₂₁, A.toBlocks₂₂, (fromBlocks_toBlocks A).symm⟩
  obtain ⟨hR, l, hP, hT⟩ := solve_two P R T (comm_blocks h1) (comm_blocks h2) (comm_blocks h3)
  subst hR hP hT
  refine ⟨l, fromBlocks 0 Q 0 0, ?_, ?_⟩
  · rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
    simp
  · rw [fromBlocks_multiply]
    simp

theorem nilp_of_comm_one (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (h1 : A * fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(1 : F), 0; 0, 0]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) =
      fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(1 : F), 0; 0, 0]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) * A)
    (h3 : A * fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(0 : F), 1; 1, 0]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) =
      fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) !![(0 : F), 1; 1, 0]
        (0 : Matrix (Fin 2) (Fin 2) F) (0 : Matrix (Fin 2) (Fin 2) F) * A)
    (hL : A * fromBlocks (!![(1 : F), 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0
        (!![(1 : F), 0; -1, 1] : Matrix (Fin 2) (Fin 2) F) =
      fromBlocks (!![(1 : F), 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0
        (!![(1 : F), 0; -1, 1] : Matrix (Fin 2) (Fin 2) F) * A) :
    ∃ (l : F) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F), A = l • 1 + M ∧ M * M = 0 := by
  obtain ⟨P, Q, R, T, rfl⟩ : ∃ P Q R T : Matrix (Fin 2) (Fin 2) F, A = fromBlocks P Q R T :=
    ⟨A.toBlocks₁₁, A.toBlocks₁₂, A.toBlocks₂₁, A.toBlocks₂₂, (fromBlocks_toBlocks A).symm⟩
  have hQ : Q * !![(1 : F), 0; -1, 1] = !![(1 : F), 1; 0, 1] * Q := by
    rw [fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at hL
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add] at hL
    exact hL.2.1
  obtain ⟨hR, l, x, p, q, hP, hT, hQq⟩ :=
    solve_one P Q R T (comm_blocks h1) (comm_blocks h3) hQ
  subst hR hP hT hQq
  refine ⟨l, fromBlocks !![0, x; 0, 0] !![p, q; -q, 0] 0 !![0, 0; x, 0], ?_, ?_⟩
  · rw [← fromBlocks_one, fromBlocks_smul, fromBlocks_add]
    congr 1
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
    · simp
    · simp
    · ext i j
      fin_cases i <;> fin_cases j <;> simp
  · rw [fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;> simp
    all_goals ring

theorem pow_of_sq_zero {r : ℕ} [Fact r.Prime] [CharP F r]
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F} (hM : M * M = 0) (l : F) :
    ((l • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) + M) ^ r = (l ^ r) • 1 := by
  have hMr : M ^ r = 0 := by
    have hr2 : 2 ≤ r := (Fact.out : r.Prime).two_le
    rw [show r = 2 + (r - 2) by omega, pow_add, pow_two, hM, zero_mul]
  rw [add_pow_char_of_commute r ((Commute.one_left M).smul_left l), hMr, add_zero, smul_pow,
    one_pow]

theorem conjAut_eq_one_of_scalar_sp {B : gsp 2 F} {c : F}
    (hB : ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = c • 1) :
    conjAut 2 F B = 1 := by
  have h1 : ((B : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      (((B : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := Units.mul_inv _
  have hc : c ≠ 0 := by
    intro h0
    rw [hB, h0, zero_smul, Matrix.zero_mul] at h1
    exact zero_ne_one h1
  have hBinv : (((B : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = c⁻¹ • 1 := by
    rw [hB, smul_mul_assoc, one_mul] at h1
    have h2 := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => c⁻¹ • M) h1
    simpa [smul_smul, hc] using h2
  ext x
  obtain ⟨g, rfl⟩ := proj_surjective x
  rw [conjAut_proj, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  apply Units.ext
  rw [coe_conjSp, Units.val_mul, Units.val_mul, hB, hBinv, smul_mul_assoc, one_mul,
    mul_smul_comm, mul_one, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem conjAut_pow_eq_one {r : ℕ} [Fact r.Prime] [CharP F r] {A : gsp 2 F} {l : F}
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hA : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = l • 1 + M)
    (hM : M * M = 0) : conjAut 2 F A ^ r = 1 := by
  rw [← map_pow]
  refine conjAut_eq_one_of_scalar_sp (c := l ^ r) ?_
  rw [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hA, pow_of_sq_zero hM]

theorem trace_siegel (C : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace (fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
      (1 : Matrix (Fin 2) (Fin 2) F)) = 4 := by
  rw [trace_fromBlocks_two]
  simp [Matrix.trace]
  norm_num

theorem trace_siegel_map (σ : F ≃+* F) (C : Matrix (Fin 2) (Fin 2) F) :
    Matrix.trace ((fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
      (1 : Matrix (Fin 2) (Fin 2) F)).map σ) = 4 := by
  rw [fromBlocks_map, Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.map_zero σ (map_zero σ)]
  exact trace_siegel _

theorem siegel_eq_one_add' (C : Matrix (Fin 2) (Fin 2) F) :
    fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
        (1 : Matrix (Fin 2) (Fin 2) F) =
      1 + fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
        (0 : Matrix (Fin 2) (Fin 2) F) := by
  rw [← fromBlocks_one, fromBlocks_add]
  simp

theorem comm_siegel_of_fix (h4 : (4 : F) ≠ 0) {A : gsp 2 F} {σ : F ≃+* F}
    (C : Matrix (Fin 2) (Fin 2) F) (hC : Cᵀ = C)
    (h : conjAut 2 F A (fieldAut 2 F σ (SymplecticFlag.proj 2 F (siegelElt C hC))) =
      SymplecticFlag.proj 2 F (siegelElt C hC)) :
    fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
        (1 : Matrix (Fin 2) (Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
          (1 : Matrix (Fin 2) (Fin 2) F)).map σ := by
  have := comm_of_fix_sp h4 h (by rw [coe_siegelElt]; exact trace_siegel C)
    (by rw [coe_siegelElt]; exact trace_siegel_map σ C)
  rwa [coe_siegelElt] at this

theorem comm_nB_of_comm_siegel {σ : F ≃+* F} (hσ : ∀ c, σ c = c)
    (A : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (C : Matrix (Fin 2) (Fin 2) F)
    (h : fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
        (1 : Matrix (Fin 2) (Fin 2) F) * A =
      A * (fromBlocks (1 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
        (1 : Matrix (Fin 2) (Fin 2) F)).map σ) :
    A * fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
        (0 : Matrix (Fin 2) (Fin 2) F) =
      fromBlocks (0 : Matrix (Fin 2) (Fin 2) F) C (0 : Matrix (Fin 2) (Fin 2) F)
        (0 : Matrix (Fin 2) (Fin 2) F) * A := by
  have hmap : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, M.map σ = M := fun M => by
    ext i j
    simp [Matrix.map_apply, hσ]
  rw [hmap, siegel_eq_one_add', add_mul, mul_add, Matrix.one_mul, Matrix.mul_one] at h
  exact (add_left_cancel h).symm

theorem comm_levi_of_fix (h4 : (4 : F) ≠ 0) {A : gsp 2 F} {σ : F ≃+* F}
    (hσ : ∀ c, σ c = c)
    (h : conjAut 2 F A (fieldAut 2 F σ (SymplecticFlag.proj 2 F leviElt)) =
      SymplecticFlag.proj 2 F leviElt) :
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        fromBlocks (!![(1 : F), 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0
          (!![(1 : F), 0; -1, 1] : Matrix (Fin 2) (Fin 2) F) =
      fromBlocks (!![(1 : F), 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0
        (!![(1 : F), 0; -1, 1] : Matrix (Fin 2) (Fin 2) F) *
        ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  have hmap : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, M.map σ = M := fun M => by
    ext i j
    simp [Matrix.map_apply, hσ]
  have htr : Matrix.trace (fromBlocks (!![(1 : F), 1; 0, 1] : Matrix (Fin 2) (Fin 2) F) 0 0
      (!![(1 : F), 0; -1, 1] : Matrix (Fin 2) (Fin 2) F)) = 4 := by
    rw [trace_fromBlocks_two]
    simp [Matrix.trace]
    norm_num
  have := comm_of_fix_sp h4 h (by rw [coe_leviElt]; exact htr)
    (by rw [coe_leviElt, hmap]; exact htr)
  rw [coe_leviElt, hmap] at this
  exact this.symm

private theorem sym_e11 : (!![(1 : F), 0; 0, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem sym_e22 : (!![(0 : F), 0; 0, 1] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem sym_sig : (!![(0 : F), 1; 1, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

private theorem sym_c_e11 (c : F) :
    (c • !![(1 : F), 0; 0, 0] : Matrix (Fin 2) (Fin 2) F)ᵀ = c • !![1, 0; 0, 0] := by
  rw [Matrix.transpose_smul, sym_e11]

theorem four_ne_zero_of_charP {r : ℕ} [Fact r.Prime] [CharP F r] (hr2 : r ≠ 2) :
    (4 : F) ≠ 0 := by
  have hodd : ringChar F ≠ 2 := by rwa [ringChar.eq F r]
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hodd
  have : (4 : F) = 2 * 2 := by norm_num
  rw [this]
  exact mul_ne_zero h2 h2

theorem pow_eq_one_of_fix_spRad2 {r : ℕ} [Fact r.Prime] [CharP F r] [Finite F] (hr2 : r ≠ 2)
    (b : MulAut (StatedProj (StatedSp 2 F)))
    (hb : ∀ g ∈ spRad2 F, b (SymplecticFlag.proj 2 F g) = SymplecticFlag.proj 2 F g) :
    b ^ r = 1 := by
  have hodd : ringChar F ≠ 2 := by rwa [ringChar.eq F r]
  have h4 := four_ne_zero_of_charP (F := F) hr2
  obtain ⟨A, σ, hbeq⟩ := psp4_odd_automorphism_normal_form hodd b
  have hfix : ∀ g ∈ spRad2 F, conjAut 2 F A (fieldAut 2 F σ (SymplecticFlag.proj 2 F g)) =
      SymplecticFlag.proj 2 F g := by
    intro g hg
    have := hb g hg
    rwa [hbeq, MulAut.mul_apply] at this
  have hA' : (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 :=
    Units.inv_mul _
  have hσ : ∀ c, σ c = c := sigma_id_of_comm _ _ hA' σ fun c =>
    comm_siegel_of_fix h4 _ (sym_c_e11 c) (hfix _ (siegelElt_mem_spRad2 _ (sym_c_e11 c)))
  have hσ1 : σ = 1 := RingEquiv.ext hσ
  obtain ⟨l, M, hAM, hMM⟩ := nilp_of_comm_two
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (comm_nB_of_comm_siegel hσ _ _
      (comm_siegel_of_fix h4 _ sym_e11 (hfix _ (siegelElt_mem_spRad2 _ sym_e11))))
    (comm_nB_of_comm_siegel hσ _ _
      (comm_siegel_of_fix h4 _ sym_e22 (hfix _ (siegelElt_mem_spRad2 _ sym_e22))))
    (comm_nB_of_comm_siegel hσ _ _
      (comm_siegel_of_fix h4 _ sym_sig (hfix _ (siegelElt_mem_spRad2 _ sym_sig))))
  rw [hbeq, hσ1, map_one, mul_one]
  exact conjAut_pow_eq_one hAM hMM

theorem pow_eq_one_of_fix_spRad1 {r : ℕ} [Fact r.Prime] [CharP F r] [Finite F] (hr2 : r ≠ 2)
    (b : MulAut (StatedProj (StatedSp 2 F)))
    (hb : ∀ g ∈ spRad1 F, b (SymplecticFlag.proj 2 F g) = SymplecticFlag.proj 2 F g) :
    b ^ r = 1 := by
  have hodd : ringChar F ≠ 2 := by rwa [ringChar.eq F r]
  have h4 := four_ne_zero_of_charP (F := F) hr2
  obtain ⟨A, σ, hbeq⟩ := psp4_odd_automorphism_normal_form hodd b
  have hfix : ∀ g ∈ spRad1 F, conjAut 2 F A (fieldAut 2 F σ (SymplecticFlag.proj 2 F g)) =
      SymplecticFlag.proj 2 F g := by
    intro g hg
    have := hb g hg
    rwa [hbeq, MulAut.mul_apply] at this
  have hA' : (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 :=
    Units.inv_mul _
  have h11 : ∀ c : F, (c • !![(1 : F), 0; 0, 0] : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := fun c => by
    simp
  have hσ : ∀ c, σ c = c := sigma_id_of_comm _ _ hA' σ fun c =>
    comm_siegel_of_fix h4 _ (sym_c_e11 c)
      (hfix _ (siegelElt_mem_spRad1 _ (sym_c_e11 c) (h11 c)))
  have hσ1 : σ = 1 := RingEquiv.ext hσ
  obtain ⟨l, M, hAM, hMM⟩ := nilp_of_comm_one
    ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    (comm_nB_of_comm_siegel hσ _ _
      (comm_siegel_of_fix h4 _ sym_e11 (hfix _ (siegelElt_mem_spRad1 _ sym_e11 (by simp)))))
    (comm_nB_of_comm_siegel hσ _ _
      (comm_siegel_of_fix h4 _ sym_sig (hfix _ (siegelElt_mem_spRad1 _ sym_sig (by simp)))))
    (comm_levi_of_fix h4 hσ (hfix _ leviElt_mem_spRad1))
  rw [hbeq, hσ1, map_one, mul_one]
  exact conjAut_pow_eq_one hAM hMM

end Two

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
