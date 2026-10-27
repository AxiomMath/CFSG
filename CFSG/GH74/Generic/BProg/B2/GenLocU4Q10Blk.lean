module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4QFrame2
public import CFSG.GH74.Generic.BProg.B2.GenLocU4QHyp
public import CFSG.GH74.Generic.BProg.B2.GenLocU4GenFrame

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic GenLocU4QLift GenLocU4QClass GenLocU4QHyp CFSG.ClassicalInvolution.Phan
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne CFSG.ClassicalGroups.Unitary

namespace GenLocU4Q10Blk

variable {A : Type} [Group A]

theorem pairSub_rank2 [Finite A] (hA : IsElementaryAbelian 2 A) {e f : A} (he : e * e = 1) (hf : f * f = 1)
    (hef : e * f = f * e) (he1 : e ≠ 1) (hf1 : f ≠ 1) (hef1 : e * f ≠ 1) :
    IsRank23 ↥(GenLocL4Q.pairSub e f he hf hef) ∧ pRank 2 ↥(GenLocL4Q.pairSub e f he hf hef) = 2 := by
  classical
  have hfe : e ≠ f := fun h => hef1 (by rw [h, hf])
  have hn1 : e * f ≠ e := fun h => hf1 (by simpa using h)
  have hn2 : e * f ≠ f := fun h => he1 (by simpa using h)
  have hset : ((GenLocL4Q.pairSub e f he hf hef : Subgroup A) : Set A) = {1, e, f, e * f} := rfl
  have h4 : ({1, e, f, e * f} : Set A).ncard = 4 := by
    have m1 : (1 : A) ∉ ({e, f, e * f} : Set A) := by simp [he1.symm, hf1.symm, hef1.symm]
    have m2 : e ∉ ({f, e * f} : Set A) := by simp [hfe, hn1.symm]
    have m3 : f ∉ ({e * f} : Set A) := by simp [hn2.symm]
    rw [Set.ncard_insert_of_notMem m1, Set.ncard_insert_of_notMem m2, Set.ncard_insert_of_notMem m3,
      Set.ncard_singleton]
  have hcard : Nat.card ↥(GenLocL4Q.pairSub e f he hf hef) = 4 := by
    rw [← h4, ← hset]
    exact (Nat.card_coe_set_eq _).symm ▸ rfl
  have := hA
  have hEA : IsElementaryAbelian 2 ↥(GenLocL4Q.pairSub e f he hf hef) := by
    refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun g => Subtype.ext ?_
    have h2 : ((g : A)) ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) (g : A)
    simpa using h2
  have hpr : pRank 2 ↥(GenLocL4Q.pairSub e f he hf hef) = 2 := by
    have h1 := GenLocBasic.card_eq_two_pow_pRank_type hEA
    rw [hcard] at h1
    exact (Nat.pow_right_injective (le_refl 2) (by simpa using h1.symm : 2 ^ pRank 2 ↥(GenLocL4Q.pairSub e f he hf hef) = 2 ^ 2))
  exact ⟨⟨hEA, Or.inl hpr⟩, hpr⟩

variable {K : Type} [Field K]

@[expose] def bdiag (M M' : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, M' 0 0, M' 0 1; 0, 0, M' 1 0, M' 1 1]

theorem bdiag_mul_blockMat0 (M M' Y Y' : Matrix (Fin 2) (Fin 2) K) (h : M * Y = Y' * M) :
    bdiag M M' * blockMat 4 0 Y = blockMat 4 0 Y' * bdiag M M' := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext a b
  fin_cases a <;> fin_cases b <;> simp [bdiag, blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination e00 | linear_combination e01 | linear_combination e10 | linear_combination e11

theorem bdiag_mul_blockMat2 (M M' Y Y' : Matrix (Fin 2) (Fin 2) K) (h : M' * Y = Y' * M') :
    bdiag M M' * blockMat 4 2 Y = blockMat 4 2 Y' * bdiag M M' := by
  have e00 := congrFun (congrFun h 0) 0
  have e01 := congrFun (congrFun h 0) 1
  have e10 := congrFun (congrFun h 1) 0
  have e11 := congrFun (congrFun h 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ext a b
  fin_cases a <;> fin_cases b <;> simp [bdiag, blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination e00 | linear_combination e01 | linear_combination e10 | linear_combination e11

section Conj

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Fact p.Prime] [CharP K p] in
theorem unitary_block (h : UnitaryFieldData p f K) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : (M.map (· ^ (p ^ f)))ᵀ * M = 1) :
    ∃ Mgl : GL (Fin 2) K, (Mgl : Matrix (Fin 2) (Fin 2) K) = M ∧ Mgl ∈ primeFormUnitary h (idGram K 2) := by
  have hMM' : M * (M.map (· ^ (p ^ f)))ᵀ = 1 := mul_eq_one_comm.mp hM
  refine ⟨⟨M, (M.map (· ^ (p ^ f)))ᵀ, hMM', hM⟩, rfl, ?_⟩
  rw [mem_primeFormUnitary]
  simp only [idGram, Units.val_one, Matrix.mul_one]
  exact hM

theorem exists_su2_conj (h : UnitaryFieldData p f K) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : (M.map (· ^ (p ^ f)))ᵀ * M = 1) (y : Su K p f 2) :
    ∃ y' : Su K p f 2, M * ((y : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      ((y' : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) * M := by
  obtain ⟨Mgl, hMc, hMu⟩ := unitary_block h hM
  have hY : (y : GL (Fin 2) K) ∈ unitarySU p f K 2 := (GenLocU3Blk.suEquiv h 2 y).2
  have hY2 := KFU.conj_mem_unitarySU h hMu hY
  refine ⟨(GenLocU3Blk.suEquiv h 2).symm ⟨Mgl * y * Mgl⁻¹, hY2⟩, ?_⟩
  have e : ((((GenLocU3Blk.suEquiv h 2).symm ⟨Mgl * y * Mgl⁻¹, hY2⟩ : Su K p f 2) : GL (Fin 2) K)) = Mgl * y * Mgl⁻¹ := rfl
  rw [e, ← hMc]
  simp only [Units.val_mul]
  rw [Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]

omit [Finite K] [CharP K p] in
theorem unitary_bdiag {M M' : Matrix (Fin 2) (Fin 2) K}
    (hU : ((bdiag M M').map (· ^ (p ^ f)))ᵀ * bdiag M M' = 1) :
    (M.map (· ^ (p ^ f)))ᵀ * M = 1 ∧ (M'.map (· ^ (p ^ f)))ᵀ * M' = 1 := by
  have hq0 : p ^ f ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have u00 := congrFun (congrFun hU 0) 0
  have u01 := congrFun (congrFun hU 0) 1
  have u10 := congrFun (congrFun hU 1) 0
  have u11 := congrFun (congrFun hU 1) 1
  have v22 := congrFun (congrFun hU 2) 2
  have v23 := congrFun (congrFun hU 2) 3
  have v32 := congrFun (congrFun hU 3) 2
  have v33 := congrFun (congrFun hU 3) 3
  simp [bdiag, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.map_apply, zero_pow hq0] at u00 u01 u10 u11 v22 v23 v32 v33
  constructor
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
    · exact u00
    · exact u01
    · exact u10
    · exact u11
  · ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
    · exact v22
    · exact v23
    · exact v32
    · exact v33

theorem exists_frameBlock_bdiag (hK : Nat.card K = (p ^ f) ^ 2) (P u : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (hu : ((u : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (u : Matrix (Fin 4) (Fin 4) K) = 1)
    {M M' : Matrix (Fin 2) (Fin 2) K} (hD : ((P⁻¹ * u * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = bdiag M M')
    (y : Su K p f 2) :
    (∃ y0 : Su K p f 2, u * (GenLocU4Gen.frameBlock hK P hP 0 y : GL (Fin 4) K) * u⁻¹ =
      (GenLocU4Gen.frameBlock hK P hP 0 y0 : GL (Fin 4) K)) ∧
    (∃ y2 : Su K p f 2, u * (GenLocU4Gen.frameBlock hK P hP 2 y : GL (Fin 4) K) * u⁻¹ =
      (GenLocU4Gen.frameBlock hK P hP 2 y2 : GL (Fin 4) K)) := by
  have hh : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card (Fact.out) hK
  have hDU := GenLocU4QFrame2.unitary_conj hh hP hu
  obtain ⟨D, hDdef⟩ : ∃ D : GL (Fin 4) K, D = P⁻¹ * u * P := ⟨_, rfl⟩
  rw [← hDdef] at hDU hD
  rw [hD] at hDU
  obtain ⟨hM, hM'⟩ := unitary_bdiag hDU
  have conj_form : ∀ (i : Fin 3) (y y' : Su K p f 2),
      D * (blockEmb2 K p f 3 i y : GL (Fin 4) K) = (blockEmb2 K p f 3 i y' : GL (Fin 4) K) * D →
      u * (GenLocU4Gen.frameBlock hK P hP i y : GL (Fin 4) K) * u⁻¹ = (GenLocU4Gen.frameBlock hK P hP i y' : GL (Fin 4) K) := by
    intro i y y' h
    have e1 : u * (GenLocU4Gen.frameBlock hK P hP i y : GL (Fin 4) K) * u⁻¹ =
        P * (D * (blockEmb2 K p f 3 i y : GL (Fin 4) K) * D⁻¹) * P⁻¹ := by
      rw [GenLocU4Gen.coe_frameBlock, hDdef]; group
    rw [e1, h, GenLocU4Gen.coe_frameBlock]
    group
  refine ⟨?_, ?_⟩
  · obtain ⟨y0, hy0⟩ := exists_su2_conj hh hM y
    refine ⟨y0, conj_form 0 y y0 ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, coe_coe_blockEmb2, coe_coe_blockEmb2]
    exact bdiag_mul_blockMat0 M M' _ _ hy0
  · obtain ⟨y2, hy2⟩ := exists_su2_conj hh hM' y
    refine ⟨y2, conj_form 2 y y2 ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, coe_coe_blockEmb2, coe_coe_blockEmb2]
    exact bdiag_mul_blockMat2 M M' _ _ hy2

omit [Finite K] in
theorem shape_of_comm_Dz (h2 : (2 : K) ≠ 0) (Z : Matrix (Fin 4) (Fin 4) K)
    (hz : Matrix.diagonal ![(1 : K), 1, -1, -1] * Z = Z * Matrix.diagonal ![(1 : K), 1, -1, -1]) :
    Z = bdiag !![Z 0 0, Z 0 1; Z 1 0, Z 1 1] !![Z 2 2, Z 2 3; Z 3 2, Z 3 3] := by
  have e : ∀ i j : Fin 4, (![(1 : K), 1, -1, -1] i - ![(1 : K), 1, -1, -1] j) * Z i j = 0 := by
    intro i j
    have := congrFun (congrFun hz i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at this
    linear_combination this
  have h2' : (1 : K) - -1 ≠ 0 := by
    intro h0; apply h2; linear_combination h0
  have h2'' : (-1 : K) - 1 ≠ 0 := by
    intro h0; apply h2; linear_combination -h0
  have z02 : Z 0 2 = 0 := (mul_eq_zero.1 (e 0 2)).resolve_left (by simpa using h2')
  have z03 : Z 0 3 = 0 := (mul_eq_zero.1 (e 0 3)).resolve_left (by simpa using h2')
  have z12 : Z 1 2 = 0 := (mul_eq_zero.1 (e 1 2)).resolve_left (by simpa using h2')
  have z13 : Z 1 3 = 0 := (mul_eq_zero.1 (e 1 3)).resolve_left (by simpa using h2')
  have z20 : Z 2 0 = 0 := (mul_eq_zero.1 (e 2 0)).resolve_left (by simpa using h2'')
  have z21 : Z 2 1 = 0 := (mul_eq_zero.1 (e 2 1)).resolve_left (by simpa using h2'')
  have z30 : Z 3 0 = 0 := (mul_eq_zero.1 (e 3 0)).resolve_left (by simpa using h2'')
  have z31 : Z 3 1 = 0 := (mul_eq_zero.1 (e 3 1)).resolve_left (by simpa using h2'')
  ext i j
  fin_cases i <;> fin_cases j <;> simp [bdiag, z02, z03, z12, z13, z20, z21, z30, z31]

omit [Finite K] in
theorem Dz_comm_blockMat0 (Y : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal ![(1 : K), 1, -1, -1] * blockMat 4 0 Y = blockMat 4 0 Y * Matrix.diagonal ![(1 : K), 1, -1, -1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

omit [Finite K] in
theorem Dz_comm_blockMat2 (Y : Matrix (Fin 2) (Fin 2) K) :
    Matrix.diagonal ![(1 : K), 1, -1, -1] * blockMat 4 2 Y = blockMat 4 2 Y * Matrix.diagonal ![(1 : K), 1, -1, -1] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]

end Conj

theorem lift_gl {p f : ℕ} {A : Type} [Group A] {α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)} {e : A} {u : GL (Fin 4) K}
    (hu : IsLiftU α e u) (g : ↥(StatedSU 4 (p ^ f) K)) : ((α e g : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) = u * g * u⁻¹ :=
  Units.ext (by simpa [Units.val_mul] using hu.2 g)

theorem diag_Dx : (!![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) K) =
    Matrix.diagonal ![-1, 1, -1, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diag_Dz : (!![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] : Matrix (Fin 4) (Fin 4) K) =
    Matrix.diagonal ![1, 1, -1, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem comm_of_fix {p f : ℕ} {A : Type} [Group A] {α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)} {e : A} {u : GL (Fin 4) K}
    (hu : IsLiftU α e u) (g : ↥(StatedSU 4 (p ^ f) K)) (hg : α e g = g) :
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (u : Matrix (Fin 4) (Fin 4) K) =
      (u : Matrix (Fin 4) (Fin 4) K) * ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  have h1 := lift_gl hu g
  rw [hg] at h1
  have h2 : (g : GL (Fin 4) K) * u = u * (g : GL (Fin 4) K) := by
    calc (g : GL (Fin 4) K) * u = (u * (g : GL (Fin 4) K) * u⁻¹) * u := by rw [← h1]
      _ = u * (g : GL (Fin 4) K) := by group
  simpa [Units.val_mul] using congrArg (fun w : GL (Fin 4) K => (w : Matrix (Fin 4) (Fin 4) K)) h2

section MainHelpers

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem frameBlock_comm_z (hK : Nat.card K = (p ^ f) ^ 2) (P z : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (hzP : ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![1, 1, -1, -1])
    (i : Fin 3) (hi : i = 0 ∨ i = 2) (w : Su K p f 2) :
    (GenLocU4Gen.frameBlock hK P hP i w : GL (Fin 4) K) * z = z * (GenLocU4Gen.frameBlock hK P hP i w : GL (Fin 4) K) := by
  have hBD' : ∀ D : GL (Fin 4) K, (D : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![1, 1, -1, -1] →
      ((blockEmb2 K p f 3 i w : Su K p f 4) : GL (Fin 4) K) * D = D * ((blockEmb2 K p f 3 i w : Su K p f 4) : GL (Fin 4) K) := by
    intro D hD
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, coe_coe_blockEmb2]
    rcases hi with rfl | rfl
    · exact (Dz_comm_blockMat0 _).symm
    · exact (Dz_comm_blockMat2 _).symm
  have hBD := hBD' _ hzP
  have e1 : z = P * (P⁻¹ * z * P) * P⁻¹ := by group
  rw [GenLocU4Gen.coe_frameBlock]
  calc P * ((blockEmb2 K p f 3 i w : Su K p f 4) : GL (Fin 4) K) * P⁻¹ * z
      = P * (((blockEmb2 K p f 3 i w : Su K p f 4) : GL (Fin 4) K) * (P⁻¹ * z * P)) * P⁻¹ := by group
    _ = P * ((P⁻¹ * z * P) * ((blockEmb2 K p f 3 i w : Su K p f 4) : GL (Fin 4) K)) * P⁻¹ := by rw [hBD]
    _ = z * (P * ((blockEmb2 K p f 3 i w : Su K p f 4) : GL (Fin 4) K) * P⁻¹) := by group

end MainHelpers

section Main

variable [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem block_le_class10
    (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    {A : Type} [Group A] [Finite A] (α : A →* MulAut ↥(StatedSU 4 (p ^ f) K)) (hA : IsRank23 A) (hr : pRank 2 A = 3)
    {a b c : A} {x y z : GL (Fin 4) K} (hax : IsLiftU α a x) (hby : IsLiftU α b y) (hcz : IsLiftU α c z)
    (hx : (x : Matrix (Fin 4) (Fin 4) K) * x = (1 : K) • 1) (hy : (y : Matrix (Fin 4) (Fin 4) K) * y = (1 : K) • 1)
    (hz : (z : Matrix (Fin 4) (Fin 4) K) * z = (1 : K) • 1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * y = -((y : Matrix (Fin 4) (Fin 4) K) * x))
    (hxz : (x : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * x)
    (hyz : (y : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * y) (hzn : NonScalar z)
    (P : GL (Fin 4) K)
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (hxP : ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1])
    (hzP : ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1])
    (i : Fin 3) (hi : i = 0 ∨ i = 2) (w : Su K p f 2) :
    GenLocU4Gen.frameBlock hK P hP i w ∈ gammaAct α := by
  have h : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have h5 : 5 ≤ p ^ f := GenLocU4ExtCore.five_le_of_mod_four hK hq
  have := hA.1
  have haa : a * a = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 a
  have hbb : b * b = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 b
  have hab : (a * b) * (a * b) = 1 := WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hA.1 (a * b)
  have hcomm : a * b = b * a := mul_comm' a b
  have hyx : (y : Matrix (Fin 4) (Fin 4) K) * x = -((x : Matrix (Fin 4) (Fin 4) K) * y) := by rw [hxy]; simp
  have nx := GenLocL4Q.not_scalar_of_anticomm h2 hxy
  have ny := GenLocL4Q.not_scalar_of_anticomm h2 hyx
  have nxy := GenLocL4Q.not_scalar_of_anticomm h2 (u := x * y) (v := x)
    (by rw [Units.val_mul]; exact GenLocL4Q.W_xy_x hx hy hz hxy hxz hyz)
  have nxz := GenLocL4Q.not_scalar_of_anticomm h2 (u := x * z) (v := y)
    (by rw [Units.val_mul]; exact GenLocL4Q.W_xz_y hx hy hz hxy hxz hyz)
  have nyz := GenLocL4Q.not_scalar_of_anticomm h2 (u := y * z) (v := x)
    (by rw [Units.val_mul]; exact GenLocL4Q.W_yz_x hx hy hz hxy hxz hyz)
  have nxyz := GenLocL4Q.not_scalar_of_anticomm h2 (u := (x * y) * z) (v := x) (by
    rw [Units.val_mul, Units.val_mul]
    have hxy_x := GenLocL4Q.W_xy_x hx hy hz hxy hxz hyz
    calc (x : Matrix (Fin 4) (Fin 4) K) * y * z * x = (x * y) * (z * x) := Matrix.mul_assoc _ _ _
      _ = (x * y) * (x * z) := by rw [← hxz]
      _ = ((x * y) * x) * z := (Matrix.mul_assoc _ _ _).symm
      _ = -(x * (x * y)) * z := by rw [hxy_x]
      _ = -(x * (x * y * z)) := by rw [Matrix.neg_mul, Matrix.mul_assoc])
  have ha1 : a ≠ 1 := hax.ne_one hp hp2 hK nx
  have hb1 : b ≠ 1 := hby.ne_one hp hp2 hK ny
  have hab1 : a * b ≠ 1 := (hax.mul h hby).ne_one hp hp2 hK nxy
  obtain ⟨hH23, hHr⟩ := pairSub_rank2 hA.1 haa hbb hcomm ha1 hb1 hab1
  have hmemH : ∀ e : A, e ∈ GenLocL4Q.pairSub a b haa hbb hcomm → e = 1 ∨ e = a ∨ e = b ∨ e = a * b := by
    intro e he
    simpa [GenLocL4Q.pairSub] using he
  have hone : IsLiftU α (1 : A) (1 : GL (Fin 4) K) := by
    refine ⟨?_, fun g => ?_⟩
    · have : ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := rfl
      rw [this]; exact GenLocU4Basic.isUnitaryU_one (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
    · simp
  have hlift : ∀ e : A, e ∈ GenLocL4Q.pairSub a b haa hbb hcomm → ∃ u : GL (Fin 4) K, IsLiftU α e u ∧
      (u : Matrix (Fin 4) (Fin 4) K) * z = (z : Matrix (Fin 4) (Fin 4) K) * u := by
    intro e he
    rcases hmemH e he with rfl | rfl | rfl | rfl
    · exact ⟨1, hone, by simp⟩
    · exact ⟨x, hax, hxz⟩
    · exact ⟨y, hby, hyz⟩
    · refine ⟨x * y, hax.mul h hby, ?_⟩
      rw [Units.val_mul]
      calc (x : Matrix (Fin 4) (Fin 4) K) * y * z = x * (y * z) := by rw [Matrix.mul_assoc]
        _ = x * (z * y) := by rw [hyz]
        _ = (x * z) * y := by rw [Matrix.mul_assoc]
        _ = z * x * y := by rw [hxz]
        _ = z * (x * y) := by rw [Matrix.mul_assoc]
  have hDz : ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![1, 1, -1, -1] := by
    rw [hzP, diag_Dz]
  let φ := GenLocU4Gen.frameBlock hK P hP i
  have hφinj : Function.Injective φ := GenLocU4Gen.frameBlock_injective hK P hP i
  let α' : ↥(GenLocL4Q.pairSub a b haa hbb hcomm) →* MulAut ↥(StatedSU 4 (p ^ f) K) :=
    α.comp (Subgroup.subtype _)
  have hpres : ∀ (e : ↥(GenLocL4Q.pairSub a b haa hbb hcomm)) (y : Su K p f 2),
      ∃ y' : Su K p f 2, φ y' = α' e (φ y) := by
    intro e y
    obtain ⟨u, hu, huz⟩ := hlift (e : A) e.2
    have hcz' := GenLocU4QFrame.conj_comm_gl P (x := u) (z := z)
      (Units.ext (by simpa [Units.val_mul] using huz))
    obtain ⟨Du, hDu⟩ : ∃ D : GL (Fin 4) K, D = P⁻¹ * u * P := ⟨_, rfl⟩
    obtain ⟨Dz, hDz'⟩ : ∃ D : GL (Fin 4) K, D = P⁻¹ * z * P := ⟨_, rfl⟩
    rw [← hDu, ← hDz'] at hcz'
    rw [← hDz'] at hDz
    have hc := congrArg (fun w : GL (Fin 4) K => (w : Matrix (Fin 4) (Fin 4) K)) hcz'
    simp only [Units.val_mul] at hc
    rw [hDz] at hc
    have hshape := shape_of_comm_Dz h2 (Du : Matrix (Fin 4) (Fin 4) K) hc.symm
    rw [hDu] at hshape
    obtain ⟨⟨y0, hy0⟩, ⟨y2, hy2⟩⟩ := exists_frameBlock_bdiag hK P u hP hu.1 hshape y
    rcases hi with rfl | rfl
    · refine ⟨y0, Subtype.ext ?_⟩
      show (GenLocU4Gen.frameBlock hK P hP 0 y0 : GL (Fin 4) K) = ((α (e : A) (φ y) : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K)
      rw [lift_gl hu, ← hy0]
    · refine ⟨y2, Subtype.ext ?_⟩
      show (GenLocU4Gen.frameBlock hK P hP 2 y2 : GL (Fin 4) K) = ((α (e : A) (φ y) : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K)
      rw [lift_gl hu, ← hy2]
  obtain ⟨β, hβ⟩ := GenLocU3Blk.exists_restrict_action φ hφinj α' hpres
  have ha_mem : a ∈ GenLocL4Q.pairSub a b haa hbb hcomm := by simp [GenLocL4Q.pairSub]
  have hmix : ¬ β.range ≤ (MulAut.conj : Su K p f 2 →* MulAut (Su K p f 2)).range := by
    have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
    have he : ∀ k : Fin 2, (![(-1 : K), 1] k) ^ (p ^ f) * ![(-1 : K), 1] k = 1 := by
      intro k; fin_cases k
      · simp [Odd.neg_pow hodd]
      · simp
    have hne : ∀ lam : K, lam ^ (p ^ f) * lam = 1 → lam * lam ≠ ![(-1 : K), 1] 0 * ![(-1 : K), 1] 1 := by
      intro lam hlam hsq
      apply GenLocU4ExtMu.not_isSqM_neg_one hq h2
      exact ⟨lam, by rw [pow_succ]; exact hlam, by simpa using hsq⟩
    refine GenLocU4Gen.not_range_le_inn_of_block hK hp2 (by omega) (RingEquiv.refl K) (Or.inl rfl)
      ![(-1 : K), 1] he hne β ⟨a, ha_mem⟩ ?_
    intro w'
    have hd0 : ∀ j : Fin 4, (![(-1 : K), 1, -1, 1] : Fin 4 → K) j ≠ 0 := by
      intro j; fin_cases j <;> simp
    have hρ : ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![(-1 : K), 1, -1, 1] := by
      rw [hxP, diag_Dx]
    have hx' : x * (φ w' : GL (Fin 4) K) * x⁻¹ = (φ (β ⟨a, ha_mem⟩ w') : GL (Fin 4) K) := by
      rw [← lift_gl hax (φ w')]
      exact congrArg (fun g : ↥(StatedSU 4 (p ^ f) K) => (g : GL (Fin 4) K)) (hβ ⟨a, ha_mem⟩ w')
    have hmat := GenLocU4Gen.block_action_diag hK P hP i x ![(-1 : K), 1, -1, 1] hd0 hρ w' (β ⟨a, ha_mem⟩ w') hx'
    have hdd : ∀ k : Fin 2, (![(-1 : K), 1, -1, 1] : Fin 4 → K) (GenLocU4Gen.idx4 i k) = ![(-1 : K), 1] k := by
      rcases hi with rfl | rfl <;> (intro k; fin_cases k <;> simp [GenLocU4Gen.idx4])
    simp only [hdd] at hmat
    rw [hmat]
    simp
  have hgam : gammaAct β = ⊤ :=
    GenLocU4Gen.gammaAct_su2_mixed_rank2 hp2 hK h5 hH23 hHr β (Or.inr hmix)
  have hcardH : Nat.card ↥(GenLocL4Q.pairSub a b haa hbb hcomm) = 4 := by
    rw [GenLocBasic.card_eq_two_pow_pRank_type hH23.1, hHr]; norm_num
  have hnontriv : ∀ E : Subgroup ↥(GenLocL4Q.pairSub a b haa hbb hcomm), pRank 2 ↥(GenLocL4Q.pairSub a b haa hbb hcomm) - 1 ≤ pRank 2 ↥E →
      ∃ e ∈ E, e ≠ 1 := by
    intro E hE
    have hidx := (GenLocBasic.adm_iff_index hH23.1 E).1 hE
    by_contra hcon
    push Not at hcon
    have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).2 hcon
    rw [hbot, Subgroup.index_bot, hcardH] at hidx
    omega
  have hle : gammaAct β ≤ (gammaAct α).comap φ := by
    refine iSup₂_le fun E hE w0 hw0 => ?_
    have hw0' := (GenLocBasic.mem_fixedIn_map β E w0).1 hw0
    obtain ⟨e, heE, he1⟩ := hnontriv E hE
    have hfix : α (e : A) (φ w0) = φ w0 := by
      have := hβ e w0
      rw [hw0' e heE] at this
      exact this
    have hgz : (((φ w0 : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) =
        (z : Matrix (Fin 4) (Fin 4) K) * (((φ w0 : ↥(StatedSU 4 (p ^ f) K)) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      have := frameBlock_comm_z hK P z hP (by rw [hzP, diag_Dz]) i hi w0
      simpa [Units.val_mul] using congrArg (fun w : GL (Fin 4) K => (w : Matrix (Fin 4) (Fin 4) K)) this
    show φ w0 ∈ gammaAct α
    rcases hmemH e.1 e.2 with h1 | h1 | h1 | h1
    · exact absurd (Subtype.ext h1) he1
    · rw [h1] at hfix
      exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hax hcz nx hzn nxz _ (comm_of_fix hax _ hfix) hgz
    · rw [h1] at hfix
      exact mem_gammaAct_of_pairU hp hp2 hK α hA hr hby hcz ny hzn nyz _ (comm_of_fix hby _ hfix) hgz
    · rw [h1] at hfix
      exact mem_gammaAct_of_pairU hp hp2 hK α hA hr (hax.mul h hby) hcz nxy hzn nxyz _
        (comm_of_fix (hax.mul h hby) _ hfix) hgz
  exact hle (hgam ▸ Subgroup.mem_top w)

end Main

end GenLocU4Q10Blk

end CFSG.GH74.Generic.BProg.B2
