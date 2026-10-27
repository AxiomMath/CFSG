module

public import CFSG.GH74.Generic.BProg.B2.GenLocU4QFrame

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial Subgroup Matrix
open scoped MatrixGroups

open GenLocU4Basic CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
open CFSG.ClassicalInvolution.Models

namespace GenLocU4QFrame2

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem eigenframe_split (hσ : IsUnitaryInvolution (unitaryInvolution K p f)) (h2 : (2 : K) ≠ 0) {a b c d : K}
    (haa : unitaryInvolution K p f a = a) (hbc : unitaryInvolution K p f b = c) (hd : d = -a)
    (h1 : a * a + b * c = 1) :
    ∃ s t : K, unitaryInvolution K p f s * s + unitaryInvolution K p f t * t = 1 ∧
      a * s + b * t = s ∧ c * s + d * t = t := by
  set σ := unitaryInvolution K p f with hσdef
  by_cases ha1 : a = 1
  · have hbc0 : b * c = 0 := by rw [ha1] at h1; linear_combination h1
    have hb : σ b * b = 0 := by rw [hbc]; linear_combination hbc0
    have hb0 : b = 0 := by
      rcases mul_eq_zero.1 hb with h | h
      · exact (map_eq_zero_iff σ σ.injective |>.1 h)
      · exact h
    have hc0 : c = 0 := by rw [← hbc, hb0, map_zero]
    refine ⟨1, 0, by simp, ?_, ?_⟩
    · rw [ha1]; ring
    · rw [hc0]; ring
  · have hne : (2 : K) * (1 - a) ≠ 0 := mul_ne_zero h2 (sub_ne_zero.2 (Ne.symm ha1))
    have hfix : σ ((2 * (1 - a))⁻¹) = (2 * (1 - a))⁻¹ := by
      rw [map_inv₀, map_mul, map_sub, map_one, haa, map_ofNat]
    obtain ⟨l, hl⟩ := hσ.exists_norm hfix
    have hNv : σ b * b + σ (1 - a) * (1 - a) = 2 * (1 - a) := by
      rw [hbc, map_sub, map_one, haa]; linear_combination h1
    refine ⟨l * b, l * (1 - a), ?_, ?_, ?_⟩
    · have : σ (l * b) * (l * b) + σ (l * (1 - a)) * (l * (1 - a)) = σ l * l * (σ b * b + σ (1 - a) * (1 - a)) := by
        simp only [map_mul]; ring
      rw [this, hNv, hl]; field_simp
    · ring
    · rw [hd]; linear_combination l * h1

theorem block_rel_split {a b c d : K}
    (hZ2 : (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) *
      !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] = 1)
    (hZU : ((!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] = 1)
    (hns : ¬ ∃ l : K, (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) = l • 1) :
    unitaryInvolution K p f a = a ∧ unitaryInvolution K p f b = c ∧ d = -a ∧ a * a + b * c = 1 := by
  have hH := left_inv_eq_right_inv hZU hZ2
  have e00 := congrFun (congrFun hZ2 0) 0
  have e01 := congrFun (congrFun hZ2 0) 1
  have e10 := congrFun (congrFun hZ2 1) 0
  have e11 := congrFun (congrFun hZ2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e10 e11
  have h00 := congrFun (congrFun hH 0) 0
  have h10 := congrFun (congrFun hH 0) 1
  have h01 := congrFun (congrFun hH 1) 0
  simp [Matrix.transpose_apply, Matrix.map_apply] at h00 h10 h01
  have hd : d = -a := by
    by_contra hne
    have hs : a + d ≠ 0 := fun h0 => hne (by linear_combination h0)
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    have haa : a * a = 1 := by rw [hb] at e00; linear_combination e00
    have hdd : d * d = 1 := by rw [hc] at e11; linear_combination e11
    have had : a = d := by
      have : (a - d) * (a + d) = 0 := by linear_combination haa - hdd
      have := (mul_eq_zero.1 this).resolve_right hs
      linear_combination this
    apply hns
    refine ⟨a, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
  refine ⟨by rw [unitaryInvolution_apply K p f]; exact h00, ?_, hd, e00⟩
  rw [unitaryInvolution_apply K p f]
  exact h01

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem raw_of_mem {h : UnitaryFieldData p f K} {g : GL (Fin 4) K} (hg : g ∈ primeFormUnitary h (idGram K 4)) :
    ((g : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (g : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have := mem_primeFormUnitary.1 hg
  have hb : ((g : Matrix (Fin 4) (Fin 4) K).map h.bar) = ((g : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f))) := rfl
  rw [hb] at this
  simpa [idGram] using this

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem unitary_conj (h : UnitaryFieldData p f K) {P z : GL (Fin 4) K}
    (hP : ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1)
    (hz : ((z : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (z : Matrix (Fin 4) (Fin 4) K) = 1) :
    (((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have hP' := GenLocU4Gen.mem_primeFormUnitary_of_raw h hP
  have hz' := GenLocU4Gen.mem_primeFormUnitary_of_raw h hz
  exact raw_of_mem (mul_mem (mul_mem (inv_mem hP') hz') hP')

@[expose] def Rmat (σ : K ≃+* K) (s t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![s, 0, -σ t, 0; t, 0, σ s, 0; 0, s, 0, -σ t; 0, t, 0, σ s]

@[expose] def Rbar (s t : K) (σ : K ≃+* K) : Matrix (Fin 4) (Fin 4) K :=
  !![σ s, σ t, 0, 0; 0, 0, σ s, σ t; -t, s, 0, 0; 0, 0, -t, s]

omit [Finite K] in
theorem Rbar_mul_Rmat (σ : K ≃+* K) {s t : K} (hst : σ s * s + σ t * t = 1) :
    Rbar s t σ * Rmat σ s t = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rbar, Rmat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | linear_combination hst | ring

omit [Finite K] in
theorem Rmat_mul_Rbar (σ : K ≃+* K) {s t : K} (hst : σ s * s + σ t * t = 1) :
    Rmat σ s t * Rbar s t σ = 1 :=
  mul_eq_one_comm.mp (Rbar_mul_Rmat σ hst)

omit [Finite K] in
theorem Rmat_bar (σ : K ≃+* K) {s t : K} (hσσ : ∀ x, σ (σ x) = x) :
    ((Rmat σ s t).map σ)ᵀ = Rbar s t σ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Rbar, Rmat, Matrix.map_apply, hσσ]

theorem frame10 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (x y z : GL (Fin 4) K)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hyU : ((y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (y : Matrix (Fin 4) (Fin 4) K) = 1)
    (hzU : ((z : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (z : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hz2 : z * z = 1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) =
      -((y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K)))
    (hxz : (x : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) =
      (z : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K))
    (hyz : (y : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) =
      (z : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K))
    (hzn : ¬ ∃ l : K, (z : Matrix (Fin 4) (Fin 4) K) = l • 1) :
    ∃ P : GL (Fin 4) K, ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, 1] ∧
      ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] ∧
      ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1] := by
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hh : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  obtain ⟨P, hP, hxP, hyP, a, b, c, d, hzP⟩ :=
    GenLocU4QFrame.exists_triple_frame hp hp2 hK x y z hxU hyU hx2 hy2 hxy hxz hyz
  have hzP2 : (P⁻¹ * z * P) * (P⁻¹ * z * P) = 1 := by
    calc (P⁻¹ * z * P) * (P⁻¹ * z * P) = P⁻¹ * (z * z) * P := by group
      _ = 1 := by rw [hz2]; group
  have hZ2 : (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) *
      !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] = 1 := by
    rw [← hzP, ← Units.val_mul, hzP2, Units.val_one]
  have hZU : ((!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] = 1 := by
    rw [← hzP]; exact unitary_conj hh hP hzU
  have hZn : ¬ ∃ l : K, (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) = l • 1 := by
    rintro ⟨l, hl⟩
    apply hzn
    refine ⟨l, ?_⟩
    have e : z = P * (P⁻¹ * z * P) * P⁻¹ := by group
    have e' : (z : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) *
        ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      conv_lhs => rw [e]
      simp only [Units.val_mul]
    rw [e', hzP, hl, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨haa, hbc, hd, h1⟩ := block_rel_split hZ2 hZU hZn
  obtain ⟨s, t, hst, e1, e2⟩ := eigenframe_split hσ h2 haa hbc hd h1
  subst hd
  set σ := unitaryInvolution K p f with hσdef
  have hσσ : ∀ x : K, σ (σ x) = x := hσ.invol
  have hσc : σ c = b := by rw [← hbc]; exact hσσ b
  have hσd : σ (-a) = -a := by rw [map_neg, haa]
  have E1' : a * σ s + c * σ t = σ s := by
    have := congrArg σ e1
    simpa [map_add, map_mul, haa, hbc] using this
  have E2' : b * σ s + -a * σ t = σ t := by
    have := congrArg σ e2
    simpa [map_add, map_mul, hσc, haa, map_neg] using this
  let Rgl : GL (Fin 4) K := ⟨Rmat σ s t, Rbar s t σ, Rmat_mul_Rbar σ hst, Rbar_mul_Rmat σ hst⟩
  have hRc : (Rgl : Matrix (Fin 4) (Fin 4) K) = Rmat σ s t := rfl
  have hRi : ((Rgl⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Rbar s t σ := rfl
  have hRU : (((Rgl : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      (Rgl : GL (Fin 4) K) = 1 := by
    have hfun : (fun x : K => x ^ (p ^ f)) = σ := funext fun x => (unitaryInvolution_apply K p f x).symm
    rw [hRc, hfun]
    show ((Rmat σ s t).map σ)ᵀ * Rmat σ s t = 1
    rw [Rmat_bar σ hσσ]
    exact Rbar_mul_Rmat σ hst
  have conj_of_comm : ∀ {M D : Matrix (Fin 4) (Fin 4) K}, M * Rmat σ s t = Rmat σ s t * D →
      Rbar s t σ * M * Rmat σ s t = D := by
    intro M D h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Rbar_mul_Rmat σ hst, Matrix.one_mul]
  refine ⟨P * Rgl, GenLocU4QLift.isUnitaryU_mul hh hP hRU, ?_, ?_, ?_⟩
  · have e : (P * Rgl)⁻¹ * x * (P * Rgl) = Rgl⁻¹ * (P⁻¹ * x * P) * Rgl := by group
    rw [e, Units.val_mul, Units.val_mul, hxP, hRc, hRi, GenLocU4QFrame.diag_X0]
    refine conj_of_comm ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rmat, Matrix.mul_apply, Fin.sum_univ_four]
  · have e : (P * Rgl)⁻¹ * y * (P * Rgl) = Rgl⁻¹ * (P⁻¹ * y * P) * Rgl := by group
    rw [e, Units.val_mul, Units.val_mul, hyP, hRc, hRi]
    refine conj_of_comm ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rmat, Matrix.mul_apply, Fin.sum_univ_four]
  · have e : (P * Rgl)⁻¹ * z * (P * Rgl) = Rgl⁻¹ * (P⁻¹ * z * P) * Rgl := by group
    rw [e, Units.val_mul, Units.val_mul, hzP, hRc, hRi]
    refine conj_of_comm ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Rmat, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals first | linear_combination e1 | linear_combination e2 | linear_combination E1' | linear_combination E2' | linear_combination (-1 : K) * E1'

omit [Finite K] [Fact p.Prime] [CharP K p] in
theorem block_rel_nsplit {a b c d : K}
    (hZ2 : (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) *
      !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] = -1)
    (hZU : ((!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] = 1)
    (hns : ¬ ∃ l : K, (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) = l • 1) :
    a ^ (p ^ f) = -a ∧ c ^ (p ^ f) = -b ∧ b ^ (p ^ f) = -c ∧ d = -a ∧ a * a + b * c = -1 := by
  have hZ2' : (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) *
      -(!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d]) = 1 := by
    rw [Matrix.mul_neg, hZ2, neg_neg]
  have hH := left_inv_eq_right_inv hZU hZ2'
  have e00 := congrFun (congrFun hZ2 0) 0
  have e01 := congrFun (congrFun hZ2 0) 1
  have e10 := congrFun (congrFun hZ2 1) 0
  have e11 := congrFun (congrFun hZ2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e00 e01 e10 e11
  have h00 := congrFun (congrFun hH 0) 0
  have h10 := congrFun (congrFun hH 0) 1
  have h01 := congrFun (congrFun hH 1) 0
  simp [Matrix.transpose_apply, Matrix.map_apply] at h00 h10 h01
  have hd : d = -a := by
    by_contra hne
    have hs : a + d ≠ 0 := fun h0 => hne (by linear_combination h0)
    have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e01
      exact (mul_eq_zero.1 this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e10
      exact (mul_eq_zero.1 this).resolve_right hs
    have haa : a * a = -1 := by rw [hb] at e00; linear_combination e00
    have hdd : d * d = -1 := by rw [hc] at e11; linear_combination e11
    have had : a = d := by
      have : (a - d) * (a + d) = 0 := by linear_combination haa - hdd
      have := (mul_eq_zero.1 this).resolve_right hs
      linear_combination this
    apply hns
    refine ⟨a, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hb, hc, had]
  exact ⟨h00, h10, h01, hd, e00⟩

@[expose] def Qmat (s t u v : K) : Matrix (Fin 4) (Fin 4) K :=
  !![s, u, 0, 0; t, v, 0, 0; 0, 0, s, u; 0, 0, t, v]

@[expose] def Qbar (σ : K ≃+* K) (s t u v : K) : Matrix (Fin 4) (Fin 4) K :=
  !![σ s, σ t, 0, 0; σ u, σ v, 0, 0; 0, 0, σ s, σ t; 0, 0, σ u, σ v]

omit [Finite K] in
theorem Qbar_mul_Qmat (σ : K ≃+* K) {s t u v : K} (R1 : σ s * s + σ t * t = 1) (R2 : σ u * u + σ v * v = 1)
    (R3 : σ s * u + σ t * v = 0) (R3' : σ u * s + σ v * t = 0) : Qbar σ s t u v * Qmat s t u v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qbar, Qmat, Matrix.mul_apply, Fin.sum_univ_four] <;>
    first | exact R1 | exact R2 | exact R3 | exact R3'

omit [Finite K] in
theorem Qmat_mul_Qbar (σ : K ≃+* K) {s t u v : K} (R1 : σ s * s + σ t * t = 1) (R2 : σ u * u + σ v * v = 1)
    (R3 : σ s * u + σ t * v = 0) (R3' : σ u * s + σ v * t = 0) : Qmat s t u v * Qbar σ s t u v = 1 :=
  mul_eq_one_comm.mp (Qbar_mul_Qmat σ R1 R2 R3 R3')

omit [Finite K] in
theorem Qmat_bar (σ : K ≃+* K) {s t u v : K} : ((Qmat s t u v).map σ)ᵀ = Qbar σ s t u v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Qbar, Qmat, Matrix.map_apply]

theorem frame11 (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 4 = 1)
    (x y z : GL (Fin 4) K)
    (hxU : ((x : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (x : Matrix (Fin 4) (Fin 4) K) = 1)
    (hyU : ((y : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (y : Matrix (Fin 4) (Fin 4) K) = 1)
    (hzU : ((z : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (z : Matrix (Fin 4) (Fin 4) K) = 1)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hz2 : (z * z : GL (Fin 4) K) = -1)
    (hxy : (x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K) =
      -((y : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K)))
    (hxz : (x : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) =
      (z : Matrix (Fin 4) (Fin 4) K) * (x : Matrix (Fin 4) (Fin 4) K))
    (hyz : (y : Matrix (Fin 4) (Fin 4) K) * (z : Matrix (Fin 4) (Fin 4) K) =
      (z : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K))
    (hzn : ¬ ∃ l : K, (z : Matrix (Fin 4) (Fin 4) K) = l • 1) :
    ∃ P : GL (Fin 4) K, ((P : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (P : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      ((P⁻¹ * x * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal ![-1, -1, 1, 1] ∧
      ((P⁻¹ * y * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0] ∧
      ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        !![0, 1, 0, 0; -1, 0, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0] := by
  have h2 : (2 : K) ≠ 0 := GenLocU4ExtFrame.two_ne_zero_of_card hp hp2 hK
  have hh : UnitaryFieldData p f K := GenLocDiagU.unitaryFieldData_of_card hp hK
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  obtain ⟨P, hP, hxP, hyP, a, b, c, d, hzP⟩ :=
    GenLocU4QFrame.exists_triple_frame hp hp2 hK x y z hxU hyU hx2 hy2 hxy hxz hyz
  have hzP2 : (P⁻¹ * z * P) * (P⁻¹ * z * P) = -1 := by
    calc (P⁻¹ * z * P) * (P⁻¹ * z * P) = P⁻¹ * (z * z) * P := by group
      _ = -1 := by
        rw [hz2]
        apply Units.ext
        simp
  have hZ2 : (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) *
      !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] = -1 := by
    rw [← hzP, ← Units.val_mul, hzP2, Units.val_neg, Units.val_one]
  have hZU : ((!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ *
      !![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] = 1 := by
    rw [← hzP]; exact unitary_conj hh hP hzU
  have hZn : ¬ ∃ l : K, (!![a, b, 0, 0; c, d, 0, 0; 0, 0, a, b; 0, 0, c, d] : Matrix (Fin 4) (Fin 4) K) = l • 1 := by
    rintro ⟨l, hl⟩
    apply hzn
    refine ⟨l, ?_⟩
    have e : z = P * (P⁻¹ * z * P) * P⁻¹ := by group
    have e' : (z : Matrix (Fin 4) (Fin 4) K) = (P : Matrix (Fin 4) (Fin 4) K) *
        ((P⁻¹ * z * P : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) * ((P⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
      conv_lhs => rw [e]
      simp only [Units.val_mul]
    rw [e', hzP, hl, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  obtain ⟨ha, hc, hb, hd, h1⟩ := block_rel_nsplit hZ2 hZU hZn
  subst hd
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have hna : (-a) ^ (p ^ f) = a := by rw [Odd.neg_pow hodd, ha, neg_neg]
  have u00 := congrFun (congrFun hZU 0) 0
  have u01 := congrFun (congrFun hZU 0) 1
  have u10 := congrFun (congrFun hZU 1) 0
  have u11 := congrFun (congrFun hZU 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply, Matrix.map_apply] at u00 u01 u10 u11
  have hdet : (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination (-1 : K) * h1
  have hunit : ((!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) K).map (· ^ (p ^ f)))ᵀ * !![a, b; c, -a] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply, hna]
    · exact u00
    · exact u01
    · rw [hna] at u10; exact u10
    · rw [hna] at u11; exact u11
  let B : Su K p f 2 := GenLocU4Aux.su2Mk (p := p) (f := f) (!![a, b; c, -a]) hdet hunit
  have hB : suMat B * suMat B = -1 := by
    show (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) K) * !![a, b; c, -a] = -1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> first | linear_combination h1 | linear_combination (-1 : K) * h1 | ring
  obtain ⟨ι, hι, -⟩ := GenLocU4Su.exists_sqrt_neg_one hK hp2
  have hσι : unitaryInvolution K p f ι = ι := by
    rw [unitaryInvolution_apply K p f]; exact GenLocU4ExtBd.pow_eq_self_of_sq_neg_one hq hι
  obtain ⟨fp, fm, hfp, hfm, nfp, nfm, hcross⟩ := GenLocU4Su.exists_witt_pair h2 hι hσι B hB
  set σ := unitaryInvolution K p f with hσdef
  have hσσ : ∀ x : K, σ (σ x) = x := hσ.invol
  have hfp' : (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) K) *ᵥ fp = ι • fp := hfp
  have hfm' : (!![a, b; c, -a] : Matrix (Fin 2) (Fin 2) K) *ᵥ fm = (-ι) • fm := hfm
  have p0 := congrFun hfp' 0
  have p1 := congrFun hfp' 1
  have m0 := congrFun hfm' 0
  have m1 := congrFun hfm' 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at p0 p1 m0 m1
  have hcross' : σ (fm 0) * fp 0 + σ (fm 1) * fp 1 = 1 := by
    have := congrArg σ hcross
    simp only [map_add, map_mul, hσσ, map_one] at this
    linear_combination this
  have hfix2 : σ ((2 : K)⁻¹) = (2 : K)⁻¹ := by rw [map_inv₀, map_ofNat]
  obtain ⟨lam, hlam⟩ := hσ.exists_norm hfix2
  have hinv2 : (2 : K) * (2 : K)⁻¹ = 1 := mul_inv_cancel₀ h2
  obtain ⟨s, hs⟩ : ∃ s : K, s = lam * (fp 0 + fm 0) := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ t : K, t = lam * (fp 1 + fm 1) := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : K, u = -ι * lam * (fp 0 - fm 0) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : K, v = -ι * lam * (fp 1 - fm 1) := ⟨_, rfl⟩
  have R1 : σ s * s + σ t * t = 1 := by
    rw [hs, ht]; simp only [map_mul, map_add]
    linear_combination (σ lam * lam) * nfp + (σ lam * lam) * nfm + (σ lam * lam) * hcross +
      (σ lam * lam) * hcross' + 2 * hlam + hinv2
  have R2 : σ u * u + σ v * v = 1 := by
    rw [hu, hv]; simp only [map_mul, map_sub, map_neg, hσι]
    linear_combination ((σ lam * lam) * ((σ (fp 0) - σ (fm 0)) * (fp 0 - fm 0) +
      (σ (fp 1) - σ (fm 1)) * (fp 1 - fm 1))) * hι - (σ lam * lam) * nfp - (σ lam * lam) * nfm +
      (σ lam * lam) * hcross + (σ lam * lam) * hcross' + 2 * hlam + hinv2
  have R3 : σ s * u + σ t * v = 0 := by
    rw [hs, ht, hu, hv]; simp only [map_mul, map_add]
    linear_combination (-ι * (σ lam * lam)) * (nfp - hcross + hcross' - nfm)
  have R3' : σ u * s + σ v * t = 0 := by
    have := congrArg σ R3
    simp only [map_add, map_mul, hσσ, map_zero] at this
    linear_combination this
  have Z1 : a * s + b * t = -u := by
    rw [hs, ht, hu]; linear_combination lam * p0 + lam * m0
  have Z2 : c * s + -a * t = -v := by
    rw [hs, ht, hv]; linear_combination lam * p1 + lam * m1
  have Z3 : a * u + b * v = s := by
    rw [hs, hu, hv]
    linear_combination (-(lam * (fp 0 + fm 0))) * hι - (ι * lam) * p0 + (ι * lam) * m0
  have Z4' : c * u + -a * v = t := by
    rw [ht, hu, hv]
    linear_combination (-(lam * (fp 1 + fm 1))) * hι - (ι * lam) * p1 + (ι * lam) * m1
  let Qgl : GL (Fin 4) K := ⟨Qmat s t u v, Qbar σ s t u v, Qmat_mul_Qbar σ R1 R2 R3 R3', Qbar_mul_Qmat σ R1 R2 R3 R3'⟩
  have hQc : (Qgl : Matrix (Fin 4) (Fin 4) K) = Qmat s t u v := rfl
  have hQi : ((Qgl⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = Qbar σ s t u v := rfl
  have hQU : (((Qgl : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ (p ^ f)))ᵀ * (Qgl : GL (Fin 4) K) = 1 := by
    have hfun : (fun x : K => x ^ (p ^ f)) = σ := funext fun x => (unitaryInvolution_apply K p f x).symm
    rw [hQc, hfun]
    show ((Qmat s t u v).map σ)ᵀ * Qmat s t u v = 1
    rw [Qmat_bar σ]
    exact Qbar_mul_Qmat σ R1 R2 R3 R3'
  have conj_of_comm : ∀ {M D : Matrix (Fin 4) (Fin 4) K}, M * Qmat s t u v = Qmat s t u v * D →
      Qbar σ s t u v * M * Qmat s t u v = D := by
    intro M D h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, Qbar_mul_Qmat σ R1 R2 R3 R3', Matrix.one_mul]
  refine ⟨P * Qgl, GenLocU4QLift.isUnitaryU_mul hh hP hQU, ?_, ?_, ?_⟩
  · have e : (P * Qgl)⁻¹ * x * (P * Qgl) = Qgl⁻¹ * (P⁻¹ * x * P) * Qgl := by group
    rw [e, Units.val_mul, Units.val_mul, hxP, hQc, hQi]
    refine conj_of_comm ?_
    rw [GenLocU4QFrame.diag_X0]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Qmat, Matrix.mul_apply, Fin.sum_univ_four]
  · have e : (P * Qgl)⁻¹ * y * (P * Qgl) = Qgl⁻¹ * (P⁻¹ * y * P) * Qgl := by group
    rw [e, Units.val_mul, Units.val_mul, hyP, hQc, hQi]
    refine conj_of_comm ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Qmat, Matrix.mul_apply, Fin.sum_univ_four]
  · have e : (P * Qgl)⁻¹ * z * (P * Qgl) = Qgl⁻¹ * (P⁻¹ * z * P) * Qgl := by group
    rw [e, Units.val_mul, Units.val_mul, hzP, hQc, hQi]
    refine conj_of_comm ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Qmat, Matrix.mul_apply, Fin.sum_univ_four]
    all_goals first | exact Z1 | exact Z2 | exact Z3 | exact Z4' | linear_combination Z1 | linear_combination Z2 | linear_combination Z3 | linear_combination Z4'

end GenLocU4QFrame2

end CFSG.GH74.Generic.BProg.B2
