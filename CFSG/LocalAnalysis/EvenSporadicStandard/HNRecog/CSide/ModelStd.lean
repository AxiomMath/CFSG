module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.CSide.ModelIota
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Aschbacher.Swap.Structure
public import Mathlib.Tactic.ENatToNat

@[expose] public section

namespace CFSG.EvenSporadicStandard.HNRecog.CSide

open Module Matrix CFSG.EvenSporadicStandard.HNRecog.Fpf

theorem sigma0_injective : Function.Injective sigma0 := by
  refine (injective_iff_map_eq_one sigma0).mpr ?_
  intro g hg
  set a : SL2 := iota g.1 with ha_def
  set b : SL2 := iota g.2 with hb_def
  have hM : ∀ M : V0,
      (a : Matrix (Fin 2) (Fin 2) F4) * M * ((b : Matrix (Fin 2) (Fin 2) F4))ᵀ = M := by
    intro M
    have h := congrArg (fun e : V0 ≃ₗ[ZMod 2] V0 => e M) hg
    rw [sigma0_apply] at h
    rw [← ha_def, ← hb_def] at h
    simpa [actFun] using h
  have hABmat : (a : Matrix (Fin 2) (Fin 2) F4) * ((b : Matrix (Fin 2) (Fin 2) F4))ᵀ = 1 := by
    simpa using hM 1
  have hAB : a * Matrix.SpecialLinearGroup.transpose b = 1 :=
    Subtype.ext (by
      simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
        Matrix.SpecialLinearGroup.coe_one] using hABmat)
  have hbTa : (Matrix.SpecialLinearGroup.transpose b) * a = 1 := by
    rw [eq_inv_of_mul_eq_one_right hAB]
    exact inv_mul_cancel a
  have hcomm : ∀ M : V0,
      (a : Matrix (Fin 2) (Fin 2) F4) * M = M * (a : Matrix (Fin 2) (Fin 2) F4) := by
    intro M
    have h := congrArg (fun N : V0 => N * (a : Matrix (Fin 2) (Fin 2) F4)) (hM M)
    have hbTa' : ((b : Matrix (Fin 2) (Fin 2) F4))ᵀ * (a : Matrix (Fin 2) (Fin 2) F4) = 1 := by
      have := congrArg (fun x : SL2 => (x : Matrix (Fin 2) (Fin 2) F4)) hbTa
      simpa [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_transpose,
        Matrix.SpecialLinearGroup.coe_one] using this
    simp only [Matrix.mul_assoc] at h
    rw [hbTa', Matrix.mul_one] at h
    exact h
  have h10 : (a : Matrix (Fin 2) (Fin 2) F4) 1 0 = 0 := by
    have h := congrFun (congrFun (hcomm (Matrix.single 0 1 1)) 1) 1
    simpa using h
  have h01 : (a : Matrix (Fin 2) (Fin 2) F4) 0 1 = 0 := by
    have h := congrFun (congrFun (hcomm (Matrix.single 1 0 1)) 0) 0
    simpa using h
  have h00 : (a : Matrix (Fin 2) (Fin 2) F4) 0 0 = (a : Matrix (Fin 2) (Fin 2) F4) 1 1 := by
    have h := congrFun (congrFun (hcomm (Matrix.single 0 1 1)) 0) 1
    simpa using h
  have hA : (a : Matrix (Fin 2) (Fin 2) F4) =
      Matrix.scalar (Fin 2) ((a : Matrix (Fin 2) (Fin 2) F4) 0 0) := by
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.scalar_apply, Matrix.diagonal_apply, h01, h10, h00]
  have hdet : (a : Matrix (Fin 2) (Fin 2) F4) 0 0 * (a : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 := by
    have h1 : (Matrix.scalar (Fin 2) ((a : Matrix (Fin 2) (Fin 2) F4) 0 0)).det = 1 := by
      rw [← hA]
      exact Matrix.SpecialLinearGroup.det_coe a
    rw [Matrix.det_fin_two] at h1
    simpa [Matrix.scalar_apply, Matrix.diagonal_apply] using h1
  have hfac : ∀ x : F4, x * x = 1 → x = 1 := by decide
  have hr : (a : Matrix (Fin 2) (Fin 2) F4) 0 0 = 1 := hfac _ hdet
  have hA1 : (a : Matrix (Fin 2) (Fin 2) F4) = 1 := by
    rw [hA, hr]
    exact map_one (Matrix.scalar (Fin 2) : F4 →+* Matrix (Fin 2) (Fin 2) F4)
  have ha1 : a = 1 := Subtype.ext (by simpa [Matrix.SpecialLinearGroup.coe_one] using hA1)
  have hbT : Matrix.SpecialLinearGroup.transpose b = 1 := by
    rw [ha1, one_mul] at hAB
    exact hAB
  have hb1 : b = 1 := by
    apply Subtype.ext
    have hbTmat : ((b : Matrix (Fin 2) (Fin 2) F4))ᵀ = (1 : Matrix (Fin 2) (Fin 2) F4) := by
      have := congrArg (fun x : SL2 => (x : Matrix (Fin 2) (Fin 2) F4)) hbT
      simpa [Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_transpose] using this
    simpa using (Matrix.transpose_eq_one.mp hbTmat)
  have hg1 : g.1 = 1 := iota.injective (by rw [← ha_def, ha1, map_one])
  have hg2 : g.2 = 1 := iota.injective (by rw [← hb_def, hb1, map_one])
  exact Prod.ext hg1 hg2

theorem finrank_V0 : finrank (ZMod 2) V0 = 8 := by
  have hF4 : Fintype.card F4 = 4 := by
    rw [← Nat.card_eq_fintype_card, F4.card_eq]
  have hcard : Fintype.card V0 = 2 ^ 8 := by
    show Fintype.card (Fin 2 → Fin 2 → F4) = 2 ^ 8
    rw [Fintype.card_fun, Fintype.card_fun, hF4]
    norm_num
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := V0)
  rw [hcard, ZMod.card 2] at h
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h.symm

theorem sigma0_irreducible : ∀ U : Submodule (ZMod 2) V0,
    (∀ g : A5 × A5, ∀ u ∈ U, sigma0 g u ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  by_cases hbot : U = ⊥
  · exact Or.inl hbot
  right
  have hleftSL : ∀ (A : SL2) (N : V0), N ∈ U →
      (A : Matrix (Fin 2) (Fin 2) F4) * N ∈ U := by
    intro A N hN
    have h := hU (iota.symm A, 1) N hN
    rw [sigma0_apply] at h
    rw [MulEquiv.apply_symm_apply, map_one] at h
    simpa [actFun, Matrix.SpecialLinearGroup.coe_one] using h
  have hrightSL : ∀ (B : SL2) (N : V0), N ∈ U →
      N * (B : Matrix (Fin 2) (Fin 2) F4) ∈ U := by
    intro B N hN
    have h := hU (1, iota.symm (Matrix.SpecialLinearGroup.transpose B)) N hN
    rw [sigma0_apply] at h
    rw [MulEquiv.apply_symm_apply, map_one] at h
    simpa [actFun, Matrix.SpecialLinearGroup.coe_one, Matrix.SpecialLinearGroup.coe_transpose,
      Matrix.transpose_transpose, Matrix.one_mul] using h
  have hL01 : ∀ (t : F4) (N : V0), N ∈ U →
      Matrix.single (0 : Fin 2) (1 : Fin 2) t * N ∈ U := by
    intro t N hN
    have h1 := hleftSL (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
      (j := (1 : Fin 2)) (by decide) t) N hN
    have h2 := Submodule.sub_mem U h1 hN
    have hXN : ((Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := (1 : Fin 2))
        (by decide) t : SL2) : Matrix (Fin 2) (Fin 2) F4) * N - N =
        Matrix.single (0 : Fin 2) (1 : Fin 2) t * N := by
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mul, Matrix.one_mul]
      abel
    rwa [hXN] at h2
  have hL10 : ∀ (t : F4) (N : V0), N ∈ U →
      Matrix.single (1 : Fin 2) (0 : Fin 2) t * N ∈ U := by
    intro t N hN
    have h1 := hleftSL (Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
      (j := (0 : Fin 2)) (by decide) t) N hN
    have h2 := Submodule.sub_mem U h1 hN
    have hXN : ((Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := (0 : Fin 2))
        (by decide) t : SL2) : Matrix (Fin 2) (Fin 2) F4) * N - N =
        Matrix.single (1 : Fin 2) (0 : Fin 2) t * N := by
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.add_mul, Matrix.one_mul]
      abel
    rwa [hXN] at h2
  have hR01 : ∀ (t : F4) (N : V0), N ∈ U →
      N * Matrix.single (0 : Fin 2) (1 : Fin 2) t ∈ U := by
    intro t N hN
    have h1 : N * ((Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
        (j := (1 : Fin 2)) (by decide) t : SL2) : Matrix (Fin 2) (Fin 2) F4) ∈ U :=
      hrightSL _ N hN
    have h2 := Submodule.sub_mem U h1 hN
    have hXN : N * ((Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2))
        (j := (1 : Fin 2)) (by decide) t : SL2) : Matrix (Fin 2) (Fin 2) F4) - N =
        N * Matrix.single (0 : Fin 2) (1 : Fin 2) t := by
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.mul_one]
      abel
    rwa [hXN] at h2
  have hR10 : ∀ (t : F4) (N : V0), N ∈ U →
      N * Matrix.single (1 : Fin 2) (0 : Fin 2) t ∈ U := by
    intro t N hN
    have h1 : N * ((Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
        (j := (0 : Fin 2)) (by decide) t : SL2) : Matrix (Fin 2) (Fin 2) F4) ∈ U :=
      hrightSL _ N hN
    have h2 := Submodule.sub_mem U h1 hN
    have hXN : N * ((Matrix.SpecialLinearGroup.transvection (i := (1 : Fin 2))
        (j := (0 : Fin 2)) (by decide) t : SL2) : Matrix (Fin 2) (Fin 2) F4) - N =
        N * Matrix.single (1 : Fin 2) (0 : Fin 2) t := by
      rw [Matrix.SpecialLinearGroup.transvection_coe, Matrix.mul_add, Matrix.mul_one]
      abel
    rwa [hXN] at h2
  have hLdiag : ∀ (k : Fin 2) (t : F4) (N : V0), N ∈ U →
      Matrix.single k k t * N ∈ U := by
    intro k t N hN
    fin_cases k
    · have h1 := hL10 (1 : F4) N hN
      have h2 := hL01 t (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : F4) * N) h1
      rwa [← Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one] at h2
    · have h1 := hL01 (1 : F4) N hN
      have h2 := hL10 t (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : F4) * N) h1
      rwa [← Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one] at h2
  have hRdiag : ∀ (k : Fin 2) (t : F4) (N : V0), N ∈ U →
      N * Matrix.single k k t ∈ U := by
    intro k t N hN
    fin_cases k
    · have h1 := hR01 t N hN
      have h2 := hR10 (1 : F4) (N * Matrix.single (0 : Fin 2) (1 : Fin 2) t) h1
      rwa [Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one] at h2
    · have h1 := hR10 t N hN
      have h2 := hR01 (1 : F4) (N * Matrix.single (1 : Fin 2) (0 : Fin 2) t) h1
      rwa [Matrix.mul_assoc, Matrix.single_mul_single_same, mul_one] at h2
  have seed : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : F4) ∈ U := by
    obtain ⟨M0, hM0U, hM0ne⟩ := (Submodule.ne_bot_iff U).mp hbot
    have hnonzero : ∃ i j : Fin 2, M0 i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hM0ne (Matrix.ext fun i j => by simpa using h i j)
    obtain ⟨i, j, hij⟩ := hnonzero
    have hEij : Matrix.single i j (1 : F4) ∈ U := by
      have h1 := hLdiag i (M0 i j)⁻¹ M0 hM0U
      have h2 := hRdiag j (1 : F4) (Matrix.single i i (M0 i j)⁻¹ * M0) h1
      have hthis : Matrix.single i j ((M0 i j)⁻¹ * M0 i j * 1) ∈ U := by
        simpa only [Matrix.single_mul_mul_single] using h2
      simp only [mul_one] at hthis
      rwa [inv_mul_cancel₀ hij] at hthis
    fin_cases i <;> fin_cases j
    · exact hEij
    · have := hR10 (1 : F4) (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : F4)) hEij
      simpa using this
    · have := hL01 (1 : F4) (Matrix.single (1 : Fin 2) (0 : Fin 2) (1 : F4)) hEij
      simpa using this
    · have hE12 := hL01 (1 : F4) (Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : F4)) hEij
      have hE12' : Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : F4) ∈ U := by simpa using hE12
      have := hR10 (1 : F4) (Matrix.single (0 : Fin 2) (1 : Fin 2) (1 : F4)) hE12'
      simpa using this
  have h01t : ∀ t : F4, Matrix.single (0 : Fin 2) (1 : Fin 2) t ∈ U := fun t => by
    have := hR01 t (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : F4)) seed
    simpa using this
  have h10t : ∀ t : F4, Matrix.single (1 : Fin 2) (0 : Fin 2) t ∈ U := fun t => by
    have := hL10 t (Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : F4)) seed
    simpa using this
  have h11t : ∀ t : F4, Matrix.single (1 : Fin 2) (1 : Fin 2) t ∈ U := fun t => by
    have := hR01 (1 : F4) (Matrix.single (1 : Fin 2) (0 : Fin 2) t) (h10t t)
    simpa using this
  have h00t : ∀ t : F4, Matrix.single (0 : Fin 2) (0 : Fin 2) t ∈ U := fun t => by
    have := hR10 (1 : F4) (Matrix.single (0 : Fin 2) (1 : Fin 2) t) (h01t t)
    simpa using this
  have hsingle : ∀ (k l : Fin 2) (t : F4), Matrix.single k l t ∈ U := by
    intro k l t
    fin_cases k <;> fin_cases l
    · exact h00t t
    · exact h01t t
    · exact h10t t
    · exact h11t t
  exact Submodule.eq_top_iff'.mpr fun M =>
    (Matrix.matrix_eq_sum_single M) ▸
      (Submodule.sum_mem U fun i _ => Submodule.sum_mem U fun j _ => hsingle i j (M i j))

theorem stdHyp_sigma0 : Swap.StdHyp sigma0 :=
  ⟨sigma0_injective, finrank_V0, sigma0_irreducible⟩

end CFSG.EvenSporadicStandard.HNRecog.CSide
