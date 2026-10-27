module

public import CFSG.Quasithin.SteinbergCBGDCocycle
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLLNorm
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherFieldInvolution
public import CFSG.Quasithin.SteinbergCBGDFrob

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.Quasithin.SteinbergCB.GDescent CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Fixed

variable {k : Type*} [Field k] {d : ℕ}

theorem bgll_exists_fixed_basis [Finite k] {r : ℕ} (s : k ≃+* k) (hs : orderOf s = r)
    (hr : 0 < r) {B : Matrix (Fin d) (Fin d) k} (hB : IsUnit B) (hC : iterMat s B r = 1) :
    ∃ P : Matrix (Fin d) (Fin d) k, IsUnit P ∧ B * P.map s = P := by
  classical
  have ha : ∀ (c : k) (v : Fin d → k), semilinOf s hB (c • v) = s c • semilinOf s hB v :=
    semilinOf_smul s hB
  have hsr : s ^ r = 1 := hs ▸ pow_orderOf_eq_one s
  have hah : ∀ v, (⇑(semilinOf s hB))^[r] v = v := by
    intro v
    rw [semilinOf_iterate, hC, hsr, Matrix.one_mulVec, RingAut.coe_one]
    rfl
  obtain ⟨n, b, b₀, hbb₀⟩ :=
    CFSG.GroupTheory.SteinbergBK.exists_semilinear_fixed_basis s hs hr (semilinOf s hB) ha hah
  have hn : n = d := by
    have := Module.finrank_eq_card_basis b
    rw [Module.finrank_fin_fun, Fintype.card_fin] at this
    exact this.symm
  have hfix : ∀ j, semilinOf s hB (b j) = b j := by
    intro j
    have := (b₀ j).2
    rw [hbb₀] at this
    exact this
  set b' := b.reindex (finCongr hn) with hb'
  have hfix' : ∀ j, semilinOf s hB (b' j) = b' j := fun j => by
    rw [hb', Module.Basis.reindex_apply]
    exact hfix _
  set P : Matrix (Fin d) (Fin d) k := (Pi.basisFun k (Fin d)).toMatrix b' with hP
  have hPij : ∀ i j, P i j = b' j i := by
    intro i j
    rw [hP, Module.Basis.toMatrix_apply, Pi.basisFun_repr]
  have hPu : IsUnit P := by
    have := (Pi.basisFun k (Fin d)).invertibleToMatrix b'
    exact isUnit_of_invertible _
  refine ⟨P, hPu, ?_⟩
  ext i j
  have := congrFun (hfix' j) i
  rw [semilinOf_apply] at this
  rw [hPij, ← this, Matrix.mul_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hPij, Function.comp_apply]

end Fixed


section Core

variable {F : Type} [Field F] [Finite F]

theorem bgll_map_cube {σ : F ≃+* F} (hσ : orderOf σ = 3) (M : Matrix (Fin 3) (Fin 3) F) :
    ((M.map σ).map σ).map σ = M := by
  ext i j
  simp [bgll_sigma_cube hσ]

theorem bgll_core {σ : F ≃+* F} (hσ : orderOf σ = 3) {G : Matrix (Fin 3) (Fin 3) F}
    (hGu : IsUnit G) {c d : F} (hc0 : c ≠ 0) (hd0 : d ≠ 0) (hG : G.map σ = c • G)
    (hG3 : G * G * G = d • (1 : Matrix (Fin 3) (Fin 3) F)) :
    ∃ ν : F, ν ≠ 0 ∧ iterMat σ (ν • G) 3 = 1 := by
  have hG0 : G ≠ 0 := hGu.ne_zero
  have hmap : ∀ (a : F) (M : Matrix (Fin 3) (Fin 3) F), (a • M).map σ = σ a • M.map σ :=
    fun a M => smul_map σ a M
  have hmm : ∀ A B : Matrix (Fin 3) (Fin 3) F, (A * B).map σ = A.map σ * B.map σ :=
    fun A B => Matrix.map_mul (f := σ.toRingHom)
  have hN : c * σ c * σ (σ c) = 1 := by
    have h1 := bgll_map_cube hσ G
    simp only [hG, hmap, smul_smul, map_mul] at h1
    have h2 : (σ (σ c) * σ c * c - 1) • G = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    rcases smul_eq_zero.1 h2 with h | h
    · linear_combination h
    · exact absurd h hG0
  have hd : σ d = c ^ 3 * d := by
    have h1 : (G * G * G).map σ = (d • (1 : Matrix (Fin 3) (Fin 3) F)).map σ := by rw [hG3]
    rw [hmm, hmm, hmap, one_map, hG] at h1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hG3] at h1
    have h2 := congrFun (congrFun h1 0) 0
    simp at h2
    linear_combination -h2
  have ht0 : c ^ 2 * σ c * d ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hc0) ((map_ne_zero σ).2 hc0)) hd0
  have htσ : σ (c ^ 2 * σ c * d) = c ^ 2 * σ c * d := by
    simp only [map_mul, map_pow, hd]
    linear_combination (c ^ 2 * σ c * d) * hN
  obtain ⟨ν, hν0, hν⟩ := bgll_norm_surj hσ (t := (c ^ 2 * σ c * d)⁻¹)
    (by rw [map_inv₀, htσ]) (inv_ne_zero ht0)
  refine ⟨ν, hν0, ?_⟩
  have hit : iterMat σ G 3 = (c ^ 2 * σ c * d) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have hG3' : G * (G * G) = d • (1 : Matrix (Fin 3) (Fin 3) F) := by rw [← mul_assoc]; exact hG3
    rw [iterMat_succ, iterMat_succ, iterMat_succ, iterMat_zero, one_map, mul_one, hG, Matrix.mul_smul,
      hmap, hmm, hG]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hG3']
    congr 1
    ring
  rw [iterMat_smul, hit]
  have hnorm : normIter σ ν 3 = ν * σ ν * σ (σ ν) := by
    simp [normIter_succ, normIter_zero, mul_assoc]
  rw [hnorm, hν, smul_smul, inv_mul_cancel₀ ht0, one_smul]

end Core


section Main

variable {F : Type} [Field F] [Finite F]

theorem bgll_coe_mul_scalar (g : GL (Fin 3) F) (c : Fˣ) :
    ((g * GeneralLinearGroup.scalar (Fin 3) c : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (c : F) • (g : Matrix (Fin 3) (Fin 3) F) := by
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  ext i j
  simp [Matrix.mul_diagonal, mul_comm]

theorem bgll_exists_h {σ : F ≃+* F} (hσ : orderOf σ = 3) (g : GL (Fin 3) F)
    (hcomm : conjAut 3 F g * fieldAut 3 F σ = fieldAut 3 F σ * conjAut 3 F g)
    (h3 : conjAut 3 F g ^ 3 = 1) :
    ∃ h : GL (Fin 3) F, conjAut 3 F g * fieldAut 3 F σ =
      conjAut 3 F h * fieldAut 3 F σ * (conjAut 3 F h)⁻¹ := by
  have e1 : fieldAut 3 F σ * conjAut 3 F g =
      conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) g) * fieldAut 3 F σ := by
    have := conjAut_mul_fieldAut_mul (n := 3) (K := F) 1 g σ 1
    simpa using this
  have e2 : conjAut 3 F g = conjAut 3 F (GeneralLinearGroup.map (σ : F →+* F) g) :=
    mul_right_cancel (hcomm.trans e1)
  have hs : conjAut 3 F (g⁻¹ * GeneralLinearGroup.map (σ : F →+* F) g) * fieldAut 3 F 1 = 1 := by
    rw [map_one, mul_one, map_mul, map_inv, ← e2, inv_mul_cancel]
  obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ 1 hs
  have h3' : conjAut 3 F (g ^ 3) * fieldAut 3 F 1 = 1 := by
    rw [map_one, mul_one, map_pow, h3]
  obtain ⟨-, d, hd⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (le_refl 3) _ 1 h3'
  have hmapg : GeneralLinearGroup.map (σ : F →+* F) g = g * GeneralLinearGroup.scalar (Fin 3) c := by
    rw [hc]; group
  have hGσ : (g : Matrix (Fin 3) (Fin 3) F).map σ = (c : F) • (g : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hmapg
    simp only [bgll_coe_mul_scalar] at this
    exact this
  have hG3 : (g : Matrix (Fin 3) (Fin 3) F) * g * g = (d : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    have := congrArg (fun x : GL (Fin 3) F => (x : Matrix (Fin 3) (Fin 3) F)) hd
    simp only [GeneralLinearGroup.coe_scalar, Units.val_pow_eq_pow_val] at this
    rw [pow_three'] at this
    rw [← this, Matrix.scalar_apply, smul_one_eq_diagonal]
  obtain ⟨ν, hν0, hν⟩ := bgll_core hσ g.isUnit c.ne_zero d.ne_zero hGσ hG3
  have hBu : IsUnit (ν • (g : Matrix (Fin 3) (Fin 3) F)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul]
    exact (isUnit_iff_ne_zero.2 hν0).pow _ |>.mul ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
  obtain ⟨P, hP, hBP⟩ := bgll_exists_fixed_basis σ hσ (by norm_num) hBu hν
  set h : GL (Fin 3) F := hP.unit with hh
  refine ⟨h, ?_⟩
  have hν' : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν0
  have hhe : g * GeneralLinearGroup.map (σ : F →+* F) h =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν⁻¹ (inv_ne_zero hν0)) * h := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    have e3 : ((GeneralLinearGroup.map (σ : F →+* F) h : GL (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = P.map σ := rfl
    have e4 : (h : Matrix (Fin 3) (Fin 3) F) = P := rfl
    rw [e3, e4]
    have e5 : (g : Matrix (Fin 3) (Fin 3) F) * P.map σ = ν⁻¹ • P := by
      calc (g : Matrix (Fin 3) (Fin 3) F) * P.map σ =
          ν⁻¹ • ((ν • (g : Matrix (Fin 3) (Fin 3) F)) * P.map σ) := by
            rw [Matrix.smul_mul, smul_smul, hν', one_smul]
        _ = ν⁻¹ • P := by rw [hBP]
    rw [e5]
    ext i j
    simp [Matrix.diagonal_mul]
  have hg : conjAut 3 F g = conjAut 3 F (h * GeneralLinearGroup.map (σ : F →+* F) h⁻¹) := by
    have : g = GeneralLinearGroup.scalar (Fin 3) (Units.mk0 ν⁻¹ (inv_ne_zero hν0)) *
        (h * GeneralLinearGroup.map (σ : F →+* F) h⁻¹) := by
      rw [map_inv, ← mul_assoc, ← hhe]
      group
    rw [this, map_mul, conjAut_scalar, one_mul]
  have := conjAut_mul_fieldAut_mul (n := 3) (K := F) h h⁻¹ σ 1
  rw [map_inv, map_one, mul_one, mul_one] at this
  rw [this, ← hg]

end Main

end CFSG.HardMathSupport.Solomon.Coordinator
