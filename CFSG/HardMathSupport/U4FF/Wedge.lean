module

public import CFSG.HardMathSupport.U4FF.Omega2Defs
public import CFSG.RankThree.PartOne.CTP.SU4EvenSU

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CliffordAlgebra QuadraticMap
  CFSG.RankThree.PartOne.CTP.SU4Even CFSG.ClassicalInvolution.WeakCT.SU4
  CFSG.LieType.Universal.Unitary
open scoped Matrix

section Equivariance

variable {F K : Type} [Field F] [Field K] [Algebra F K] {σ₀ : K ≃+* K} {b c : F}

theorem rv_mulVec (D : KleinDataEven F K σ₀ b c) (X : Matrix (Fin 4) (Fin 4) K) (y : Fin 4 → K) :
    D.rv (X *ᵥ y) = D.Hs X *ᵥ D.rv y := by
  funext i
  rw [KleinDataEven.rv_apply]
  exact D.Hs_mulVec X y i

theorem xmat_spinAction (D : KleinDataEven F K σ₀ b c) (s : spinGroup (quadMinus 3 F b c))
    (v : Vm 3 F) :
    D.Xmat (spinAction (quadMinus 3 F b c) s v) =
      D.PhiMon s * D.Xmat v * D.Hs (D.PhiMon s⁻¹) := by
  have key : ∀ x : Fin 4 → K, D.Xmat (spinAction (quadMinus 3 F b c) s v) *ᵥ D.rv x =
      (D.PhiMon s * D.Xmat v * D.Hs (D.PhiMon s⁻¹)) *ᵥ D.rv x := by
    intro x
    have h := congrArg (fun a => D.Psi a x) (ι_spinAction (quadMinus 3 F b c) s v)
    simp only [map_mul, Module.End.mul_apply, KleinDataEven.Psi_ι, KleinDataEven.Psi_spin] at h
    rw [KleinDataEven.gam_apply] at h
    rw [h, KleinDataEven.gam_apply, rv_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have key' : ∀ y : Fin 4 → K, D.Xmat (spinAction (quadMinus 3 F b c) s v) *ᵥ y =
      (D.PhiMon s * D.Xmat v * D.Hs (D.PhiMon s⁻¹)) *ᵥ y := by
    intro y
    have := key (D.rv y)
    rwa [KleinDataEven.rv_rv] at this
  ext i j
  have := congrFun (key' (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem hs_inv_eq_transpose (D : KleinDataEven F K σ₀ b c) (s : spinGroup (quadMinus 3 F b c))
    (hs : D.PhiGL s ∈ SU σ₀ 4) : D.Hs (D.PhiMon s⁻¹) = (D.PhiMon s)ᵀ := by
  have hSU := (mem_SU.1 hs).2
  have hgg : D.PhiMon s * D.PhiMon s⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  have hg : ((D.PhiGL s : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = D.PhiMon s := rfl
  rw [hg] at hSU
  have h1 : conjTr σ₀ (D.PhiMon s) * antidiag 4 = antidiag 4 * D.PhiMon s⁻¹ := by
    calc conjTr σ₀ (D.PhiMon s) * antidiag 4
        = conjTr σ₀ (D.PhiMon s) * antidiag 4 * (D.PhiMon s * D.PhiMon s⁻¹) := by
          rw [hgg, Matrix.mul_one]
      _ = (conjTr σ₀ (D.PhiMon s) * antidiag 4 * D.PhiMon s) * D.PhiMon s⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = antidiag 4 * D.PhiMon s⁻¹ := by rw [hSU]
  have hE : ∀ a b : Fin 4, D.PhiMon s⁻¹ (Fin.rev a) b = σ₀ (D.PhiMon s (Fin.rev b) a) := by
    intro a b
    have h := congrFun (congrFun h1 a) b
    revert h
    generalize D.PhiMon s = g
    generalize D.PhiMon s⁻¹ = g'
    intro h
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, antidiag, conjTr, Fin.rev] at h ⊢ <;>
      exact h.symm
  ext i j
  simp only [KleinDataEven.Hs, Matrix.of_apply, Matrix.transpose_apply]
  rw [hE i (Fin.rev j), Fin.rev_rev, D.σσ]

abbrev VIdx : Type := Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2

@[expose] def colEquiv : Fin 6 ≃ VIdx where
  toFun := ![Sum.inl iZ, Sum.inl iO, Sum.inr (Sum.inr 0), Sum.inr (Sum.inr 1),
    Sum.inr (Sum.inl iO), Sum.inr (Sum.inl iZ)]
  invFun x := Sum.elim (fun i => (![0, 1] : Fin 2 → Fin 6) i)
    (Sum.elim (fun i => (![5, 4] : Fin 2 → Fin 6) i) (fun i => (![2, 3] : Fin 2 → Fin 6) i)) x
  left_inv a := by fin_cases a <;> rfl
  right_inv x := by
    rcases x with i | i | i <;> fin_cases i <;> rfl

@[expose] def up {A : Type*} (X : Matrix (Fin 4) (Fin 4) A) : Fin 6 → A :=
  fun p => X (wedgeIdx p).1 (wedgeIdx p).2

@[expose] def Tm (D : KleinDataEven F K σ₀ b c) : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
    0, D.δ, 0, 0, 0, 0;
    0, 0, 1, -D.ω, 0, 0;
    0, 0, 1, algebraMap F K b + D.ω, 0, 0;
    0, 0, 0, 0, -D.ε, 0;
    0, 0, 0, 0, 0, 1]

theorem up_xmat (D : KleinDataEven F K σ₀ b c) (v : Vm 3 F) :
    up (D.Xmat v) = Tm D *ᵥ fun a => algebraMap F K (v (colEquiv a)) := by
  ext p
  fin_cases p <;>
    simp [up, wedgeIdx, KleinDataEven.Xmat, skew6, Tm, colEquiv, Matrix.mulVec, dotProduct,
      Fin.sum_univ_six] <;> ring

theorem up_mul_mul_transpose {A : Type*} [CommRing A] (M X : Matrix (Fin 4) (Fin 4) A)
    (hd : ∀ i, X i i = 0) (hs : ∀ i j, X j i = -X i j) :
    up (M * X * Mᵀ) = comp2 M *ᵥ up X := by
  have h10 := hs 0 1
  have h20 := hs 0 2
  have h30 := hs 0 3
  have h21 := hs 1 2
  have h31 := hs 1 3
  have h32 := hs 2 3
  have d0 := hd 0
  have d1 := hd 1
  have d2 := hd 2
  have d3 := hd 3
  ext p
  fin_cases p <;>
    simp [up, wedgeIdx, comp2, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Fin.sum_univ_six, h10, h20, h30, h21, h31, h32, d0, d1, d2, d3] <;> ring

theorem xmat_diag (D : KleinDataEven F K σ₀ b c) (v : Vm 3 F) (i : Fin 4) : D.Xmat v i i = 0 := by
  fin_cases i <;> simp [KleinDataEven.Xmat, skew6]

theorem xmat_skew (D : KleinDataEven F K σ₀ b c) (v : Vm 3 F) (i j : Fin 4) :
    D.Xmat v j i = -D.Xmat v i j := by
  fin_cases i <;> fin_cases j <;> simp [KleinDataEven.Xmat, skew6]

theorem tm_mul_spin (D : KleinDataEven F K σ₀ b c) (s : spinGroup (quadMinus 3 F b c))
    (hs : D.PhiGL s ∈ SU σ₀ 4) :
    Tm D * ((spinMatrix (quadMinus 3 F b c) s : Matrix VIdx VIdx F).submatrix colEquiv
      colEquiv).map (algebraMap F K) = comp2 (D.PhiMon s) * Tm D := by
  classical
  set M : Matrix VIdx VIdx F := (spinMatrix (quadMinus 3 F b c) s : Matrix VIdx VIdx F) with hM
  have key : ∀ u : Fin 6 → F,
      (Tm D * (M.submatrix colEquiv colEquiv).map (algebraMap F K)) *ᵥ
        (fun a => algebraMap F K (u a)) =
      (comp2 (D.PhiMon s) * Tm D) *ᵥ (fun a => algebraMap F K (u a)) := by
    intro u
    let v : Vm 3 F := fun x => u (colEquiv.symm x)
    have hv : ∀ a, v (colEquiv a) = u a := fun a => by simp [v]
    have h1 : ∀ a, spinAction (quadMinus 3 F b c) s v (colEquiv a) =
        (M.submatrix colEquiv colEquiv *ᵥ u) a := by
      intro a
      rw [← spinMatrix_mulVec]
      simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
      rw [← Equiv.sum_comp colEquiv]
      simp [hv, hM]
    have h2 := xmat_spinAction D s v
    rw [hs_inv_eq_transpose D s hs] at h2
    have h3 := congrArg up h2
    rw [up_mul_mul_transpose _ _ (xmat_diag D v) (xmat_skew D v), up_xmat, up_xmat] at h3
    have h4 : (fun a => algebraMap F K (spinAction (quadMinus 3 F b c) s v (colEquiv a))) =
        (M.submatrix colEquiv colEquiv).map (algebraMap F K) *ᵥ fun a => algebraMap F K (u a) := by
      funext a
      rw [h1 a, RingHom.map_mulVec]
      rfl
    rw [h4, Matrix.mulVec_mulVec] at h3
    simp only [hv] at h3
    rw [h3, Matrix.mulVec_mulVec]
  ext p q
  have h := congrFun (key (Pi.single q 1)) p
  have hsingle : (fun a => algebraMap F K ((Pi.single q (1 : F) : Fin 6 → F) a)) =
      (Pi.single q (1 : K) : Fin 6 → K) := by
    funext a
    by_cases haq : a = q <;> simp [Pi.single_apply, haq]
  rw [hsingle] at h
  simpa [Matrix.mulVec_single_one] using h

@[expose] def TmInv (D : KleinDataEven F K σ₀ b c) : Matrix (Fin 6) (Fin 6) K :=
  !![1, 0, 0, 0, 0, 0;
    0, D.ε, 0, 0, 0, 0;
    0, 0, D.ε * (algebraMap F K b + D.ω), D.ε * D.ω, 0, 0;
    0, 0, -D.ε, D.ε, 0, 0;
    0, 0, 0, 0, -D.δ, 0;
    0, 0, 0, 0, 0, 1]

theorem tm_mul_tmInv (D : KleinDataEven F K σ₀ b c) : Tm D * TmInv D = 1 := by
  have h : (2 * D.ω + algebraMap F K b) * D.ε = 1 := by
    have := D.δ_mul_ε
    rwa [KleinDataEven.δ] at this
  have h' : D.δ * D.ε = 1 := D.δ_mul_ε
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Tm, TmInv, Matrix.mul_apply, Fin.sum_univ_six, Matrix.one_apply] <;>
    first | linear_combination h | linear_combination -h | linear_combination h' | ring

theorem tmInv_mul_tm (D : KleinDataEven F K σ₀ b c) : TmInv D * Tm D = 1 :=
  mul_eq_one_comm.1 (tm_mul_tmInv D)

@[expose] def TmGL (D : KleinDataEven F K σ₀ b c) : GL (Fin 6) K :=
  ⟨Tm D, TmInv D, tm_mul_tmInv D, tmInv_mul_tm D⟩

end Equivariance

end CFSG.HardMathSupport.U4FF
