module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalORigidCen

public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix Subgroup CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Index

variable {ι₃ ι₂ ι₂P ι : Type}

@[expose] def oeP (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (oe' : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂)
    (oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂P) : ι₂P ⊕ (Fin 2 ⊕ Fin 2) ≃ ι :=
  (Equiv.sumCongr oe₂.symm (Equiv.refl _)).trans
    (((Equiv.sumAssoc _ _ _).trans ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
      (Equiv.sumAssoc _ _ _).symm)).trans ((Equiv.sumCongr oe' (Equiv.refl _)).trans oe))

variable (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (oe' : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂)
  (oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂P)

theorem oeP_inl_inl (a : ι₃) : oeP oe oe' oe₂ (.inl (oe₂ (.inl a))) = oe (.inl (oe' (.inl a))) := by
  simp [oeP]

theorem oeP_inl_inr (b : Fin 2 ⊕ Fin 2) : oeP oe oe' oe₂ (.inl (oe₂ (.inr b))) = oe (.inr b) := by
  simp [oeP]

theorem oeP_inr (b : Fin 2 ⊕ Fin 2) : oeP oe oe' oe₂ (.inr b) = oe (.inl (oe' (.inr b))) := by
  simp [oeP]

end Index

section Blocks

variable {K : Type} [Field K] {ι₃ ι₂ ι₂P ι : Type} [Fintype ι₃] [DecidableEq ι₃] [Fintype ι₂]
  [DecidableEq ι₂] [Fintype ι₂P] [DecidableEq ι₂P] [Fintype ι] [DecidableEq ι]
  {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {oe' : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂}
  {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂P}

theorem oblk_oblk_oeP (Y₃ : Matrix ι₃ ι₃ K) (X X' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) :
    oblk oe (oblk oe' Y₃ X') X = oblk (oeP oe oe' oe₂) (oblk oe₂ Y₃ X) X' := by
  ext i j
  obtain ⟨x, rfl⟩ := (oeP oe oe' oe₂).surjective i
  obtain ⟨y, rfl⟩ := (oeP oe oe' oe₂).surjective j
  rw [oblk_apply]
  rcases x with c | b <;> rcases y with d | b'
  · obtain ⟨c, rfl⟩ := oe₂.surjective c
    obtain ⟨d, rfl⟩ := oe₂.surjective d
    rcases c with a | b <;> rcases d with a' | b' <;>
      simp only [oeP_inl_inl, oeP_inl_inr, oblk_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
        fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.zero_apply]
  · obtain ⟨c, rfl⟩ := oe₂.surjective c
    rcases c with a | b <;>
      simp only [oeP_inl_inl, oeP_inl_inr, oeP_inr, oblk_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, Matrix.zero_apply]
  · obtain ⟨d, rfl⟩ := oe₂.surjective d
    rcases d with a' | b' <;>
      simp only [oeP_inl_inl, oeP_inl_inr, oeP_inr, oblk_apply, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, Matrix.zero_apply]
  · simp only [oeP_inr, oblk_apply, fromBlocks_apply₁₁, fromBlocks_apply₂₂]

theorem oKappaGL_oRhoOneGL (B : SL(2, K)) :
    oKappaGL oe (oRhoOneGL oe' B) = oRhoOneGL (oeP oe oe' oe₂) B := by
  apply Units.ext
  rw [coe_oKappaGL, coe_oRhoOneGL, coe_oRhoOneGL, oblk_oblk_oeP (oe₂ := oe₂), oblk_one]

theorem oKappaGL_oRhoTwoGL (A : SL(2, K)) :
    oKappaGL oe (oRhoTwoGL oe' A) = oRhoTwoGL (oeP oe oe' oe₂) A := by
  apply Units.ext
  rw [coe_oKappaGL, coe_oRhoTwoGL, coe_oRhoTwoGL, oblk_oblk_oeP (oe₂ := oe₂), oblk_one]

theorem oRhoOneGL_eq_oKappaGL (B : SL(2, K)) :
    oRhoOneGL oe B = oKappaGL (oeP oe oe' oe₂) (oRhoOneGL oe₂ B) := by
  apply Units.ext
  rw [coe_oKappaGL, coe_oRhoOneGL, coe_oRhoOneGL, ← oblk_oblk_oeP, oblk_one]

theorem oRhoTwoGL_eq_oKappaGL (A : SL(2, K)) :
    oRhoTwoGL oe A = oKappaGL (oeP oe oe' oe₂) (oRhoTwoGL oe₂ A) := by
  apply Units.ext
  rw [coe_oKappaGL, coe_oRhoTwoGL, coe_oRhoTwoGL, ← oblk_oblk_oeP, oblk_one]

theorem oKappaGL_oKappaGL (Y : GL ι₃ K) :
    oKappaGL oe (oKappaGL oe' Y) = oKappaGL (oeP oe oe' oe₂) (oKappaGL oe₂ Y) := by
  apply Units.ext
  rw [coe_oKappaGL, coe_oKappaGL, coe_oKappaGL, coe_oKappaGL, oblk_oblk_oeP (oe₂ := oe₂)]

end Blocks

section Forms

variable {K : Type} [Field K] {ι₃ ι₂ ι₂P ι : Type} {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι}
  {oe' : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂} {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂P} {Q : (ι → K) → K}
  {Q₂ : (ι₂ → K) → K}
  {Q₃ : (ι₃ → K) → K} {Q₂P : (ι₂P → K) → K}

theorem quad_oeP
    (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
    (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe' (.inl a))) +
      StatedQuadPlus 2 K (fun b => w (oe' (.inr b))))
    (hQ₂P : ∀ w, Q₂P w = Q₃ (fun a => w (oe₂ (.inl a))) +
      StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
    (v : ι → K) :
    Q v = Q₂P (fun a => v (oeP oe oe' oe₂ (.inl a))) +
      StatedQuadPlus 2 K (fun b => v (oeP oe oe' oe₂ (.inr b))) := by
  rw [hQ, hQ₂, hQ₂P]
  simp only [oeP_inl_inl, oeP_inl_inr, oeP_inr]
  rw [add_right_comm]

end Forms

section Omega

variable {K : Type} [Field K] [CharP K 2] {ι₃ ι₂ ι₂P ι : Type} [Fintype ι₃] [DecidableEq ι₃]
  [Fintype ι₂] [DecidableEq ι₂] [Fintype ι₂P] [DecidableEq ι₂P] [Fintype ι] [DecidableEq ι]
  {oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι} {oe' : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂}
  {oe₂ : ι₃ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι₂P} {Q : (ι → K) → K} {Q₂ : (ι₂ → K) → K}
  {Q₃ : (ι₃ → K) → K} {Q₂P : (ι₂P → K) → K}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))
  (hQ₂ : ∀ w, Q₂ w = Q₃ (fun a => w (oe' (.inl a))) +
    StatedQuadPlus 2 K (fun b => w (oe' (.inr b))))
  (hQ₂P : ∀ w, Q₂P w = Q₃ (fun a => w (oe₂ (.inl a))) +
    StatedQuadPlus 2 K (fun b => w (oe₂ (.inr b))))
  (hSL : commutator SL(2, K) = ⊤)

theorem oKappa_oRhoOne_eq (B : SL(2, K)) :
    oKappa oe hQ (oRhoOne oe' hQ₂ hSL B) = oRhoOne (oeP oe oe' oe₂) (quad_oeP hQ hQ₂ hQ₂P) hSL B :=
  Subtype.ext (oKappaGL_oRhoOneGL B)

omit [CharP K 2] in
theorem oKappa_oRhoTwo_eq (A : SL(2, K)) :
    oKappa oe hQ (oRhoTwo oe' hQ₂ hSL A) = oRhoTwo (oeP oe oe' oe₂) (quad_oeP hQ hQ₂ hQ₂P) hSL A :=
  Subtype.ext (oKappaGL_oRhoTwoGL A)

theorem oProj_oKappa_oRhoOne_eq (B : SL(2, K)) :
    oProj Q (oKappa oe hQ (oRhoOne oe' hQ₂ hSL B)) =
      oProj Q (oRhoOne (oeP oe oe' oe₂) (quad_oeP hQ hQ₂ hQ₂P) hSL B) := by
  rw [oKappa_oRhoOne_eq hQ hQ₂ hQ₂P]

theorem oRhoOne_eq_oKappa (B : SL(2, K)) :
    oRhoOne oe hQ hSL B = oKappa (oeP oe oe' oe₂) (quad_oeP hQ hQ₂ hQ₂P) (oRhoOne oe₂ hQ₂P hSL B) :=
  Subtype.ext (oRhoOneGL_eq_oKappaGL B)

omit [CharP K 2] in
theorem oRhoTwo_eq_oKappa (A : SL(2, K)) :
    oRhoTwo oe hQ hSL A = oKappa (oeP oe oe' oe₂) (quad_oeP hQ hQ₂ hQ₂P) (oRhoTwo oe₂ hQ₂P hSL A) :=
  Subtype.ext (oRhoTwoGL_eq_oKappaGL A)

theorem oBarOne_eq_oeP :
    oBarOne oe hQ hSL = ((oProj Q).comp ((oKappa (oeP oe oe' oe₂) (quad_oeP hQ hQ₂ hQ₂P)).comp
      (oRhoOne oe₂ hQ₂P hSL))).range := by
  rw [oBarOne]
  congr 1
  ext B : 1
  simp only [MonoidHom.comp_apply]
  rw [oRhoOne_eq_oKappa hQ hQ₂ hQ₂P]

omit [CharP K 2] in
theorem oBarTwo_eq_oeP :
    oBarTwo oe hQ hSL = ((oProj Q).comp ((oKappa (oeP oe oe' oe₂) (quad_oeP hQ hQ₂ hQ₂P)).comp
      (oRhoTwo oe₂ hQ₂P hSL))).range := by
  rw [oBarTwo]
  congr 1
  ext A : 1
  simp only [MonoidHom.comp_apply]
  rw [oRhoTwo_eq_oKappa hQ hQ₂ hQ₂P]

end Omega

end CFSG.ComponentClassification.RankTwoClassical.ORigid
