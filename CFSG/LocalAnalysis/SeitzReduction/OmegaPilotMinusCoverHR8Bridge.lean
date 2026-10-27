module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCoverHR8Model
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotMinusCover
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatPlusType

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedOmega StatedQuadPlus)
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData (coordinateQuadMinus
  coordinateQuadPlus minusIndexEquiv plusIndexEquiv coordinateQuadMinus_apply
  coordinateQuadPlus_apply)

section Lin

variable {F : Type} [Field F] {r : ℕ}

@[expose] noncomputable def minusPlusFun (hn : 1 ≤ r + 1) (α α' : F) (v : Fin (2 * (r + 1)) → F) :
    Fin (r + 1) ⊕ Fin (r + 1) → F :=
  Sum.elim
    (Fin.snoc (α := fun _ => F) (fun l : Fin r => v (minusIndexEquiv (r + 1) hn (.inl l)))
      (v (minusIndexEquiv (r + 1) hn (.inr (.inr 0))) -
        α * v (minusIndexEquiv (r + 1) hn (.inr (.inr 1)))))
    (Fin.snoc (α := fun _ => F) (fun l : Fin r => v (minusIndexEquiv (r + 1) hn (.inr (.inl l))))
      (v (minusIndexEquiv (r + 1) hn (.inr (.inr 0))) -
        α' * v (minusIndexEquiv (r + 1) hn (.inr (.inr 1)))))

theorem minusPlusFun_add (hn : 1 ≤ r + 1) (α α' : F) (v w : Fin (2 * (r + 1)) → F)
    (s : Fin (r + 1) ⊕ Fin (r + 1)) :
    minusPlusFun hn α α' (v + w) s = minusPlusFun hn α α' v s + minusPlusFun hn α α' w s := by
  rcases s with i | i <;> induction i using Fin.lastCases <;>
    simp only [minusPlusFun, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last,
      Pi.add_apply] <;> ring

theorem minusPlusFun_smul (hn : 1 ≤ r + 1) (α α' : F) (a : F) (v : Fin (2 * (r + 1)) → F)
    (s : Fin (r + 1) ⊕ Fin (r + 1)) :
    minusPlusFun hn α α' (a • v) s = a * minusPlusFun hn α α' v s := by
  rcases s with i | i <;> induction i using Fin.lastCases <;>
    simp only [minusPlusFun, Sum.elim_inl, Sum.elim_inr, Fin.snoc_castSucc, Fin.snoc_last,
      Pi.smul_apply, smul_eq_mul] <;> ring

@[expose] noncomputable def minusPlusLin (hn : 1 ≤ r + 1) (α α' : F) :
    (Fin (2 * (r + 1)) → F) →ₗ[F] (Fin (2 * (r + 1)) → F) where
  toFun v j := minusPlusFun hn α α' v ((plusIndexEquiv (r + 1)).symm j)
  map_add' v w := funext fun _ => minusPlusFun_add hn α α' v w _
  map_smul' a v := funext fun _ => minusPlusFun_smul hn α α' a v _

variable (hn : 1 ≤ r + 1) (α α' : F) (v : Fin (2 * (r + 1)) → F)

theorem minusPlusLin_apply (j : Fin (2 * (r + 1))) :
    minusPlusLin hn α α' v j = minusPlusFun hn α α' v ((plusIndexEquiv (r + 1)).symm j) := rfl

theorem minusPlusLin_inl_castSucc (l : Fin r) :
    minusPlusLin hn α α' v (plusIndexEquiv (r + 1) (.inl l.castSucc)) =
      v (minusIndexEquiv (r + 1) hn (.inl l)) := by
  simp [minusPlusLin_apply, minusPlusFun]

theorem minusPlusLin_inr_castSucc (l : Fin r) :
    minusPlusLin hn α α' v (plusIndexEquiv (r + 1) (.inr l.castSucc)) =
      v (minusIndexEquiv (r + 1) hn (.inr (.inl l))) := by
  simp [minusPlusLin_apply, minusPlusFun]

theorem minusPlusLin_inl_last :
    minusPlusLin hn α α' v (plusIndexEquiv (r + 1) (.inl (Fin.last r))) =
      v (minusIndexEquiv (r + 1) hn (.inr (.inr 0))) -
        α * v (minusIndexEquiv (r + 1) hn (.inr (.inr 1))) := by
  simp [minusPlusLin_apply, minusPlusFun]

theorem minusPlusLin_inr_last :
    minusPlusLin hn α α' v (plusIndexEquiv (r + 1) (.inr (Fin.last r))) =
      v (minusIndexEquiv (r + 1) hn (.inr (.inr 0))) -
        α' * v (minusIndexEquiv (r + 1) hn (.inr (.inr 1))) := by
  simp [minusPlusLin_apply, minusPlusFun]

variable {hn α α'}

theorem minusPlusLin_injective (hαα : α ≠ α') : Function.Injective (minusPlusLin hn α α') := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  have h0 : ∀ j, minusPlusLin hn α α' v j = 0 := fun j => congrFun hv j
  have hu := h0 (plusIndexEquiv (r + 1) (.inl (Fin.last r)))
  have hw := h0 (plusIndexEquiv (r + 1) (.inr (Fin.last r)))
  rw [minusPlusLin_inl_last] at hu
  rw [minusPlusLin_inr_last] at hw
  have hw0 : v (minusIndexEquiv (r + 1) hn (.inr (.inr 1))) = 0 := by
    have h1 : (α' - α) * v (minusIndexEquiv (r + 1) hn (.inr (.inr 1))) = 0 := by
      linear_combination hu - hw
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hαα
    · exact h
  have hu0 : v (minusIndexEquiv (r + 1) hn (.inr (.inr 0))) = 0 := by
    rw [hw0, mul_zero, sub_zero] at hu
    exact hu
  funext i
  obtain ⟨s, rfl⟩ := (minusIndexEquiv (r + 1) hn).surjective i
  rcases s with l | l | l
  · have h := h0 (plusIndexEquiv (r + 1) (.inl l.castSucc))
    rwa [minusPlusLin_inl_castSucc] at h
  · have h := h0 (plusIndexEquiv (r + 1) (.inr l.castSucc))
    rwa [minusPlusLin_inr_castSucc] at h
  · fin_cases l
    · exact hu0
    · exact hw0

theorem coordinateQuadPlus_minusPlusLin {α β γ : F} (hα : α ^ 2 + β * α + γ = 0)
    (v : Fin (2 * (r + 1)) → F) :
    coordinateQuadPlus (r + 1) F (minusPlusLin hn α (-β - α) v) =
      coordinateQuadMinus (r + 1) F hn β γ v := by
  rw [coordinateQuadPlus_apply, coordinateQuadMinus_apply, Fin.sum_univ_castSucc]
  simp only [minusPlusLin_inl_castSucc, minusPlusLin_inr_castSucc, minusPlusLin_inl_last,
    minusPlusLin_inr_last]
  have hS : (∑ i : Fin r, v (minusIndexEquiv (r + 1) hn (.inl i)) *
      v (minusIndexEquiv (r + 1) hn (.inr (.inl i)))) =
      ∑ i : Fin (r + 1 - 1), v (minusIndexEquiv (r + 1) hn (.inl i)) *
        v (minusIndexEquiv (r + 1) hn (.inr (.inl i))) := rfl
  rw [hS]
  linear_combination (-(v (minusIndexEquiv (r + 1) hn (.inr (.inr 1))) ^ 2)) * hα

end Lin

section Frame

variable {F : Type} [Field F] {r : ℕ}

theorem frameEntry_plus_inl {n : ℕ} (t : Fin n → Fˣ) (k : Fin n) :
    frameEntry (plusFrameLeft n) (plusFrameRight n) t (plusIndexEquiv n (.inl k)) = t k :=
  (isHypFrame_plus F n).frameEntry_left t k

theorem frameEntry_plus_inr {n : ℕ} (t : Fin n → Fˣ) (k : Fin n) :
    frameEntry (plusFrameLeft n) (plusFrameRight n) t (plusIndexEquiv n (.inr k)) = (t k)⁻¹ :=
  (isHypFrame_plus F n).frameEntry_right t k

theorem frameEntry_minusSucc_inl (hn : 1 ≤ r + 1) (s : Fin r → Fˣ) (l : Fin r) :
    frameEntry (minusFrameLeft hn) (minusFrameRight hn) s (minusIndexEquiv (r + 1) hn (.inl l)) =
      s l :=
  (isHypFrame_minus F hn 0 0).frameEntry_left s l

theorem frameEntry_minusSucc_inr (hn : 1 ≤ r + 1) (s : Fin r → Fˣ) (l : Fin r) :
    frameEntry (minusFrameLeft hn) (minusFrameRight hn) s
      (minusIndexEquiv (r + 1) hn (.inr (.inl l))) = (s l)⁻¹ :=
  (isHypFrame_minus F hn 0 0).frameEntry_right s l

theorem frameEntry_minusSucc_aniso (hn : 1 ≤ r + 1) (s : Fin r → Fˣ) (l : Fin 2) :
    frameEntry (minusFrameLeft hn) (minusFrameRight hn) s
      (minusIndexEquiv (r + 1) hn (.inr (.inr l))) = 1 :=
  frameEntry_minus_aniso hn s l

theorem minusPlusLin_frameLin (hn : 1 ≤ r + 1) (α α' : F) (s : Fin r → Fˣ)
    (v : Fin (2 * (r + 1)) → F) :
    minusPlusLin hn α α' (frameLin (minusFrameLeft hn) (minusFrameRight hn) s v) =
      frameLin (plusFrameLeft (r + 1)) (plusFrameRight (r + 1)) (snocOneParam F r s)
        (minusPlusLin hn α α' v) := by
  funext j
  obtain ⟨σ, rfl⟩ := (plusIndexEquiv (r + 1)).surjective j
  rw [frameLin_apply]
  rcases σ with p | p
  · induction p using Fin.lastCases with
    | last =>
      rw [minusPlusLin_inl_last, minusPlusLin_inl_last, frameLin_apply, frameLin_apply,
        frameEntry_minusSucc_aniso, frameEntry_minusSucc_aniso, frameEntry_plus_inl,
        snocOneParam_last]
      simp only [Units.val_one, one_mul]
    | cast l =>
      rw [minusPlusLin_inl_castSucc, minusPlusLin_inl_castSucc, frameLin_apply,
        frameEntry_minusSucc_inl, frameEntry_plus_inl, snocOneParam_castSucc]
  · induction p using Fin.lastCases with
    | last =>
      rw [minusPlusLin_inr_last, minusPlusLin_inr_last, frameLin_apply, frameLin_apply,
        frameEntry_minusSucc_aniso, frameEntry_minusSucc_aniso, frameEntry_plus_inr,
        snocOneParam_last]
      simp only [inv_one, Units.val_one, one_mul]
    | cast l =>
      rw [minusPlusLin_inr_castSucc, minusPlusLin_inr_castSucc, frameLin_apply,
        frameEntry_minusSucc_inr, frameEntry_plus_inr, snocOneParam_castSucc]

end Frame

section Bridge

variable {F : Type} [Field F] {r : ℕ}

@[expose] noncomputable def minusPlusIsometry (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) :
    (coordinateQuadMinus (r + 1) F hn β γ).IsometryEquiv (coordinateQuadPlus (r + 1) F) where
  toLinearEquiv := LinearEquiv.ofInjectiveEndo (minusPlusLin hn α (-β - α))
    (minusPlusLin_injective hαα)
  map_app' v := coordinateQuadPlus_minusPlusLin (hn := hn) hα v

theorem minusPlusIsometry_apply (hn : 1 ≤ r + 1) {α β γ : F} (hα : α ^ 2 + β * α + γ = 0)
    (hαα : α ≠ -β - α) (v : Fin (2 * (r + 1)) → F) :
    (minusPlusIsometry hn hα hαα).toLinearEquiv v = minusPlusLin hn α (-β - α) v := rfl

theorem exists_ne_zero_of_isometryEquiv {d d' : ℕ} {Q₁ : QuadraticForm F (Fin d → F)}
    {Q₂ : QuadraticForm F (Fin d' → F)} (e : Q₁.IsometryEquiv Q₂) (h : ∃ v, Q₂ v ≠ 0) :
    ∃ v, Q₁ v ≠ 0 := by
  obtain ⟨w, hw⟩ := h
  exact ⟨e.symm w, by rw [← e.map_app, QuadraticMap.IsometryEquiv.apply_symm_apply]; exact hw⟩

theorem exists_ne_zero_coordinateQuadPlus_succ (r : ℕ) :
    ∃ v, coordinateQuadPlus (r + 1) F v ≠ 0 :=
  (isHypCoord_coordinateQuadPlus (K := F) (0 : Fin (r + 1))).exists_ne_zero

variable [Finite F] [CharP F 2]

@[expose] noncomputable def orthDerivedProjEquiv {d : ℕ} (Q : QuadraticForm F (Fin d → F))
    (hQ : ∃ v, Q v ≠ 0) : orthDerived Q ≃* matrixProjectiveDerived Q :=
  MulEquiv.ofBijective (projHom Q) ⟨projHom_injective hQ, projHom_surjective Q⟩

@[expose] noncomputable def minusPlusProjEquiv (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) :
    matrixProjectiveDerived (coordinateQuadMinus (r + 1) F hn β γ) ≃*
      matrixProjectiveDerived (coordinateQuadPlus (r + 1) F) :=
  (orthDerivedProjEquiv _ (exists_ne_zero_of_isometryEquiv (minusPlusIsometry hn hα hαα)
      (exists_ne_zero_coordinateQuadPlus_succ r))).symm.trans
    ((orthDerivedCongr (minusPlusIsometry hn hα hαα)).trans
      (orthDerivedProjEquiv _ (exists_ne_zero_coordinateQuadPlus_succ r)))

theorem minusPlusProjEquiv_frameHom (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) (s : Fin r → Fˣ) :
    minusPlusProjEquiv hn hα hαα ((isHypFrame_minus F hn β γ).frameHom s) =
      (isHypFrame_plus F (r + 1)).frameHom (snocOneParam F r s) := by
  have h1 : (orthDerivedProjEquiv (coordinateQuadMinus (r + 1) F hn β γ)
      (exists_ne_zero_of_isometryEquiv (minusPlusIsometry hn hα hαα)
        (exists_ne_zero_coordinateQuadPlus_succ r))).symm
        ((isHypFrame_minus F hn β γ).frameHom s) =
      ⟨frameLin (minusFrameLeft hn) (minusFrameRight hn) s,
        (isHypFrame_minus F hn β γ).frameLin_mem_orthDerived s⟩ := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  rw [minusPlusProjEquiv, MulEquiv.trans_apply, h1, MulEquiv.trans_apply,
    IsHypFrame.frameHom_apply]
  change projHom _ _ = projHom _ _
  congr 1
  apply Subtype.ext
  have hcoe : ((orthDerivedCongr (minusPlusIsometry hn hα hαα)
      ⟨frameLin (minusFrameLeft hn) (minusFrameRight hn) s,
        (isHypFrame_minus F hn β γ).frameLin_mem_orthDerived s⟩ :
      orthDerived (coordinateQuadPlus (r + 1) F)) :
        (Fin (2 * (r + 1)) → F) ≃ₗ[F] (Fin (2 * (r + 1)) → F)) =
      LinearEquiv.autCongr (minusPlusIsometry hn hα hαα).toLinearEquiv
        (frameLin (minusFrameLeft hn) (minusFrameRight hn) s) := rfl
  rw [hcoe]
  apply LinearEquiv.ext
  intro w
  rw [LinearEquiv.autCongr_apply_apply, minusPlusIsometry_apply, minusPlusLin_frameLin,
    ← minusPlusIsometry_apply hn hα hαα, LinearEquiv.apply_symm_apply]

@[expose] noncomputable def minusPlusBridge (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) :
    matrixProjectiveDerived (coordinateQuadMinus (r + 1) F hn β γ) ≃*
      StatedOmega (StatedQuadPlus (r + 1) F) :=
  (minusPlusProjEquiv hn hα hαα).trans (statedOmegaPlusEquiv F (r + 1) hn).symm

theorem minusPlusBridge_frameHom (hn : 1 ≤ r + 1) {α β γ : F}
    (hα : α ^ 2 + β * α + γ = 0) (hαα : α ≠ -β - α) (s : Fin r → Fˣ) :
    ((minusPlusBridge hn hα hαα ((isHypFrame_minus F hn β γ).frameHom s) :
        StatedOmega (StatedQuadPlus (r + 1) F)) : GL (Fin (r + 1) ⊕ Fin (r + 1)) F) =
      diagOmega F (r + 1) (snocOneParam F r s) := by
  rw [minusPlusBridge, MulEquiv.trans_apply, minusPlusProjEquiv_frameHom]
  exact statedOmegaPlusEquiv_symm_frameHom hn _

end Bridge

section Root

theorem coeff_ne_zero_of_irreducible {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : b ≠ 0 := by
  rintro rfl
  obtain ⟨δ, hδ⟩ := isSquare_of_charTwo' c
  apply hirr δ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [hδ]
  linear_combination δ ^ 2 * h2

theorem exists_root_of_card_eq_sq {K F : Type} [Field K] [Finite K] [CharP K 2] [Field F]
    [Finite F] (ι : K →+* F) (hF : Nat.card F = Nat.card K ^ 2) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : ∃ α : F, α ^ 2 + ι b * α + ι c = 0 := by
  let _ : Algebra K F := ι.toAlgebra
  let _ : Fintype K := Fintype.ofFinite K
  have : Module.Finite K F := Module.finite_iff_finite.mpr inferInstance
  have hE : Module.finrank K F = 2 := by
    have h1 := Module.natCard_eq_pow_finrank (K := K) (V := F)
    rw [hF] at h1
    exact (Nat.pow_right_injective (Finite.one_lt_card (α := K)) h1).symm
  exact exists_root_of_finrank_two hE hirr

theorem root_ne_other_of_ne_zero {F : Type} [Field F] [CharP F 2] {α β : F} (hβ : β ≠ 0) :
    α ≠ -β - α := by
  intro h
  apply hβ
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination h - α * h2

end Root

end CFSG.SeitzReduction.OmegaPilot
