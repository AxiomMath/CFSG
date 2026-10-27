module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QBlk
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QUCov
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherInvolutionCentralizer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open CFSG Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram idForm)

variable {K : Type} [Field K] {n r s : ℕ}

abbrev eigP (l : K) (A : Module.End K (Fin n → K)) : Submodule K (Fin n → K) :=
  LinearMap.ker (invSMulOp l A - 1)

abbrev eigM (l : K) (A : Module.End K (Fin n → K)) : Submodule K (Fin n → K) :=
  LinearMap.ker (invSMulOp l A + 1)

@[expose] def eigCoord {l : K} {A : Module.End K (Fin n → K)}
    (hc : IsCompl (eigP l A) (eigM l A)) (eP : eigP l A ≃ₗ[K] (Fin r → K))
    (eM : eigM l A ≃ₗ[K] (Fin s → K)) : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin s → K)) :=
  (Submodule.prodEquivOfIsCompl _ _ hc).symm.trans (eP.prodCongr eM)

section coord

variable {l : K} {A : Module.End K (Fin n → K)} (hc : IsCompl (eigP l A) (eigM l A))
  (eP : eigP l A ≃ₗ[K] (Fin r → K)) (eM : eigM l A ≃ₗ[K] (Fin s → K))

theorem eigCoord_symm (w : (Fin r → K) × (Fin s → K)) :
    (eigCoord hc eP eM).symm w = (eP.symm w.1 : Fin n → K) + (eM.symm w.2 : Fin n → K) := rfl

theorem eigCoord_apply_fst (x : eigP l A) : eigCoord hc eP eM (x : Fin n → K) = (eP x, 0) := by
  apply (eigCoord hc eP eM).symm.injective
  rw [LinearEquiv.symm_apply_apply, eigCoord_symm, LinearEquiv.symm_apply_apply, map_zero,
    Submodule.coe_zero, add_zero]

theorem eigCoord_apply_snd (y : eigM l A) : eigCoord hc eP eM (y : Fin n → K) = (0, eM y) := by
  apply (eigCoord hc eP eM).symm.injective
  rw [LinearEquiv.symm_apply_apply, eigCoord_symm, LinearEquiv.symm_apply_apply, map_zero,
    Submodule.coe_zero, zero_add]

theorem eigCoord_A (hl0 : l ≠ 0) (v : Fin n → K) :
    eigCoord hc eP eM (A v) = (l • (eigCoord hc eP eM v).1, (-l) • (eigCoord hc eP eM v).2) := by
  have hAT : ∀ w, A w = l • invSMulOp l A w := fun w => by
    rw [invSMulOp, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hl0, one_smul]
  obtain ⟨w, rfl⟩ := (eigCoord hc eP eM).symm.surjective v
  rw [LinearEquiv.apply_symm_apply, eigCoord_symm, map_add, hAT, hAT,
    apply_eq_of_mem_ker_sub_one (eP.symm w.1).2, apply_eq_neg_of_mem_ker_add_one (eM.symm w.2).2,
    smul_neg, ← neg_smul]
  have h1 : eigCoord hc eP eM (l • (eP.symm w.1 : Fin n → K)) = (l • w.1, 0) := by
    rw [← Submodule.coe_smul, eigCoord_apply_fst, map_smul, LinearEquiv.apply_symm_apply]
  have h2 : eigCoord hc eP eM ((-l) • (eM.symm w.2 : Fin n → K)) = (0, (-l) • w.2) := by
    rw [← Submodule.coe_smul, eigCoord_apply_snd, map_smul, LinearEquiv.apply_symm_apply]
  rw [map_add, h1, h2]
  simp

end coord

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem coe_eq_blockScalar (a : gramSU h (idGram K n)) {l : K} (hl0 : l ≠ 0)
    (hc : IsCompl (eigP l (unitaryOp (suOp h a))) (eigM l (unitaryOp (suOp h a))))
    (eP : eigP l (unitaryOp (suOp h a)) ≃ₗ[K] (Fin r → K))
    (eM : eigM l (unitaryOp (suOp h a)) ≃ₗ[K] (Fin s → K)) :
    (a : GL (Fin n) K) = blockScalar (eigCoord hc eP eM) (Units.mk0 l hl0)
      (Units.mk0 (-l) (neg_ne_zero.mpr hl0)) := by
  apply Units.ext
  refine Matrix.ext_iff_mulVec.mpr fun v => (eigCoord hc eP eM).injective ?_
  rw [apply_blockScalar_mulVec]
  exact eigCoord_A hc eP eM hl0 v

theorem exists_block_of_mem_centralizer (htwo : (2 : K) ≠ 0) (a : gramSU h (idGram K n))
    {l : K} (hl0 : l ≠ 0)
    (hc : IsCompl (eigP l (unitaryOp (suOp h a))) (eigM l (unitaryOp (suOp h a))))
    (eP : eigP l (unitaryOp (suOp h a)) ≃ₗ[K] (Fin r → K))
    (eM : eigM l (unitaryOp (suOp h a)) ≃ₗ[K] (Fin s → K)) {x : gramSU h (idGram K n)}
    (hx : x ∈ centralizer ({a} : Set (gramSU h (idGram K n)))) :
    ∃ y : GL (Fin r) K × GL (Fin s) K, blockConj (eigCoord hc eP eM) y = x := by
  have hll : l ≠ -l := fun h1 => hl0 (by
    have h3 : (2 : K) * l = 0 := by linear_combination h1
    exact (mul_eq_zero.mp h3).resolve_left htwo)
  have hxa : (x : GL (Fin n) K) * a = a * x := congrArg Subtype.val
    (mem_centralizer_singleton_iff.mp hx)
  rw [coe_eq_blockScalar h a hl0 hc eP eM] at hxa
  exact exists_blockConj_eq_of_commute (eigCoord hc eP eM) (c₁ := Units.mk0 l hl0)
    (c₂ := Units.mk0 (-l) (neg_ne_zero.mpr hl0)) hll hxa

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
