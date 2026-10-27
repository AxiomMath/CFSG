module

public import CFSG.Adapters.TauCetiExceptional.ReeRat

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U CFSG.TauCetiBridge.BigCell TauCeti

variable {A : Type} [CommRing A] [Algebra (ZMod 3) A]

theorem det_eq_one_of_mem_points {g : Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ G2ShortRoot.PrimeField.points A) : (g : Matrix (Fin 7) (Fin 7) A).det = 1 := by
  have h := evalMat_eq_zero_of_mem_points detPoly evalMat_detPoly_ratRootGroup hg
  rwa [evalMat_detPoly, sub_eq_zero] at h

theorem inSpan_conj_of_mem_points {g : Matrix.GeneralLinearGroup (Fin 7) A}
    (hg : g ∈ G2ShortRoot.PrimeField.points A) (t : Fin 14) :
    InSpan ((g : Matrix (Fin 7) (Fin 7) A) * basisMatR A t *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) := by
  have h : ∀ r c, evalMat (g : Matrix (Fin 7) (Fin 7) A) (normPoly t r c) = 0 := fun r c =>
    evalMat_eq_zero_of_mem_points _ (evalMat_normPoly_ratRootGroup t r c) hg
  simp only [evalMat_normPoly, adjugate_eq_inv_of_det_eq_one g (det_eq_one_of_mem_points hg)] at h
  rw [inSpan_iff]
  exact sub_eq_zero.1 (Matrix.ext h)

theorem points_le_normGroup : G2ShortRoot.PrimeField.points A ≤ normGroup A := fun g hg t => by
  refine ⟨inSpan_conj_of_mem_points hg t, ?_⟩
  have h := inSpan_conj_of_mem_points (inv_mem hg) t
  rwa [inv_inv] at h

theorem evalMat_natMat_adConj_of_mem_points
    {L : Type} [Field L] [Algebra (ZMod 3) L]
    {g : Matrix.GeneralLinearGroup (Fin 7) L} (hg : g ∈ G2ShortRoot.PrimeField.points L)
    (P : MvPolynomial (Fin (nLab .G2) × Fin (nLab .G2)) ℤ) (hP : VanishesOnRat .G2 P) :
    evalMat (natMat .G2 L (adConj g)) P = 0 := by
  have h := evalMat_eq_zero_of_mem_points (adPoly P) (evalMat_adPoly_ratRootGroup P hP) hg
  rwa [evalMat_adPoly, adjugate_eq_inv_of_det_eq_one g (det_eq_one_of_mem_points hg)] at h

@[expose] def adPoints (L : Type) [Field L] [Algebra (ZMod 3) L] :
    G2ShortRoot.PrimeField.points L →* ModGL .G2 L :=
  (adUnits L).comp (Subgroup.inclusion points_le_normGroup)

theorem coe_adPoints {L : Type} [Field L] [Algebra (ZMod 3) L]
    (g : G2ShortRoot.PrimeField.points L) :
    ((adPoints L g : ModGL .G2 L) : Module.End L (RootModule .G2 L)) =
      adConj (g : Matrix.GeneralLinearGroup (Fin 7) L) :=
  rfl

theorem coe_primeFieldRootPoint (k : Fin 2 ⊕ Fin 2) (t : A) :
    ((G2ShortRoot.PrimeField.rootSubgroupPoints k A (Multiplicative.ofAdd t) :
      Matrix.GeneralLinearGroup (Fin 7) A)) = rootPoint k t :=
  G2ShortRoot.PrimeField.coe_rootSubgroupPoints k A _

theorem adPoints_rootSubgroupPoints_inl
    {L : Type} [Field L] [Algebra (ZMod 3) L] (i : Fin 2)
    (t : L) : adPoints L (G2ShortRoot.PrimeField.rootSubgroupPoints (.inl i) L
      (Multiplicative.ofAdd t)) = xUnit .G2 L (nodeMap i) t :=
  Units.ext (by rw [coe_adPoints, coe_primeFieldRootPoint, adConj_rootPoint_inl]; rfl)

theorem adPoints_rootSubgroupPoints_inr
    {L : Type} [Field L] [Algebra (ZMod 3) L] (i : Fin 2)
    (t : L) : adPoints L (G2ShortRoot.PrimeField.rootSubgroupPoints (.inr i) L
      (Multiplicative.ofAdd t)) = yUnit .G2 L (nodeMap i) t :=
  Units.ext (by rw [coe_adPoints, coe_primeFieldRootPoint, adConj_rootPoint_inr]; rfl)

end CFSG.TauCetiBridge.Ree
