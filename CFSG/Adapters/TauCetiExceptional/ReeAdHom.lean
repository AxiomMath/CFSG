module

public import CFSG.Adapters.TauCetiExceptional.ReeAdjoint
public import CFSG.Adapters.TauCetiExceptional.ReeConj

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U TauCeti

variable {A : Type*} [CommRing A]

abbrev adConj (g : Matrix.GeneralLinearGroup (Fin 7) A) : Module.End A (RootModule .G2 A) :=
  adOp (g : Matrix (Fin 7) (Fin 7) A)
    ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)

theorem rootModule_ext {f f' : Module.End A (RootModule .G2 A)}
    (h : ∀ b, f (Finsupp.single b 1) = f' (Finsupp.single b 1)) : f = f' :=
  Finsupp.lhom_ext' fun b => LinearMap.ext_ring (h b)

theorem sum_coord_smul_single (b : Label .G2) :
    ∑ u : Fin 14, coord u (labMat A b) • Finsupp.single (lab u) (1 : A) = Finsupp.single b 1 := by
  rw [labMat, Finset.sum_eq_single (bas.symm b)]
  · rw [coord_basisMatR, ite_eq_left rfl, one_smul, lab_bas_symm]
  · intro u _ hu
    rw [coord_basisMatR, ite_eq_right hu, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

theorem adConj_one : adConj (1 : Matrix.GeneralLinearGroup (Fin 7) A) = 1 := by
  refine rootModule_ext fun b => ?_
  rw [adOp_single]
  simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
  rw [sum_coord_smul_single, Module.End.one_apply]

theorem adConj_mul (g : Matrix.GeneralLinearGroup (Fin 7) A)
    {h : Matrix.GeneralLinearGroup (Fin 7) A} (hh : h ∈ normGroup A) :
    adConj (g * h) = adConj g * adConj h := by
  refine rootModule_ext fun b => ?_
  rw [Module.End.mul_apply, adOp_single (h : Matrix (Fin 7) (Fin 7) A), map_sum]
  simp only [map_smul, adOp_single, labMat_lab]
  set c : Fin 14 → A := fun u => coord u ((h : Matrix (Fin 7) (Fin 7) A) * labMat A b *
    ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) with hc
  have hspan := ((hh (bas.symm b)).1).eq_sum
  have e : ((g * h : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
      labMat A b * (((g * h)⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) :
        Matrix (Fin 7) (Fin 7) A) =
      ∑ u, c u • ((g : Matrix (Fin 7) (Fin 7) A) * basisMatR A u *
        ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) := by
    rw [mul_inv_rev, Units.val_mul, Units.val_mul]
    have e1 : (g : Matrix (Fin 7) (Fin 7) A) * h * labMat A b *
        (((h⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) =
        g * (h * labMat A b * (h⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A)) *
          (g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) := by
      simp only [Matrix.mul_assoc]
    rw [e1, labMat, hspan, Matrix.mul_sum, Matrix.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  simp only [coord_sum, coord_smul, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun v _ => by rw [smul_smul]

@[expose] def adHom (A : Type*) [CommRing A] : normGroup A →* Module.End A (RootModule .G2 A) where
  toFun g := adConj (g : Matrix.GeneralLinearGroup (Fin 7) A)
  map_one' := adConj_one
  map_mul' g h := adConj_mul (g : Matrix.GeneralLinearGroup (Fin 7) A) h.2

theorem adHom_apply (g : normGroup A) :
    adHom A g = adConj (g : Matrix.GeneralLinearGroup (Fin 7) A) :=
  rfl

@[expose] def adUnits (K : Type*) [Field K] : normGroup K →* ModGL .G2 K :=
  (adHom K).toHomUnits

theorem coe_adUnits {K : Type*} [Field K] (g : normGroup K) :
    ((adUnits K g : ModGL .G2 K) : Module.End K (RootModule .G2 K)) =
      adConj (g : Matrix.GeneralLinearGroup (Fin 7) K) :=
  rfl

abbrev rootPoint (k : Fin 2 ⊕ Fin 2) (t : A) : Matrix.GeneralLinearGroup (Fin 7) A :=
  (G2ShortRoot.IntegralToralClosure.rootSubgroupPoints k A (Multiplicative.ofAdd t) :
    Matrix.GeneralLinearGroup (Fin 7) A)

theorem conj_rootPoint (k : Fin 2 ⊕ Fin 2) (t : A) (s : Fin 14) :
    InSpan (rootPointMat k t * basisMatR A s * rootPointMat k (-t)) := by
  rcases k with i | i
  · exact ⟨_, conj_rootPoint_inl i t s⟩
  · exact ⟨_, conj_rootPoint_inr i t s⟩

theorem rootPoint_mem_normGroup (k : Fin 2 ⊕ Fin 2) (t : A) : rootPoint k t ∈ normGroup A := by
  intro s
  rw [coe_rootPoint_inv]
  refine ⟨conj_rootPoint k t s, ?_⟩
  have h := conj_rootPoint k (-t) s
  rwa [neg_neg] at h

theorem adConj_rootPoint_inl (i : Fin 2) (t : A) :
    adConj (rootPoint (.inl i) t) = xOp .G2 A (nodeMap i) t := by
  refine rootModule_ext fun b => Finsupp.ext fun x => ?_
  rw [adOp_single_apply, coe_rootPoint_inv, labMat, conj_rootPoint_inl i t (bas.symm b),
    coord_sum_smul_basisMatR, lab_bas_symm, lab_bas_symm, xOp_single_apply]

theorem adConj_rootPoint_inr (i : Fin 2) (t : A) :
    adConj (rootPoint (.inr i) t) = yOp .G2 A (nodeMap i) t := by
  refine rootModule_ext fun b => Finsupp.ext fun x => ?_
  rw [adOp_single_apply, coe_rootPoint_inv, labMat, conj_rootPoint_inr i t (bas.symm b),
    coord_sum_smul_basisMatR, lab_bas_symm, lab_bas_symm, yOp_single_apply]

end CFSG.TauCetiBridge.Ree
