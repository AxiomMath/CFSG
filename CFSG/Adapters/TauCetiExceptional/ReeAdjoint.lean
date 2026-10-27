module

public import CFSG.Adapters.TauCetiExceptional.ReeBasis

public noncomputable section

namespace CFSG.TauCetiBridge.Ree

open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U TauCeti

variable {A : Type*} [CommRing A]

abbrev labMat (A : Type*) [CommRing A] (b : Label .G2) : Matrix (Fin 7) (Fin 7) A :=
  basisMatR A (bas.symm b)

theorem labMat_lab (t : Fin 14) : labMat A (lab t) = basisMatR A t := by
  rw [labMat, ← bas_apply, Equiv.symm_apply_apply]

theorem lab_bas_symm (b : Label .G2) : lab (bas.symm b) = b := by
  rw [← bas_apply, Equiv.apply_symm_apply]

@[expose] def adOp (g h : Matrix (Fin 7) (Fin 7) A) : Module.End A (RootModule .G2 A) :=
  Finsupp.linearCombination A fun b =>
    ∑ u : Fin 14, coord u (g * labMat A b * h) • Finsupp.single (lab u) (1 : A)

theorem adOp_single (g h : Matrix (Fin 7) (Fin 7) A) (b : Label .G2) :
    adOp g h (Finsupp.single b 1) =
      ∑ u : Fin 14, coord u (g * labMat A b * h) • Finsupp.single (lab u) (1 : A) := by
  rw [adOp, Finsupp.linearCombination_single, one_smul]

theorem adOp_single_apply (g h : Matrix (Fin 7) (Fin 7) A) (b x : Label .G2) :
    adOp g h (Finsupp.single b 1) x = coord (bas.symm x) (g * labMat A b * h) := by
  rw [adOp_single, Finsupp.finsetSum_apply, Finset.sum_eq_single (bas.symm x)]
  · rw [Finsupp.smul_apply, lab_bas_symm, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  · intro u _ hu
    rw [Finsupp.smul_apply, Finsupp.single_eq_of_ne, smul_zero]
    intro h
    exact hu (by rw [h, ← bas_apply, Equiv.symm_apply_apply])
  · exact fun h => absurd (Finset.mem_univ _) h

abbrev spanW (A : Type*) [CommRing A] : Submodule A (Matrix (Fin 7) (Fin 7) A) :=
  Submodule.span A (Set.range (basisMatR A))

theorem inSpan_iff_mem {Y : Matrix (Fin 7) (Fin 7) A} : InSpan Y ↔ Y ∈ spanW A := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩

abbrev conjL (g h : Matrix (Fin 7) (Fin 7) A) :
    Matrix (Fin 7) (Fin 7) A →ₗ[A] Matrix (Fin 7) (Fin 7) A :=
  (LinearMap.mulLeft A g).comp (LinearMap.mulRight A h)

theorem conjL_apply (g h Y : Matrix (Fin 7) (Fin 7) A) : conjL g h Y = g * Y * h := by
  rw [LinearMap.comp_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, Matrix.mul_assoc]

theorem mem_spanW_of_basis {g h : Matrix (Fin 7) (Fin 7) A}
    (hb : ∀ t, InSpan (g * basisMatR A t * h)) {Y : Matrix (Fin 7) (Fin 7) A}
    (hY : Y ∈ spanW A) : g * Y * h ∈ spanW A := by
  have hle : (spanW A).map (conjL g h) ≤ spanW A := by
    rw [Submodule.map_span_le]
    rintro _ ⟨t, rfl⟩
    rw [conjL_apply, ← inSpan_iff_mem]
    exact hb t
  rw [← conjL_apply]
  exact hle ⟨Y, hY, rfl⟩

@[expose] def normGroup (A : Type*) [CommRing A] :
    Subgroup (Matrix.GeneralLinearGroup (Fin 7) A) where
  carrier := {g | ∀ t, InSpan ((g : Matrix (Fin 7) (Fin 7) A) * basisMatR A t *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) ∧
    InSpan (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
      basisMatR A t * (g : Matrix (Fin 7) (Fin 7) A))}
  mul_mem' := by
    intro g h hg hh t
    simp only [Set.mem_ofPred_eq, mul_inv_rev, Units.val_mul] at hg hh ⊢
    constructor
    · rw [inSpan_iff_mem]
      have e : (g : Matrix (Fin 7) (Fin 7) A) * h * basisMatR A t *
          (((h⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A)) =
          g * (h * basisMatR A t * (h⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A)) *
            (g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) := by
        simp only [Matrix.mul_assoc]
      rw [e]
      exact mem_spanW_of_basis (fun u => (hg u).1) (inSpan_iff_mem.1 (hh t).1)
    · rw [inSpan_iff_mem]
      have e : ((h⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
          ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) *
            basisMatR A t * (g * h) =
          (h⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) *
            ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) * basisMatR A t * g) * h := by
        simp only [Matrix.mul_assoc]
      rw [e]
      exact mem_spanW_of_basis (fun u => (hh u).2) (inSpan_iff_mem.1 (hg t).2)
  one_mem' := fun t => by
    simp only [inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one]
    exact ⟨inSpan_basisMatR t, inSpan_basisMatR t⟩
  inv_mem' := fun {g} hg t => by
    simp only [Set.mem_ofPred_eq, inv_inv] at hg ⊢
    exact ⟨(hg t).2, (hg t).1⟩

theorem conj_mem_spanW {g : Matrix.GeneralLinearGroup (Fin 7) A} (hg : g ∈ normGroup A)
    {Y : Matrix (Fin 7) (Fin 7) A} (hY : Y ∈ spanW A) :
    (g : Matrix (Fin 7) (Fin 7) A) * Y *
      ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 7) A) : Matrix (Fin 7) (Fin 7) A) ∈ spanW A :=
  mem_spanW_of_basis (fun t => (hg t).1) hY

end CFSG.TauCetiBridge.Ree
