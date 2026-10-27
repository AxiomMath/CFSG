module

public import CFSG.HardMathSupport.Solomon.Coordinator.L3AFix

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.UnitaryFlag

section True

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def etaTrue (q : ℕ) (K : Type) [Field K] :
    ↥(slPi true 3 q K) ⧸ Subgroup.center ↥(slPi true 3 q K) ≃* projectiveSL 3 K :=
  (QuotientGroup.congr (Subgroup.center ↥(slPi true 3 q K))
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K)) (slPiTrueEquiv q K)
    (Subgroup.map_center_eq (slPiTrueEquiv q K))).trans
    (QuotientGroup.quotientMulEquivOfEq (scalars_eq_center (n := 3) (K := K)).symm)

theorem etaTrue_mk (q : ℕ) (g : ↥(slPi true 3 q K)) :
    etaTrue q K (g : ↥(slPi true 3 q K) ⧸ Subgroup.center ↥(slPi true 3 q K)) =
      proj 3 K (slPiTrueEquiv q K g) :=
  rfl

theorem etaTrue_surj (q : ℕ) : Function.Surjective (etaTrue q K) := (etaTrue q K).surjective

theorem slPiTrueEquiv_frob (hK : PiField true p f K) (σ : K ≃+* K) (g : ↥(slPi true 3 (p ^ f) K)) :
    slPiTrueEquiv (p ^ f) K (frobSL hK σ g) =
      Matrix.SpecialLinearGroup.map σ.toRingHom (slPiTrueEquiv (p ^ f) K g) := by
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slPiTrueEquiv]
  apply Units.ext
  have h1 : ((slPiTrueEquiv (p ^ f) K g : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
    congrArg Units.val (toGL_slPiTrueEquiv g)
  rw [coe_frobSL, coe_frobGL]
  show _ = ((Matrix.SpecialLinearGroup.map σ.toRingHom (slPiTrueEquiv (p ^ f) K g) :
    Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  rw [Matrix.SpecialLinearGroup.map_apply_coe, h1]
  rfl

theorem congr_etaTrue_frob (hK : PiField true p f K) (σ : K ≃+* K) :
    MulAut.congr (etaTrue (p ^ f) K)
      (centerDescend ↥(slPi true 3 (p ^ f) K) (frobSL hK σ)) = fieldAut 3 K σ := by
  ext x
  obtain ⟨g, rfl⟩ := (etaTrue (p ^ f) K).surjective x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [centerDescend_mk, etaTrue_mk, etaTrue_mk, slPiTrueEquiv_frob, fieldAut_proj]

theorem congr_etaTrue_conj (q : ℕ) (ζ : MulAut ↥(slPi true 3 q K)) {y : GL (Fin 3) K}
    (hy : ∀ s : ↥(slPi true 3 q K), ((ζ s : ↥(slPi true 3 q K)) : GL (Fin 3) K) = y * s * y⁻¹) :
    MulAut.congr (etaTrue q K) (centerDescend ↥(slPi true 3 q K) ζ) = conjAut 3 K y := by
  ext x
  obtain ⟨g, rfl⟩ := (etaTrue q K).surjective x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [centerDescend_mk, etaTrue_mk, etaTrue_mk, conjAut_proj]
  congr 1
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [toGL_slPiTrueEquiv, CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation,
    toGL_slPiTrueEquiv, hy]

end True

section False

variable {p f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def etaFalse (hK : PiField false p f K) (hq2 : 2 < p ^ f) :
    ↥(slPi false 3 (p ^ f) K) ⧸ Subgroup.center ↥(slPi false 3 (p ^ f) K) ≃*
      unitaryPSU hK.unitary 3 :=
  suCenterEquiv hK.unitary hq2

theorem frobSL_false_eq (hK : PiField false p f K) (σ : K ≃+* K) :
    frobSL hK σ = suField hK.unitary σ := by
  refine MulEquiv.ext fun s => Subtype.ext ?_
  rw [coe_frobSL]
  exact ((coe_suField σ s).trans (glAut_eq_frobGL σ s)).symm

theorem congr_eta_false_frob (hK : PiField false p f K) (hq2 : 2 < p ^ f) (σ : K ≃+* K) :
    MulAut.congr (etaFalse hK hq2)
      (centerDescend ↥(slPi false 3 (p ^ f) K) (frobSL hK σ)) = psuField hK.unitary σ := by
  rw [frobSL_false_eq]
  exact congr_centerDescend_suField hK.unitary hq2 σ

theorem congr_eta_false_conj (hK : PiField false p f K) (hq2 : 2 < p ^ f)
    (ζ : MulAut ↥(slPi false 3 (p ^ f) K)) {y : GL (Fin 3) K} (hy : y ∈ glPi false 3 (p ^ f) K)
    (hζ : ∀ s : ↥(slPi false 3 (p ^ f) K),
      ((ζ s : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) = y * s * y⁻¹) :
    MulAut.congr (etaFalse hK hq2)
      (centerDescend ↥(slPi false 3 (p ^ f) K) ζ) =
      psuConj hK.unitary ⟨y, mem_unitaryIsom3.2 ((mem_glPi_false hK.unitary).1 hy)⟩ := by
  have h : ζ = suConj hK.unitary ⟨y, mem_unitaryIsom3.2 ((mem_glPi_false hK.unitary).1 hy)⟩ := by
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [hζ]
    exact (coe_suConj (h := hK.unitary)
      (⟨y, mem_unitaryIsom3.2 ((mem_glPi_false hK.unitary).1 hy)⟩ : ↥(unitaryIsom3 hK.unitary))
      (s : ↥(unitarySU p f K 3))).symm
  rw [h]
  exact congr_centerDescend_suConj hK.unitary hq2 _

end False

end CFSG.HardMathSupport.Solomon.Coordinator
