module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.CentA6ClPSLSmallGraph3Coord
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearHigherBIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFormFixed
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentAssemble

public section

namespace CFSG.ComponentClassification.CatFC.PSLSmallGraph3

open Subgroup Matrix
open CFSG.RankThree.PartOne.KCOrthogonalDescent

section Transfer

open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.ComponentClassification.CatalogueBAlternatingIsometry
  (basisMatrixEquiv basisMatrixEquiv_mulVec)

variable {n : ℕ} {K : Type} [Field K]

@[expose] noncomputable def isoToSim (hodd : ringChar K ≠ 2) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K)) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R)) →*
      ↥(similitudeGroup n K R) :=
  (Subgroup.inclusion (isometry_le_similitude n K R)).comp
    ((isometryGroupEquiv R).toMonoidHom.comp
      (MulEquiv.subgroupCongr (orthogonalGroup_matrixQuadraticForm hodd R hR)).toMonoidHom)

theorem isoToSim_mulVec (hodd : ringChar K ≠ 2) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K))
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R))) (v : Fin n → K) :
    ((isoToSim hodd R hR g).val : GL (Fin n) K).val.mulVec v =
      (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) v := by
  have h := basisMatrixEquiv_mulVec (Pi.basisFun K (Fin n)) g.val v
  simp only [Pi.basisFun_equivFun, LinearEquiv.refl_apply] at h
  exact h

theorem isoToSim_scalar (hodd : ringChar K ≠ 2) (R : GL (Fin n) K)
    (hR : (R : Matrix (Fin n) (Fin n) K)ᵀ = (R : Matrix (Fin n) (Fin n) K))
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm R))) (c : Kˣ)
    (h : isoToSim hodd R hR g = similitudeScalars n K R c) (v : Fin n → K) :
    (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) v = (c : K) • v := by
  rw [← isoToSim_mulVec hodd R hR g v, h]
  funext i
  simp [similitudeScalars_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mulVec_diagonal]

end Transfer

section Fixed

open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatalogueBGraphForm
open CFSG.ComponentClassification.CatalogueBHigherLinearAction

variable {n : ℕ} {K : Type} [Field K]

theorem exists_cube_root [Finite K] (hK : Nat.card K = 9) (u : Kˣ) : ∃ c : Kˣ, c ^ 3 = u := by
  have hc : (Nat.card Kˣ).Coprime 3 := by rw [Nat.card_units, hK]; norm_num
  exact ⟨(powCoprime hc).symm u, by simpa using (powCoprime hc).apply_symm_apply u⟩

theorem pslRange_three_eq_top [Finite K] (hK : Nat.card K = 9) : pslRange 3 K = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨A, rfl⟩ := ProjGenLinGroup.mk_surjective x
  rw [CatalogueBHigherLinearField.mk_mem_pslRange_iff_det_power]
  exact exists_cube_root hK _

@[expose] def toFixedT (A : GL (Fin n) K) (h : pslRange n K = ⊤) :
    fixedPGL n K A →* fixedT n K A where
  toFun x := ⟨x, by rw [Subgroup.mem_subgroupOf, h]; exact Subgroup.mem_top _⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem toFixedT_injective (A : GL (Fin n) K) (h : pslRange n K = ⊤) :
    Function.Injective (toFixedT A h) :=
  fun _ _ hxy => congrArg Subtype.val hxy

@[expose] noncomputable def toFixedPSL (hodd : ringChar K ≠ 2) (A : GL (Fin n) K)
    (hR : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (h : pslRange n K = ⊤) :
    ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)) →* fixedPSL n K A :=
  ((fixedPSLEquivT n K A).symm.toMonoidHom).comp
    ((toFixedT A h).comp ((similitudeProjection n K A).comp (isoToSim hodd A⁻¹ hR)))

theorem toFixedPSL_eq_one (hodd : ringChar K ≠ 2) (A : GL (Fin n) K)
    (hR : ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)ᵀ =
      ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    (h : pslRange n K = ⊤)
    (g : ↥(TauCeti.QuadraticMap.orthogonalGroup (matrixQuadraticForm A⁻¹)))
    (hg : toFixedPSL hodd A hR h g = 1) :
    ∃ c : K, ∀ v, (g : (Fin n → K) ≃ₗ[K] (Fin n → K)) v = c • v := by
  have h1 : (toFixedT A h) (similitudeProjection n K A (isoToSim hodd A⁻¹ hR g)) = 1 := by
    apply (fixedPSLEquivT n K A).symm.injective
    rw [map_one]
    exact hg
  have h2 : similitudeProjection n K A (isoToSim hodd A⁻¹ hR g) = 1 := by
    apply toFixedT_injective A h
    rw [map_one]
    exact h1
  have h3 : isoToSim hodd A⁻¹ hR g ∈ (similitudeProjection n K A).ker := h2
  rw [similitudeProjection_kernel] at h3
  obtain ⟨c, hc⟩ := h3
  exact ⟨c, isoToSim_scalar hodd A⁻¹ hR g c hc.symm⟩

end Fixed

section Dihedral3

open CFSG.ComponentClassification.CatalogueBLinearHigherB
open CFSG.ComponentClassification.CatalogueBGraphForm

variable {K : Type} [Field K] [Finite K]

theorem exists_split_three (hodd : ringChar K ≠ 2) (R : GL (Fin 3) K)
    (hR : (R : Matrix (Fin 3) (Fin 3) K)ᵀ = (R : Matrix (Fin 3) (Fin 3) K)) :
    Nonempty (HypSplit (matrixQuadraticForm R) 1 1) := by
  obtain ⟨m, δ, hδ, ⟨H⟩⟩ := exists_regular_split (matrixQuadraticForm R)
    (polarBilin_matrixQuadraticForm_nondegenerate hodd R hR)
  have h1 := H.finrank_eq
  rw [Module.finrank_fin_fun] at h1
  have hm : m = 1 := by omega
  have hδ' : δ = 1 := by omega
  subst hm
  subst hδ'
  exact ⟨H⟩


theorem exists_dihedral (hodd : ringChar K ≠ 2) (hK : Nat.card K = 9) (A : GL (Fin 3) K)
    (hR : ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)ᵀ =
      ((A⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) :
    ∃ z t : fixedPSL 3 K A, orderOf z = 8 ∧ orderOf t = 2 ∧ t * z * t⁻¹ = z⁻¹ := by
  obtain ⟨H⟩ := exists_split_three hodd A⁻¹ hR
  have hT := pslRange_three_eq_top hK
  obtain ⟨a, ha⟩ : ∃ a : Kˣ, orderOf a = 8 := by
    obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
    exact ⟨a, by rw [ha, Nat.card_units, hK]⟩
  have ha8 : a ^ 8 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha4 : a ^ 4 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [ha]; norm_num)
  refine ⟨toFixedPSL hodd A hR hT (zElt H a), toFixedPSL hodd A hR hT (tElt H), ?_, ?_, ?_⟩
  · have h8 : (toFixedPSL hodd A hR hT (zElt H a)) ^ 8 = 1 := by
      rw [← map_pow, zElt_pow_eq_one H ha8, map_one]
    have h4 : ¬ (toFixedPSL hodd A hR hT (zElt H a)) ^ 4 = 1 := by
      intro h
      have hz4 : zElt H a ^ 4 = zElt H (a ^ 4) := zElt_pow_eq H a 4
      have h' : toFixedPSL hodd A hR hT (zElt H (a ^ 4)) = 1 :=
        (congrArg (toFixedPSL hodd A hR hT) hz4.symm).trans
          ((map_pow (toFixedPSL hodd A hR hT) (zElt H a) 4).trans h)
      obtain ⟨c, hc⟩ := toFixedPSL_eq_one hodd A hR hT _ h'
      exact zElt_not_scalar H ha4 c hc
    exact orderOf_eq_prime_pow (p := 2) (n := 2) h4 h8
  · have hne : toFixedPSL hodd A hR hT (tElt H) ≠ 1 := by
      intro h
      obtain ⟨c, hc⟩ := toFixedPSL_eq_one hodd A hR hT _ h
      exact tElt_not_scalar H c hc
    refine orderOf_eq_prime ?_ hne
    rw [← map_pow, pow_two, tElt_mul_self, map_one]
  · rw [← map_inv, ← map_mul, ← map_mul, tElt_conj, map_inv]

end Dihedral3

end CFSG.ComponentClassification.CatFC.PSLSmallGraph3
