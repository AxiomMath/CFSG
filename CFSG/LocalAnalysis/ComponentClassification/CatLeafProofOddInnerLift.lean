module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerCent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude)

theorem oddLie_inner_psp {r : ℕ} {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hadm : StatedLieAdmissible .PSp r p f)
    (A : gsp r K) (hA : orderOf (conjAut r K A) = 2)
    {L : Subgroup (fixedSubgroup (conjAut r K A))} (hL : IsComponent L) :
    OddLieCentralQuotient p L := by
  have hf : 1 ≤ f := hadm.2.1
  have hr : 2 ≤ r := hadm.2.2.1
  have hA1 : conjAut r K A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : conjAut r K A * conjAut r K A = 1 := by
    rw [← pow_two, ← hA, pow_orderOf_eq_one]
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin r ⊕ Fin r) K) ≠ GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by omega) (A * A)).1
    (by rw [map_mul, hA2])
  set M := ((A : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hM
  have hAA : M * M = (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hcen : GeneralLinearGroup.scalar (Fin r ⊕ Fin r) c ∈ center (GL (Fin r ⊕ Fin r) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have ha : ∀ x, conjSp r K A (conjSp r K A x) = x := by
    intro x
    apply Subtype.ext
    rw [← MulAut.mul_apply, ← map_mul, coe_conjSp, hc,
      ← Subgroup.mem_center_iff.mp hcen (x : GL (Fin r ⊕ Fin r) K), mul_inv_cancel_right]
  have hα : ∀ s, conjAut r K A (conjAut r K A s) = s := fun s => by
    rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  have hK' : (proj r K).ker ≤ center (StatedSp r K) := by
    rw [ker_proj]
    intro z hz
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← GeneralLinearGroup.center_eq_range_scalar] at hz
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hz g)
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    proj_surjective hK' ha hα (fun x => (conjAut_proj A x).symm)
  set R := L.map (fixedSubgroup (conjAut r K A)).subtype with hRdef
  have hR : Assembly.IsComponentOf R (fixedSubgroup (conjAut r K A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (fixedSubgroup (conjAut r K A)) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, -, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  have hAμ : ∀ v w, pairedSympForm K r (((linA A : LinearMap.GeneralLinearGroup K
      (Fin r ⊕ Fin r → K)) : Module.End K (Fin r ⊕ Fin r → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
        Module.End K (Fin r ⊕ Fin r → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K r v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  have hQo := oddLieCentralQuotient_of_component_equiv
    ((MulEquiv.subgroupCongr (show fixedSubgroup (conjSp r K A) = spCent r K A from rfl)).trans
      (spCentEquiv A))
    (fun N hN => OddInner.oddLie_similitudeCentralizer hp hp2 hf hK hr finrank_standard
      pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA)
      hAμ hN) hQ'
  exact oddLieCentralQuotient_of_mulEquiv
    (L.equivMapOfInjective (fixedSubgroup (conjAut r K A)).subtype (subtype_injective _))
    (OddInner.oddLieCentralQuotient_of_centerQuotient_equiv eQR.symm
      (oddLieCentralQuotient_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm hQo))

end CFSG.ComponentClassification.CatLeafProof
