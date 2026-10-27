module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Sp4OutDiagCent
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSelf

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.Blueprint Module
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.Burgoyne.Sp (spCent spCentEquiv linA linA_apply linA_mul_self
  form_similitude)
open CFSG.ComponentClassification

theorem psl2CQ_inner_psp {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p ^ f) (hf : 1 ≤ f) (A : gsp 2 K)
    (hA : orderOf (conjAut 2 K A) = 2) {L : Subgroup (FixedCommutingProduct.fixedSubgroup (conjAut 2 K A))}
    (hL : IsComponent L) : Psl2CQ p L := by
  have hA1 : conjAut 2 K A ≠ 1 := fun h => by
    rw [h, orderOf_one] at hA
    exact absurd hA (by norm_num)
  have hA2 : conjAut 2 K A * conjAut 2 K A = 1 := by
    have h2 := pow_orderOf_eq_one (conjAut 2 K A)
    rw [hA] at h2
    rw [← pow_two]
    exact h2
  have hAns : ∀ c : Kˣ,
      (A : GL (Fin 2 ⊕ Fin 2) K) ≠ GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c :=
    fun c hc => hA1 ((Burgoyne.Sp.conjAut_eq_one_iff (by omega) A).2 ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := (Burgoyne.Sp.conjAut_eq_one_iff (by omega) (A * A)).1
    (by rw [map_mul, hA2])
  set M := ((A : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) with hM
  have hAA : M * M = (c : K) • 1 := by
    have := congrArg Units.val hc
    rw [Subgroup.coe_mul, Units.val_mul, GeneralLinearGroup.coe_scalar] at this
    rw [this, Matrix.smul_one_eq_diagonal]
    rfl
  have hcen : GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈ center (GL (Fin 2 ⊕ Fin 2) K) := by
    rw [GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩
  have ha : ∀ x, conjSp 2 K A (conjSp 2 K A x) = x := by
    intro x
    apply Subtype.ext
    rw [← MulAut.mul_apply, ← map_mul, coe_conjSp, hc,
      ← Subgroup.mem_center_iff.mp hcen (x : GL (Fin 2 ⊕ Fin 2) K), mul_inv_cancel_right]
  have hα : ∀ s, conjAut 2 K A (conjAut 2 K A s) = s := fun s => by
    rw [← MulAut.mul_apply, hA2, MulAut.one_apply]
  have hK' : (proj 2 K).ker ≤ center (StatedSp 2 K) := by
    rw [ker_proj]
    intro z hz
    rw [Subgroup.mem_subgroupOf, StatedScalars,
      ← GeneralLinearGroup.center_eq_range_scalar] at hz
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext (Subgroup.mem_center_iff.mp hz g)
  obtain ⟨-, -, -, hlift, -⟩ := full_central_kernel_involution_fixed_component_correspondence
    proj_surjective hK' ha hα (fun x => (conjAut_proj A x).symm)
  set R := L.map (FixedCommutingProduct.fixedSubgroup (conjAut 2 K A)).subtype with hRdef
  have hR : Assembly.IsComponentOf R (FixedCommutingProduct.fixedSubgroup (conjAut 2 K A)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (map_subtype_le L)).2 ?_
    have hRL : R.subgroupOf (FixedCommutingProduct.fixedSubgroup (conjAut 2 K A)) = L :=
      Subgroup.comap_map_eq_self_of_injective (subtype_injective _) L
    rw [hRL]
    exact hL
  obtain ⟨-, hQ, -, -, -, -, ⟨eQR⟩⟩ := hlift R hR
  have hQ' := (isComponentOf_iff_isComponent_subgroupOf hQ.1).1 hQ
  have hAμ : ∀ v w, pairedSympForm K 2 (((linA A : LinearMap.GeneralLinearGroup K
      (Fin 2 ⊕ Fin 2 → K)) : Module.End K (Fin 2 ⊕ Fin 2 → K)) v)
      (((linA A : LinearMap.GeneralLinearGroup K (Fin 2 ⊕ Fin 2 → K)) :
        Module.End K (Fin 2 ⊕ Fin 2 → K)) w) =
        (multiplierUnit A : K) * pairedSympForm K 2 v w := by
    intro v w
    rw [linA_apply, linA_apply, form_similitude (multiplierUnit_spec A)]
  have hQo := psl2CQ_of_component_equiv
    ((MulEquiv.subgroupCongr (show FixedCommutingProduct.fixedSubgroup (conjSp 2 K A) = spCent 2 K A from rfl)).trans
      (spCentEquiv A))
    (fun N hN => psl2_similitudeCentralizer_two hp hp2 hf hK finrank_standard
      pairedSympForm_isAlt SymplecticFlag.pairedSympForm_nondegenerate
      (CatalogueBSymplecticB.matrixLinIso_ne_smul_one _ hAns) c.ne_zero (linA_mul_self hAA)
      hAμ hN) hQ'
  exact Psl2CQ.of_mulEquiv
    (L.equivMapOfInjective (FixedCommutingProduct.fixedSubgroup (conjAut 2 K A)).subtype (subtype_injective _))
    (Psl2CQ.of_centerQuotient_equiv eQR.symm
      (Psl2CQ.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQ.1).symm hQo))

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
