module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModel
public import CFSG.RankThree.PartOne.S12.TerminalWeylDet

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec9t_det_involution {t : OGroup Q} (htt : t * t = 1) :
    QuadraticMap.orthogonalDet Q t = (-1 : (ZMod 3)ˣ) ^ invDim t := by
  have hss : (t : V ≃ₗ[ZMod 3] V) * (t : V ≃ₗ[ZMod 3] V) = 1 := by
    simpa using congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) htt
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have hker : commSp t =
      LinearMap.ker (((t : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) + LinearMap.id) := by
    ext v
    rw [mem_commSp_iff htt, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply,
      add_eq_zero_iff_eq_neg, LinearEquiv.coe_coe]
  have hfin : invDim t = Module.finrank (ZMod 3)
      (LinearMap.ker (((t : V ≃ₗ[ZMod 3] V) : V →ₗ[ZMod 3] V) + LinearMap.id)) := by
    simp only [invDim]
    rw [hker]
  apply Units.ext
  rw [QuadraticMap.orthogonalDet_apply, LinearEquiv.coe_det, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one,
    CFSG.RankThree.PartOne.TerminalDet.det_involution (t : V ≃ₗ[ZMod 3] V) hss h2, hfin]

theorem sec9t_not_simInOmegaStar (hQ : Q.Nondegenerate)
    (h6 : Module.finrank (ZMod 3) V = 6) {x : ProjSim Q} (h : SimHasDim x 3) :
    ¬ SimInOmegaStar hQ x := by
  rintro ⟨y, hy, hyx⟩
  obtain ⟨t, htt, ht3, htx⟩ := h
  obtain ⟨g, hg, hgy⟩ := (mem_omegaProj_iff hQ).mp hy
  have hdetg : QuadraticMap.orthogonalDet Q g = 1 := by
    have h1 : CFSG.ClassicalInvolution.detSpinorNorm hQ g = 1 := (mem_omegaGroup_iff hQ).mp hg
    simpa [CFSG.ClassicalInvolution.detSpinorNorm_apply] using congrArg Prod.fst h1
  have hgt : toProj Q g = toProj Q t :=
    projOrthToProjSim_injective (by simp only [hgy, hyx, htx])
  have hpi : QuadraticMap.orthogonalDet Q (piOrth Q) = 1 := by
    rw [sec9t_det_involution piOrth_mul_self]
    have hdim : invDim (piOrth Q) = Module.finrank (ZMod 3) V := by
      have := congrArg Prod.fst (invType_piOrth hQ)
      simpa only [invType] using this
    rw [hdim, h6]
    decide
  have hcases : g = t ∨ g = piOrth Q * t := by
    have hmem : g * t⁻¹ ∈ (toProj Q).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hgt, mul_inv_cancel]
    rw [QuotientGroup.ker_mk'] at hmem
    rcases mem_piGroup_iff.mp hmem with h1 | h1
    · left
      have := congrArg (fun z => z * t) h1
      simpa [mul_assoc] using this
    · right
      have := congrArg (fun z => z * t) h1
      simpa [mul_assoc] using this
  have hdet : QuadraticMap.orthogonalDet Q g = -1 := by
    rcases hcases with rfl | hgpi
    · rw [sec9t_det_involution htt, ht3]
      decide
    · rw [hgpi, map_mul, hpi, one_mul, sec9t_det_involution htt, ht3]
      decide
  rw [hdetg] at hdet
  exact (by decide : (1 : (ZMod 3)ˣ) ≠ -1) hdet

theorem sec9t_i3_outer : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
    ∀ s : G, s ∈ normalizer (L : Set G) → (∃ α : ℤˣ, InducesTypeSome L s 6 (-1) 3 α) →
      ¬ InnerOn L s := by
  intro G _ _ L hL s hs h3 hin
  obtain ⟨V, _, _, _, Q, hQ, hd, hs6, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus hL
  have hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := ⟨hd, hs6⟩
  have hLperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  obtain ⟨α, h3α⟩ := h3
  exact sec9t_not_simInOmegaStar hQ hd (simHasDim_of_inducesTypeSome hm e hs h3α)
    ((innerOn_iff_simInOmegaStar hm e hLperf hs).mp hin)

end CFSG.OddStandard.SmallF3.Omega
