module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKCenter
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKFj53
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKInner
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FKKGTrans
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGD4Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutAut
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FJKGAIso
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Inj
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Pocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34Syl
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Standard

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open CFSG.Blueprint
open CFSG.LieType.Universal.Spin (quadPlus nondegenerate_quadPlus)

private theorem fk_finrank_eight : Module.finrank (ZMod 3) (Fin 4 ⊕ Fin 4 → ZMod 3) = 8 := by
  rw [Module.finrank_fintype_fun_eq_card]
  decide

theorem fk_involution_conj (hA : Asc82OmegaPlusAutInvolutions)
    (α : MulAut (omegaProj (nondegenerate_quadPlus 4 (ZMod 3)))) (hα : α * α = 1) :
    ∃ (τ : MulAut (omegaProj (nondegenerate_quadPlus 4 (ZMod 3))))
      (s : OGroup (quadPlus 4 (ZMod 3))), s * s = 1 ∧
        τ * α * τ⁻¹ = projAut (nondegenerate_quadPlus 4 (ZMod 3)) s := by
  by_cases hinn : ∃ p : omegaProj (nondegenerate_quadPlus 4 (ZMod 3)), α = MulAut.conj p
  · obtain ⟨p, rfl⟩ := hinn
    have hpp : p * p = 1 := by
      have hc : MulAut.conj (p * p) = 1 := by
        rw [map_mul]
        exact hα
      have hcen : p * p ∈ Subgroup.center ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) := by
        rw [Subgroup.mem_center_iff]
        intro z
        have hz : (p * p) * z * (p * p)⁻¹ = z := by
          simpa only [MulAut.conj_apply, MulAut.one_apply] using
            congrArg (fun f : MulAut ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) => f z) hc
        exact (mul_inv_eq_iff_eq_mul.mp hz).symm
      rw [fk_center_omegaProj, Subgroup.mem_bot] at hcen
      exact hcen
    exact fkInner_reduce p hpp
  · obtain ⟨β, x, hxx, -, hβ⟩ := hA (Fin 4 ⊕ Fin 4 → ZMod 3) (quadPlus 4 (ZMod 3))
      (nondegenerate_quadPlus 4 (ZMod 3)) fk_finrank_eight (quadSign_quadPlus 4) α hα hinn
    refine ⟨β⁻¹, x, hxx, ?_⟩
    rw [inv_inv]
    exact hβ

theorem fkKGAAt_omegaProj_eight (hA : Asc82OmegaPlusAutInvolutions) :
    FJKGAAt ↥(omegaProj (nondegenerate_quadPlus 4 (ZMod 3))) :=
  fkKGAAt_of_isomInvConj (nondegenerate_quadPlus 4 (ZMod 3)) (by rw [fk_finrank_eight])
    (fun _ hs => fkFj53 (nondegenerate_quadPlus 4 (ZMod 3)) hs)
    (fun α hα => fk_involution_conj hA α hα)

theorem fkKGAAt_of_lieModel_plus (hA : Asc82OmegaPlusAutInvolutions) {Y : Type} [Group Y]
    (h : LieModel Y .POmegaPlus 4 3 1) : FJKGAAt Y := by
  obtain ⟨f⟩ := (isOmegaStar_of_lieModel_plus h).nonempty_equiv (by norm_num : 2 ≤ 8)
    (nondegenerate_quadPlus 4 (ZMod 3)) fk_finrank_eight (quadSign_quadPlus 4)
  exact fjKGAAt_of_mulEquiv f.symm (fkKGAAt_omegaProj_eight hA)

theorem asc82CoreKGAHardD4_of (hA : Asc82OmegaPlusAutInvolutions) : Asc82CoreKGAHardD4 := by
  intro Y _ _ hY _
  exact fkKGAAt_of_lieModel_plus hA hY

end CFSG.OddStandard.SmallF3.Omega
