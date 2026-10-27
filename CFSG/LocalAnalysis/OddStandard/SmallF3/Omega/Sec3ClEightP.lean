module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutAut
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClKL2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClEightProj
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFShapesAux

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem finrank_fixSp_commSp_pos_of_ne_one {x : OGroup Q} (hxx : x * x = 1)
    (hx1 : x ≠ 1) (hxπ : x ≠ piOrth Q) :
    0 < Module.finrank (ZMod 3) (fixSp x) ∧
      0 < Module.finrank (ZMod 3) (commSp x) := by
  have hcomm : commSp x ≠ ⊥ := by
    intro h
    exact hx1 ((commSp_eq_bot_iff hxx).mp h)
  have hfix : fixSp x ≠ ⊥ := by
    intro hfix
    apply hxπ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have htop : commSp x = ⊤ := by
      have hc : fixSp x ⊔ commSp x = ⊤ :=
        codisjoint_iff.mp (isCompl_fixSp_commSp (Q := Q) hxx).2
      rwa [hfix, bot_sup_eq] at hc
    have hv : v ∈ commSp x := by rw [htop]; exact Submodule.mem_top
    rw [mem_commSp_iff hxx] at hv
    rw [coe_piOrth_apply]
    exact hv
  refine ⟨?_, ?_⟩
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hfix (Submodule.finrank_eq_zero.mp h0)
  · rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hcomm (Submodule.finrank_eq_zero.mp h0)

private theorem projAut_piOrth_eq_one (hQ : Q.Nondegenerate) :
    projAut hQ (piOrth Q) = 1 := by
  rw [projAut, toProj_piOrth, map_one]

theorem cl_closureFix_omegaProj_eight_plus (hA : Asc82OmegaPlusAutInvolutions)
    (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 8) (hs : quadSign Q = 1) :
    ClosureFix ↥(omegaProj hQ) := by
  have hmodel : LieModel ↥(omegaProj hQ) .POmegaPlus 4 3 1 :=
    isOmegaStar_eight_plus_iff.mp
      ⟨V, inferInstance, inferInstance, inferInstance, Q, hQ, hdim, hs, ⟨MulEquiv.refl _⟩⟩
  have hsimple : IsSimpleGroup ↥(omegaProj hQ) :=
    (CFSG.LieType.Simplicity.fam_classical_converse ↥(omegaProj hQ)
      ⟨.POmegaPlus, 4, 3, 1,
        hmodel.statedClassicalModel_of_ne_zero (by norm_num : (4 : ℕ) ≠ 0)⟩).2.2
  have hcard : Nat.card ↥(omegaProj hQ) = 4952179814400 := by
    rw [hmodel.card_eq_lieOrd (by norm_num : (4 : ℕ) ≠ 0)]
    decide +kernel
  haveI : Finite ↥(omegaProj hQ) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  haveI : IsSimpleGroup ↥(omegaProj hQ) := hsimple
  have hnotprime : ¬ (4952179814400).Prime := by
    intro hp
    have hodd := hp.odd_of_ne_two (by norm_num)
    exact Nat.not_even_iff_odd.mpr hodd (by norm_num : Even 4952179814400)
  have hnc : ∃ a b : ↥(omegaProj hQ), a * b ≠ b * a :=
    ff_noncomm_of_simple_card hsimple (by rw [hcard]; exact hnotprime)
  have hqcenter :=
    CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := ↥(omegaProj hQ)) hnc
  have hq : CFSG.IsQuasisimple ↥(omegaProj hQ) := hqcenter.1
  have hcenter : Subgroup.center ↥(omegaProj hQ) = ⊥ := hqcenter.2
  have hsmall : SmallF3OmegaQuotient (↥(omegaProj hQ) ⧸ oddCore ↥(omegaProj hQ)) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (ff_lieModel_quot_oddCore hmodel hsimple (by rw [hcard]; norm_num))))))
  have hF : IsFStarGroup ↥(omegaProj hQ) := Or.inl ⟨hq, Or.inl hsmall⟩
  refine closureFix_of_ne_one hq hF ?_
  intro α hα hα1 J hJ
  by_cases hinn : ∃ p : ↥(omegaProj hQ), α = MulAut.conj p
  · obtain ⟨p, hp⟩ := hinn
    have hpp : p * p = 1 := by
      have hc : MulAut.conj (p * p) = 1 := by
        rw [map_mul, ← hp]
        exact hα
      have hcen : p * p ∈ Subgroup.center ↥(omegaProj hQ) := by
        rw [Subgroup.mem_center_iff]
        intro z
        have hz : (p * p) * z * (p * p)⁻¹ = z := by
          simpa only [MulAut.conj_apply, MulAut.one_apply] using
            congrArg (fun f : MulAut ↥(omegaProj hQ) => f z) hc
        exact (mul_inv_eq_iff_eq_mul.mp hz).symm
      rw [hcenter, Subgroup.mem_bot] at hcen
      exact hcen
    obtain ⟨y, rfl⟩ := omegaToProj_surjective hQ p
    have hαeq : α = projAut hQ y := by
      rw [hp, ← MulAut.conjNormal_val]
      rfl
    have hmul : omegaToProj hQ (y * y) = 1 := by rw [map_mul]; exact hpp
    rcases (omegaToProj_eq_one_iff hQ (y * y)).mp hmul with h1 | hpi
    · have hyy : (y : OGroup Q) * (y : OGroup Q) = 1 := by simpa using h1
      have hy1 : (y : OGroup Q) ≠ 1 := by
        intro h
        apply hα1
        rw [hαeq, h]
        simp [projAut]
      have hyπ : (y : OGroup Q) ≠ piOrth Q := by
        intro h
        apply hα1
        rw [hαeq, h]
        exact projAut_piOrth_eq_one hQ
      obtain ⟨hW, hU⟩ := finrank_fixSp_commSp_pos_of_ne_one hyy hy1 hyπ
      exact cl_inFStar_of_isComponentIn_fix hQ (by omega) hyy hW hU (by rwa [hαeq] at hJ)
    · have hyy : (y : OGroup Q) * (y : OGroup Q) = piOrth Q := by simpa using hpi
      exact cl_inFStar_of_isComponentIn_fix_proj hQ hdim hs hyy (by rwa [hαeq] at hJ)
  · obtain ⟨β, x, hxx, hxΩ, hβ⟩ := hA V Q hQ hdim hs α hα hinn
    have hx1 : x ≠ 1 := by
      intro h
      rw [h] at hxΩ
      exact hxΩ (Subgroup.one_mem (omegaGroup hQ))
    have hxπ : x ≠ piOrth Q := by
      intro h
      exact hxΩ (h ▸ piOrth_mem_omegaGroup_eight hQ hdim hs)
    obtain ⟨hW, hU⟩ := finrank_fixSp_commSp_pos_of_ne_one hxx hx1 hxπ
    refine inFStar_of_isComponentIn_fixSub_conj α β ?_ hJ
    intro J hJ'
    rw [hβ] at hJ'
    exact cl_inFStar_of_isComponentIn_fix hQ (by omega) hxx hW hU
      (by simpa [projAut] using hJ')

theorem asc82ClosureAt_eight_plus (hA : Asc82OmegaPlusAutInvolutions) :
    Asc82ClosureAt ShapeO8P := by
  exact asc82ClosureAt_of_omegaStar_all (P := ShapeO8P) (n := 8) (ε := 1)
    (fun X _ h => isOmegaStar_of_lieModel_plus h)
    (fun V _ _ _ Q hQ hdim hs => cl_closureFix_omegaProj_eight_plus hA hQ hdim hs)

theorem asc82OmegaPlusClosure_holds (hA : Asc82OmegaPlusAutInvolutions) :
    Asc82OmegaPlusClosure :=
  asc82OmegaPlusClosure_iff_at.mpr (asc82ClosureAt_eight_plus hA)

end CFSG.OddStandard.SmallF3.Omega
