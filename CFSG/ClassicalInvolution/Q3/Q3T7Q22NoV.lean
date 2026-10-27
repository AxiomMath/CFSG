module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutSp
public import CFSG.ClassicalInvolution.Asc77.AscS22A

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S22

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.LieType.Universal
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.FrameVertex
  CFSG.ClassicalInvolution.Models.SymplecticPairs
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag


theorem noV_psp2_three (hadm : StatedLieAdmissible .PSp 2 3 1)
    {H : Type} [Group H] [Finite H] (ψ : (modelUniv .PSp 2 3 1 Fact.out).K →* H)
    (R R' : Subgroup (modelUniv .PSp 2 3 1 Fact.out).K)
    (x x' : (modelUniv .PSp 2 3 1 Fact.out).K)
    (hpair : TwinPairOn .PSp (modelUniv .PSp 2 3 1 Fact.out) ψ R R' x x')
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) : False := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField 1 (by norm_num)
  have hF : Nat.card (GaloisField 3 1) = 3 := by
    simpa using GaloisField.card 3 1 one_ne_zero
  have : Group.IsPerfect (modelUniv .PSp 2 3 1 Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSp 2 3 1 Fact.out trivial hadm).1.1
  refine CFSG.ClassicalInvolution.Asc77.S22.noV_of_autSq (t := .PSp) (modelUniv .PSp 2 3 1 Fact.out)
    (proj 2 (GaloisField 3 1)) proj_surjective ?_ ?_ ?_ ψ R R' x x' hpair v hvR hvR' hvv
  · exact ker_proj.trans (CFSG.LieType.Universal.Symplectic.center_eq 2 _).symm
  · exact fund_noncentral_modelUniv trivial hadm (by simp)
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ' _
    exact Q3TIY.psp4_autVac3 hF h2
      ((exists_isLongRootSp2_iff h2 R).mpr ((mem_fundamentalSubgroups_PSp_iff hadm R).mp hR))
      ((exists_isLongRootSp2_iff h2 R').mpr ((mem_fundamentalSubgroups_PSp_iff hadm R').mp hR'))
      hne hxR hx2 hx1 hx'R' hx'2 hx'1 hc β hβ hβ'

theorem noV_of_e4 (t : StatedLieTag) (k e : ℕ) (he : e = 1)
    (hadm : StatedLieAdmissible t k 3 e)
    (hE4 : (t = .PSp ∧ k = 2) ∨ (t = .PSL ∧ k = 4 ∧ 3 ^ e % 4 = 3) ∨
      (t = .PSU ∧ k = 4 ∧ 3 ^ e % 4 = 1))
    {H : Type} [Group H] [Finite H] (ψ : (modelUniv t k 3 e Fact.out).K →* H)
    (R R' : Subgroup (modelUniv t k 3 e Fact.out).K) (x x' : (modelUniv t k 3 e Fact.out).K)
    (hpair : TwinPairOn t (modelUniv t k 3 e Fact.out) ψ R R' x x')
    (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) : False := by
  subst he
  rcases hE4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
  · exact noV_psp2_three hadm ψ R R' x x' hpair v hvR hvR' hvv
  · exact CFSG.ClassicalInvolution.Asc77.S22.noV_psl4_three (by norm_num) h hadm ψ R R' x x'
      hpair v hvR hvR' hvv
  · norm_num at h

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.S22
