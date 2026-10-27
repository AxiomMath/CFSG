module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2Vocab
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClKL2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClShape
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFAutSurj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem fg_simInGStar_of_odd (hQ : Q.Nondegenerate) (h0 : 0 < Module.finrank (ZMod 3) V)
    (hodd : ¬ Even (Module.finrank (ZMod 3) V)) (x : ProjSim Q) : SimInGStar x := by
  obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective x
  have hidx := index_orthogonalGroup_subgroupOf_simGroup hQ h0
  rw [if_neg hodd, Subgroup.index_eq_one] at hidx
  have hγ : (γ : V ≃ₗ[ZMod 3] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    have h : γ ∈ (TauCeti.QuadraticMap.orthogonalGroup Q).subgroupOf (simGroup Q) := by
      rw [hidx]
      exact Subgroup.mem_top γ
    exact h
  refine ⟨toProj Q ⟨γ, hγ⟩, ?_⟩
  rw [projOrthToProjSim_toProj]
  exact congrArg QuotientGroup.mk (Subtype.ext rfl)

theorem fg_closureFix_five (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 5)
    (hs : quadSign Q = 1) : ClosureFix ↥(omegaProj hQ) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite ↥(omegaGroup hQ) := Subtype.finite
  haveI : Finite ↥(omegaProj hQ) :=
    Finite.of_surjective (omegaToProj hQ) (omegaToProj_surjective hQ)
  have hπ : piOrth Q ∉ omegaGroup hQ := by
    rw [piOrth_mem_omegaGroup_iff hQ, hdim]
    exact fun h => (by decide : ¬ Even (5 : ℕ)) h.1
  let e : omegaGroup hQ ≃* omegaProj hQ :=
    MulEquiv.ofBijective (omegaToProj hQ)
      ⟨by
        rw [injective_iff_map_eq_one]
        intro g hg
        rcases (omegaToProj_eq_one_iff hQ g).mp hg with h | h
        · exact Subtype.ext h
        · exact absurd (h ▸ g.2) hπ,
       omegaToProj_surjective hQ⟩
  have hq : CFSG.IsQuasisimple ↥(omegaProj hQ) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e (isQuasisimple_omegaGroup_five hQ hdim)
  have hF : IsFStarGroup ↥(omegaProj hQ) :=
    isFStarGroup_of_mulEquiv e (cl_isFStarGroup_omegaGroup_five hQ hdim)
  have hbij := ffSimOmegaAct_bijective_five hQ hdim hs
  refine closureFix_of_ne_one hq hF ?_
  intro α hα hα1 J hJ
  obtain ⟨x, rfl⟩ := hbij.2 α
  have hx2 : x * x = 1 := hbij.1 (by rw [map_mul, map_one]; exact hα)
  obtain ⟨y, hy⟩ := fg_simInGStar_of_odd hQ (by omega) (by rw [hdim]; decide) x
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective y
  have hαA : ffSimOmegaAct hQ h2 x = projAut hQ A := by
    rw [← hy, ffSimOmegaAct_projOrthToProjSim]
    rfl
  have hy' : projOrthToProjSim Q (toProj Q A) = x := hy
  have hy2 : toProj Q A * toProj Q A = 1 :=
    projOrthToProjSim_injective (by rw [map_mul, hy', hx2, map_one])
  have hAAmem : A * A ∈ piGroup Q :=
    (QuotientGroup.eq_one_iff (A * A)).mp (by
      show toProj Q (A * A) = 1
      rw [map_mul]
      exact hy2)
  have hAA : A * A = 1 := by
    rcases mem_piGroup_iff.mp hAAmem with h | h
    · exact h
    · exfalso
      have hEven := ((exists_mul_self_eq_piOrth_iff hQ).mp ⟨A, h⟩).1
      rw [hdim] at hEven
      exact (by norm_num : ¬ Even (5 : ℕ)) hEven
  have hA1 : A ≠ 1 := by
    intro h1
    exact hα1 (by rw [hαA, h1]; simp [projAut])
  have hπ1 : toProj Q (piOrth Q) = 1 := toProj_piOrth
  have hAπ : A ≠ piOrth Q := by
    intro hπ'
    exact hα1 (by rw [hαA, hπ']; simp [projAut, hπ1])
  have hfix_ne : fixSp A ≠ ⊥ := by
    intro hfix
    apply hAπ
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have htop : commSp A = ⊤ := by
      have hc : fixSp A ⊔ commSp A = ⊤ := codisjoint_iff.mp
        (isCompl_fixSp_commSp (Q := Q) hAA).2
      rwa [hfix, bot_sup_eq] at hc
    have hv : v ∈ commSp A := by rw [htop]; exact Submodule.mem_top
    rw [mem_commSp_iff hAA] at hv
    rw [coe_piOrth_apply]
    exact hv
  have hcomm_ne : commSp A ≠ ⊥ := fun h => hA1 ((commSp_eq_bot_iff hAA).mp h)
  have hW : 0 < Module.finrank (ZMod 3) (fixSp A) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hfix_ne (Submodule.finrank_eq_zero.mp h0)
  have hU : 0 < Module.finrank (ZMod 3) (commSp A) := by
    rw [Nat.pos_iff_ne_zero]
    intro h0
    exact hcomm_ne (Submodule.finrank_eq_zero.mp h0)
  rw [hαA] at hJ
  exact cl_inFStar_of_isComponentIn_fix hQ (by omega) hAA hW hU hJ

end CFSG.OddStandard.SmallF3.Omega
