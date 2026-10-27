module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClFix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeZ2
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClTwoU43Aut
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClTwoU43Det
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClF9
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClShape
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFSimCard
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PTCover
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3ClGroup
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OmegaProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem cl_neg_not_mem_of_perfect_comm {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (hdim : Module.finrank (ZMod 3) V = 6)
    {a : V ≃ₗ[ZMod 3] V} (ha : (∀ v, a (a v) = v) ∨ (∀ v, a (a v) = -v)) (ha1 : a ≠ 1)
    (ha2 : a ≠ LinearEquiv.neg (ZMod 3)) {J : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hJ : ⁅J, J⁆ = J) (hc : ∀ g ∈ J, g * a = a * g) : LinearEquiv.neg (ZMod 3) ∉ J := by
  rcases ha with ha | ha
  · exact cl_neg_not_mem_of_involution hdim ha ha1 ha2 hJ hc
  · exact cl_neg_not_mem_of_sq_eq_neg hdim ha hJ hc

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem cl_closureFix_omegaGroup_six_minus (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hs : quadSign Q = -1)
    (hM : ClosureFix ↥(omegaProj hQ)) : ClosureFix ↥(omegaGroup hQ) := by
  have h2 : 2 ≤ Module.finrank (ZMod 3) V := by omega
  haveI : Finite (OGroup Q) := CFSG.ClassicalInvolution.finite_orthogonalGroup_of_finite
  haveI : Finite ↥(omegaGroup hQ) := Subtype.finite
  refine closureFix_of_ne_one (isQuasisimple_omegaGroup_six_minus hQ hdim hs)
    (cl_isFStarGroup_omegaGroup_six_minus hQ hdim hs) ?_
  intro α hα hα1 J hJ
  obtain ⟨γ, hγ, hαeq⟩ := cl_exists_simil_of_mulAut_six_minus hQ hdim hs α hα
  have hsim_fix (ha : (γ : V ≃ₗ[ZMod 3] V) = 1 ∨
      (γ : V ≃ₗ[ZMod 3] V) = LinearEquiv.neg (ZMod 3)) :
      ∀ t : ↥(omegaGroup hQ), simAct Q γ (t : OGroup Q) = (t : OGroup Q) := by
    intro t
    rcases ha with ha | ha
    · apply Subtype.ext
      rw [coe_simAct, ha]
      simp
    · apply Subtype.ext
      rw [coe_simAct, ha]
      ext v
      simp [LinearEquiv.mul_apply, LinearEquiv.neg_apply, map_neg]
  have ha1 : (γ : V ≃ₗ[ZMod 3] V) ≠ 1 := by
    intro ha
    apply hα1
    refine MulEquiv.ext fun t => ?_
    apply Subtype.ext
    rw [hαeq t, hsim_fix (Or.inl ha) t, MulAut.one_apply]
  have ha2 : (γ : V ≃ₗ[ZMod 3] V) ≠ LinearEquiv.neg (ZMod 3) := by
    intro ha
    apply hα1
    refine MulEquiv.ext fun t => ?_
    apply Subtype.ext
    rw [hαeq t, hsim_fix (Or.inr ha) t, MulAut.one_apply]
  let piOmg : ↥(omegaGroup hQ) := ⟨piOrth Q, ff_piOrth_mem_omegaGroup_six_minus hQ hdim hs⟩
  let J0 : Subgroup (V ≃ₗ[ZMod 3] V) :=
    (J.map (omegaGroup hQ).subtype).map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.isQuasisimple.1
  have hJ0perf : ⁅J0, J0⁆ = J0 := by
    have hX : (J.map (omegaGroup hQ).subtype).map
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype = J0 := rfl
    rw [← hX, ← Subgroup.map_commutator (f :=
        (TauCeti.QuadraticMap.orthogonalGroup Q).subtype),
      ← Subgroup.map_commutator (f := (omegaGroup hQ).subtype), hJperf]
  have hcomm : ∀ g ∈ J0, g * (γ : V ≃ₗ[ZMod 3] V) =
      (γ : V ≃ₗ[ZMod 3] V) * g := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    show ((t : ↥(omegaGroup hQ)) : V ≃ₗ[ZMod 3] V) * (γ : V ≃ₗ[ZMod 3] V) =
      (γ : V ≃ₗ[ZMod 3] V) * ((t : ↥(omegaGroup hQ)) : V ≃ₗ[ZMod 3] V)
    have hfix : α t = t := hJ.1 ht
    have heq : ((t : ↥(omegaGroup hQ)) : OGroup Q) = simAct Q γ (t : OGroup Q) := by
      rw [← hαeq t]
      exact (congrArg Subtype.val hfix).symm
    have hcoe : ((t : ↥(omegaGroup hQ)) : V ≃ₗ[ZMod 3] V) =
        (γ : V ≃ₗ[ZMod 3] V) * ((t : ↥(omegaGroup hQ)) : V ≃ₗ[ZMod 3] V) *
          (γ : V ≃ₗ[ZMod 3] V)⁻¹ := by
      have h := congrArg (fun e : OGroup Q => (e : V ≃ₗ[ZMod 3] V)) heq
      rw [coe_simAct] at h
      exact h
    conv_lhs => rw [hcoe]
    group
  have hnegJ0 : LinearEquiv.neg (ZMod 3) ∉ J0 :=
    cl_neg_not_mem_of_perfect_comm hdim hγ ha1 ha2 hJ0perf hcomm
  have hpinot : piOmg ∉ J := by
    intro hpiJ
    apply hnegJ0
    have hpival : ((TauCeti.QuadraticMap.orthogonalGroup Q).subtype
        ((omegaGroup hQ).subtype piOmg) : V ≃ₗ[ZMod 3] V) =
        LinearEquiv.neg (ZMod 3) := by
      apply LinearEquiv.ext
      intro v
      change (piOrth Q : V ≃ₗ[ZMod 3] V) v = LinearEquiv.neg (ZMod 3) v
      rw [coe_piOrth_apply, LinearEquiv.neg_apply]
    rw [← hpival]
    exact Subgroup.mem_map.mpr ⟨(omegaGroup hQ).subtype piOmg,
      Subgroup.mem_map.mpr ⟨piOmg, hpiJ, rfl⟩, rfl⟩
  have hρker : (omegaToProj hQ).ker ≤ Subgroup.center ↥(omegaGroup hQ) := by
    intro m hm
    rw [Subgroup.mem_center_iff]
    intro g
    exact omegaToProj_ker_central hQ hm g
  have hJker : J ⊓ (omegaToProj hQ).ker = ⊥ := by
    apply le_antisymm _ bot_le
    intro t ht
    rw [Subgroup.mem_inf] at ht
    obtain ⟨htJ, htker⟩ := ht
    rcases (omegaToProj_eq_one_iff hQ t).mp htker with h1 | h1
    · exact Subgroup.mem_bot.mpr (Subtype.ext h1)
    · exact absurd (show t = piOmg from Subtype.ext h1) (fun h => hpinot (h ▸ htJ))
  have hinjJ : Function.Injective ((omegaToProj hQ).comp J.subtype) := by
    intro x y hxy
    have h1 : omegaToProj hQ (((x⁻¹ * y : ↥J) : ↥(omegaGroup hQ))) = 1 := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
        show omegaToProj hQ (↑x) = omegaToProj hQ (↑y) from hxy, inv_mul_cancel]
    have hmem : ((x⁻¹ * y : ↥J) : ↥(omegaGroup hQ)) ∈ J ⊓ (omegaToProj hQ).ker :=
      ⟨(x⁻¹ * y).2, MonoidHom.mem_ker.mpr h1⟩
    have hz : ((x⁻¹ * y : ↥J) : ↥(omegaGroup hQ)) = 1 :=
      Subgroup.mem_bot.mp (hJker ▸ hmem)
    exact inv_mul_eq_one.mp (Subtype.ext hz)
  let fJ : ↥J →* ↥(J.map (omegaToProj hQ)) := (omegaToProj hQ).subgroupMap J
  have hfJinj : Function.Injective fJ := by
    intro x y hxy
    exact hinjJ (congrArg Subtype.val hxy)
  let eJ : ↥J ≃* ↥(J.map (omegaToProj hQ)) :=
    MulEquiv.ofBijective fJ ⟨hfJinj, MonoidHom.subgroupMap_surjective _ _⟩
  set abar : MulAut ↥(omegaProj hQ) := ffSimOmegaAct hQ h2 (QuotientGroup.mk γ) with habar
  have hρeq : ∀ t : ↥(omegaGroup hQ), omegaToProj hQ (α t) = abar (omegaToProj hQ t) := by
    intro t
    apply Subtype.ext
    rw [habar, coe_omegaToProj, coe_ffSimOmegaAct, coe_omegaToProj, projSimAct_mk,
      projActAux_toProj, hαeq t]
  have hγsq : γ * γ ∈ piSim Q := by
    rcases hγ with hγ | hγ
    · rw [mem_piSim_iff]
      left
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      ext v
      simpa [LinearEquiv.mul_apply] using hγ v
    · rw [mem_piSim_iff]
      right
      apply Subtype.ext
      rw [Subgroup.coe_mul, coe_orthToSim]
      ext v
      rw [LinearEquiv.mul_apply, coe_piOrth_apply]
      exact hγ v
  have hmk : QuotientGroup.mk γ * QuotientGroup.mk γ = (1 : ProjSim Q) := by
    change ((γ * γ : simGroup Q) : ProjSim Q) = 1
    rw [QuotientGroup.eq_one_iff]
    exact hγsq
  have habar2 : abar * abar = 1 := by
    rw [habar, ← map_mul, hmk, map_one]
  have hcomp1 : IsComponentIn (J.map (omegaToProj hQ))
      ((fixSub α).map (omegaToProj hQ)) :=
    sec63PT_isComponentIn_map (omegaToProj hQ) hρker hJ
  have hCM : (fixSub α).map (omegaToProj hQ) ≤ fixSub abar := by
    intro y hy
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
    rw [mem_fixSub_iff, ← hρeq c, show α c = c from hc]
  have hnorm : (((fixSub α).map (omegaToProj hQ)).subgroupOf (fixSub abar)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCM, Subgroup.le_normalizer_iff]
    intro n hn x hx
    obtain ⟨d, rfl⟩ := omegaToProj_surjective hQ n
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨d * c * d⁻¹, ?_, ?_⟩
    · rw [mem_fixSub_iff]
      have hd' : α d = d ∨ α d = piOmg * d := by
        have h3 : omegaToProj hQ (α d) = omegaToProj hQ d := by
          rw [hρeq d, show abar (omegaToProj hQ d) = omegaToProj hQ d from hn]
        rcases omegaToProj_eq_iff hQ h3 with hd'' | hd''
        · exact Or.inl (Subtype.ext hd''.symm)
        · refine Or.inr (Subtype.ext ?_)
          show ((α d : ↥(omegaGroup hQ)) : OGroup Q) = piOrth Q * (d : OGroup Q)
          have h' : piOrth Q * ((α d : ↥(omegaGroup hQ)) : OGroup Q) = (d : OGroup Q) :=
            hd''.symm
          calc ((α d : ↥(omegaGroup hQ)) : OGroup Q)
              = (1 : OGroup Q) * ((α d : ↥(omegaGroup hQ)) : OGroup Q) := by rw [one_mul]
            _ = (piOrth Q * piOrth Q) * ((α d : ↥(omegaGroup hQ)) : OGroup Q) := by
                  rw [piOrth_mul_self]
            _ = piOrth Q * (piOrth Q * ((α d : ↥(omegaGroup hQ)) : OGroup Q)) := by
                  group
            _ = piOrth Q * (d : OGroup Q) := by rw [h']
      rcases hd' with hd | hd
      · simp only [map_mul, map_inv, hd, show α c = c from hc]
      · have hcen : piOmg * (d * c * d⁻¹) = (d * c * d⁻¹) * piOmg := by
          apply Subtype.ext
          exact (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q))
            (d * c * d⁻¹ : OGroup Q)).symm
        simp only [map_mul, map_inv, hd, show α c = c from hc]
        rw [show (piOmg * d) * c * (piOmg * d)⁻¹ =
            piOmg * (d * c * d⁻¹) * piOmg⁻¹ by group, hcen]
        group
    · simp only [map_mul, map_inv]
  have hcomp : IsComponentIn (J.map (omegaToProj hQ)) (fixSub abar) :=
    IsComponentIn.of_normal hcomp1 hCM hnorm
  have hFmap : InFStar (J.map (omegaToProj hQ)) := hM abar habar2 _ hcomp
  exact isFStarGroup_of_mulEquiv eJ.symm hFmap

theorem asc82ClosureAt_twoU43 (hS : Asc82SchurU43)
    {V₀ : Type} [AddCommGroup V₀] [Module (ZMod 3) V₀] [FiniteDimensional (ZMod 3) V₀]
    {Q₀ : QuadraticForm (ZMod 3) V₀} (hQ₀ : Q₀.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V₀ = 6) (hs : quadSign Q₀ = -1)
    (hM6 : ClosureFix ↥(omegaProj hQ₀)) : Asc82ClosureAt IsTwoU43 := by
  refine asc82ClosureAt_of_closureFix ?_
  intro X _ _ hq hX
  obtain ⟨e⟩ := IsOmegaCover.nonempty_equiv (hS X hq hX)
    (show 2 ≤ 6 by norm_num) hQ₀ hdim hs
  exact closureFix_of_mulEquiv e.symm
    (cl_closureFix_omegaGroup_six_minus hQ₀ hdim hs hM6)

end CFSG.OddStandard.SmallF3.Omega
