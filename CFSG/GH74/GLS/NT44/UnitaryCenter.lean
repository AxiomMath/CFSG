module

public import CFSG.GH74.GLS.NT44.ActualCoverModel
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourAutomorphisms
import CFSG.GH74.GLS.NT44.ActualCover
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryLift

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open CFSG
open CFSG.GH74.GLS
open CFSG.LieType.Multipliers
open CFSG.ComponentClassification.GrSLit
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.ComponentClassification.PSL3Four

theorem inverts_center_of_projective_unitary
    (Phi : MulAut CFSG.GH74.GLS.NT44.FullTwoCover ≃*
      MulAut CFSG.ComponentClassification.PSL3Four.S)
    (hPhi : ∀ (beta : MulAut CFSG.GH74.GLS.NT44.FullTwoCover)
      (x : CFSG.GH74.GLS.NT44.FullTwoCover),
      CFSG.GH74.GLS.NT44.fullTwoCoverToS (beta x) =
        Phi beta (CFSG.GH74.GLS.NT44.fullTwoCoverToS x))
    {alpha : MulAut CFSG.GH74.GLS.NT44.FullTwoCover}
    (hunitary : IsConj (Phi alpha)
      (CFSG.ComponentClassification.PSL3Four.conjAutS
        CFSG.ComponentClassification.PSL3Four.r₄R)) :
    ∀ z ∈ Subgroup.center CFSG.GH74.GLS.NT44.FullTwoCover, alpha z = z⁻¹ := by
  intro z hz
  obtain ⟨-, -, -, -, hqsurj_mk, hpi_surj, -, hpi_ker_center, hpi_ker_card, -,
    -, -, -⟩ := modelStructure
  let q : FullTwoCover →* Equiv.Perm (Fin 42) :=
    (Subgroup.subtype S).comp fullTwoCoverToS
  let l : L34.Cover →* FullTwoCover := quotientMk
  let beta : MulAut FullTwoCover := Phi.symm (conjAutS r₄R)
  have hqS : ∀ e, q e ∈ S := by
    intro e
    simpa only [q, MonoidHom.comp_apply, Subgroup.subtype_apply] using
      (fullTwoCoverToS e).2
  have hqsurj : ∀ s ∈ S, ∃ e, q e = s := by
    intro s hs
    obtain ⟨e, he⟩ := hpi_surj (⟨s, hs⟩ : S)
    refine ⟨e, ?_⟩
    simpa only [q, MonoidHom.comp_apply, Subgroup.subtype_apply] using
      congrArg Subtype.val he
  have hqker : q.ker = Subgroup.center FullTwoCover := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective fullTwoCoverToS (Subgroup.subtype S)
      Subtype.coe_injective]
    exact hpi_ker_center
  have hqker' : q.ker = fullTwoCoverToS.ker := by
    rw [hqker]
    exact hpi_ker_center.symm
  have hqcard : Nat.card ↥q.ker = 16 := by
    rw [hqker']
    exact hpi_ker_card
  have hthree : ∀ e ∈ q.ker, e ^ 3 = 1 → e = 1 := by
    intro e he he3
    have hdiv16 : orderOf e ∣ 16 := by
      rw [← hqcard]
      exact Subgroup.orderOf_dvd_natCard q.ker he
    have hdiv3 : orderOf e ∣ 3 := orderOf_dvd_of_pow_eq_one he3
    have hcop : Nat.Coprime 16 3 := by norm_num
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdiv16 hdiv3)
  have hql : q.comp l = L34Facts.sigma := by
    apply MonoidHom.ext
    intro c
    have h1 : fullTwoCoverToS (quotientMk c) = sigmaS c := by
      rw [← MonoidHom.comp_apply, fullTwoCoverToS_comp_quotientMk]
    simpa only [q, l, sigmaS, MonoidHom.comp_apply, Subgroup.subtype_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.subgroupCongr_apply,
      MonoidHom.coe_rangeRestrict] using
      congrArg Subtype.val h1
  have hlsurj : Function.Surjective l := by
    simpa only [l] using hqsurj_mk
  have hqβ : ∀ e, q (beta e) = r₄ * q e * r₄⁻¹ := by
    intro e
    have hbeta : fullTwoCoverToS (beta e) = conjAutS r₄R (fullTwoCoverToS e) := by
      have h := hPhi (Phi.symm (conjAutS r₄R)) e
      rw [show Phi (Phi.symm (conjAutS r₄R)) = conjAutS r₄R from
        Phi.apply_symm_apply (conjAutS r₄R)] at h
      exact h
    simpa [q, MonoidHom.comp_apply, conjAutS_apply, r₄R] using
      congrArg Subtype.val hbeta
  have hU : IsUSetting q l beta :=
    { qS := hqS
      qsurj := hqsurj
      ker := hqker
      three := hthree
      ql := hql
      lsurj := hlsurj
      qβ := hqβ }
  obtain ⟨gamma, hgamma⟩ := isConj_iff.mp hunitary
  let delta : MulAut FullTwoCover := Phi.symm gamma
  have hdelta : delta * alpha * delta⁻¹ = beta := by
    apply Phi.injective
    calc
      Phi (delta * alpha * delta⁻¹) = gamma * Phi alpha * gamma⁻¹ := by
        simp only [map_mul, map_inv]
        exact congrArg (fun f : MulAut S => f * Phi alpha * f⁻¹)
          (show Phi delta = gamma from Phi.apply_symm_apply gamma)
      _ = conjAutS r₄R := hgamma
      _ = Phi beta := (Phi.apply_symm_apply (conjAutS r₄R)).symm
  have hcenter_map :
      (Subgroup.center FullTwoCover).map
          (delta : FullTwoCover →* FullTwoCover) =
        Subgroup.center FullTwoCover :=
    Subgroup.map_center_eq delta
  have hdeltacenter : ∀ {w : FullTwoCover},
      w ∈ Subgroup.center FullTwoCover →
        delta w ∈ Subgroup.center FullTwoCover := by
    intro w hw
    rw [← hcenter_map]
    exact Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
  have hdeltaz_ker : delta z ∈ q.ker := by
    rw [hqker]
    exact hdeltacenter hz
  have hbetadeltaz : beta (delta z) = (delta z)⁻¹ :=
    CFSG.ComponentClassification.GrSLit.L34Facts.IsUSetting.beta_ker hU hdeltaz_ker
  have halpha : delta (alpha z) = delta (z⁻¹) := by
    have h := congrArg (fun f : MulAut FullTwoCover => f (delta z)) hdelta
    change delta (alpha (delta.symm (delta z))) = beta (delta z) at h
    rw [delta.symm_apply_apply] at h
    rw [hbetadeltaz, ← map_inv] at h
    exact h
  exact delta.injective halpha

end CFSG.GH74.GLS.NT44
