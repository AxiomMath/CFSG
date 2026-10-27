module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6MFixHom
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux7

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

private theorem toSign_injective' {a b : (ZMod 3)ˣ} (h : toSign a = toSign b) : a = b := by
  revert a b
  decide

private theorem ff6m_invDim_reflPair (hQ : Q.Nondegenerate) {a b : V} (ha : Q a ≠ 0)
    (hb : Q b ≠ 0) (hab : polar Q a b = 0) :
    invDim (reflOf Q a ha * reflOf Q b hb) = 2 := by
  have haa : reflOf Q a ha * reflOf Q a ha = 1 := reflOf_mul_self a ha
  have hbb : reflOf Q b hb * reflOf Q b hb = 1 := reflOf_mul_self b hb
  have horth : ∀ x ∈ commSp (reflOf Q a ha), ∀ y ∈ commSp (reflOf Q b hb),
      polar Q x y = 0 := by
    intro x hx y hy
    rw [ff_commSp_reflOf hQ ha, Submodule.mem_span_singleton] at hx
    rw [ff_commSp_reflOf hQ hb, Submodule.mem_span_singleton] at hy
    obtain ⟨kx, rfl⟩ := hx
    obtain ⟨ky, rfl⟩ := hy
    rw [QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hab, smul_zero, smul_zero]
  have h : invDim (reflOf Q a ha * reflOf Q b hb) =
      invDim (reflOf Q a ha) + invDim (reflOf Q b hb) :=
    congrArg Prod.fst (invType_mul_of_orth hQ haa hbb horth)
  rw [show invDim (reflOf Q a ha) = 1 from
        congrArg Prod.fst (ff_invType_reflOf hQ ha),
      show invDim (reflOf Q b hb) = 1 from
        congrArg Prod.fst (ff_invType_reflOf hQ hb)] at h
  omega

theorem ff6m_frameNorm_eq (hQ : Q.Nondegenerate) {t : OGroup Q} (htt : t * t = 1)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {α : ℤˣ}
    (hty : invType t = (3, α)) :
    (frameNorm (Q.restrict (fixSp t)) : ZMod 3) =
      (frameNorm (Q.restrict (commSp t)) : ZMod 3) := by
  have hWdim : Module.finrank (ZMod 3) (commSp t) = 3 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hUdim : Module.finrank (ZMod 3) (fixSp t) = 3 := by
    have := finrank_fixSp_add_finrank_commSp (Q := Q) t
    omega
  have h := quadSign_eq_fixSp_commSp hQ htt
  rw [hsgn, hUdim, hWdim] at h
  have h9 : (-1 : ℤˣ) ^ (3 * 3) = -1 := by decide
  rw [h9] at h
  have hsign : quadSign (Q.restrict (fixSp t)) = quadSign (Q.restrict (commSp t)) := by
    revert h
    generalize quadSign (Q.restrict (fixSp t)) = sU
    generalize quadSign (Q.restrict (commSp t)) = sW
    revert sU sW
    decide
  have hunit : frameNorm (Q.restrict (fixSp t)) = frameNorm (Q.restrict (commSp t)) := by
    apply toSign_injective'
    rw [toSign_frameNorm, toSign_frameNorm, hsign]
  exact congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) hunit

theorem ff6m_K3_cover_of_data (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1) {t : OGroup Q} (htt : t * t = 1) {c : ZMod 3} (hc : c ≠ 0)
    {u v u' v' : V} (hu : Q u = c) (hv : Q v = c) (hu' : Q u' = c) (hv' : Q v' = c)
    (huv : polar Q u v = 0) (huu' : polar Q u u' = 0) (huv' : polar Q u v' = 0)
    (hvu' : polar Q v u' = 0) (hvv' : polar Q v v' = 0) (hu'v' : polar Q u' v' = 0)
    (htu : (t : V ≃ₗ[ZMod 3] V) u = u) (htv : (t : V ≃ₗ[ZMod 3] V) v = v)
    (htu' : (t : V ≃ₗ[ZMod 3] V) u' = -u') (htv' : (t : V ≃ₗ[ZMod 3] V) v' = -v')
    {σ : OGroup Q} (hσΩ : σ ∈ omegaGroup hQ) (hσ3 : σ ^ 3 = 1) (hσt : σ * t = t * σ)
    (hσv : (σ : V ≃ₗ[ZMod 3] V) v = u) (hσv' : (σ : V ≃ₗ[ZMod 3] V) v' = u') :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoRes (ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t))) ∧
      w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (projOrthToProjSim Q (toProj Q t)) a * a⁻¹ = w := by
  classical
  have hune : Q u ≠ 0 := by rw [hu]; exact hc
  have hvne : Q v ≠ 0 := by rw [hv]; exact hc
  have hu'ne : Q u' ≠ 0 := by rw [hu']; exact hc
  have hv'ne : Q v' ≠ 0 := by rw [hv']; exact hc
  have hvu : polar Q v u = 0 := (QuadraticMap.polar_comm Q v u).trans huv
  have hu'v : polar Q u' v = 0 := (QuadraticMap.polar_comm Q u' v).trans hvu'
  have hv'v : polar Q v' v = 0 := (QuadraticMap.polar_comm Q v' v).trans hvv'
  have hv'u' : polar Q v' u' = 0 := (QuadraticMap.polar_comm Q v' u').trans hu'v'
  have hcomm := ff_k3_commutator (t := t) hc hu hv hu' hv' huv huu' huv' hvu' hvv' hu'v'
    htu htv htu' htv'
  obtain ⟨a₀, ha₀def⟩ : ∃ a : OGroup Q,
      a = reflTot Q (u + u') * reflTot Q (v + v') := ⟨_, rfl⟩
  rw [← ha₀def] at hcomm
  obtain ⟨g₂, hg₂def⟩ : ∃ g : OGroup Q, g = reflTot Q u * reflTot Q u' := ⟨_, rfl⟩
  obtain ⟨g₃, hg₃def⟩ : ∃ g : OGroup Q, g = reflTot Q v * reflTot Q v' := ⟨_, rfl⟩
  have hw_comm : t * a₀ * t⁻¹ * a₀⁻¹ = g₂ * g₃ := by
    rw [hcomm, hg₂def, hg₃def]
    calc reflTot Q u * reflTot Q v * (reflTot Q u' * reflTot Q v')
        = reflTot Q u * (reflTot Q v * reflTot Q u') * reflTot Q v' := by group
      _ = reflTot Q u * (reflTot Q u' * reflTot Q v) * reflTot Q v' := by
          rw [reflTot_comm hvne hu'ne hvu']
      _ = reflTot Q u * reflTot Q u' * (reflTot Q v * reflTot Q v') := by group
  have hg₂r : g₂ = reflOf Q u hune * reflOf Q u' hu'ne := by
    rw [hg₂def, reflTot_of_ne hune, reflTot_of_ne hu'ne]
  have hg₃r : g₃ = reflOf Q v hvne * reflOf Q v' hv'ne := by
    rw [hg₃def, reflTot_of_ne hvne, reflTot_of_ne hv'ne]
  have hg₂sq : g₂ * g₂ = 1 := by rw [hg₂def]; exact ff_k3_pair_sq hune hu'ne huu'
  have hg₃sq : g₃ * g₃ = 1 := by rw [hg₃def]; exact ff_k3_pair_sq hvne hv'ne hvv'
  have horth : ∀ x ∈ commSp g₂, ∀ y ∈ commSp g₃, polar Q x y = 0 := by
    intro x hx y hy
    rw [hg₂r, commSp_reflOf_mul_reflOf_of_orth hQ u u' hune hu'ne huu'] at hx
    rw [hg₃r, commSp_reflOf_mul_reflOf_of_orth hQ v v' hvne hv'ne hvv'] at hy
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hx
    obtain ⟨d₁, d₂, rfl⟩ := Submodule.mem_span_pair.mp hy
    simp only [QuadraticMap.polar_add_left, QuadraticMap.polar_add_right,
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right]
    rw [huv, huv', hu'v, hu'v']
    ring
  have hdimg₂ : invDim g₂ = 2 := by
    rw [hg₂r]; exact ff6m_invDim_reflPair hQ hune hu'ne huu'
  have hdimg₃ : invDim g₃ = 2 := by
    rw [hg₃r]; exact ff6m_invDim_reflPair hQ hvne hv'ne hvv'
  have hdimg23 : invDim (g₂ * g₃) = 4 := by
    have h : invDim (g₂ * g₃) = invDim g₂ + invDim g₃ :=
      congrArg Prod.fst (invType_mul_of_orth hQ hg₂sq hg₃sq horth)
    rw [hdimg₂, hdimg₃] at h
    omega
  have hw_self : (g₂ * g₃) * (g₂ * g₃) = 1 := mul_mul_self_of_orth hQ hg₂sq hg₃sq horth
  have h1dim : invDim (1 : OGroup Q) = 0 := congrArg Prod.fst (invType_one (Q := Q))
  have hpidim : invDim (piOrth Q) = 6 := by
    have h : invDim (piOrth Q) = Module.finrank (ZMod 3) V :=
      congrArg Prod.fst (invType_piOrth hQ)
    rw [hdim] at h
    exact h
  have hw_ne : toProj Q (g₂ * g₃) ≠ 1 := by
    intro h1
    have hker : g₂ * g₃ ∈ (toProj Q).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk' (piGroup Q)] at hker
    rcases mem_piGroup_iff.mp hker with ht1 | htpi
    · rw [ht1, h1dim] at hdimg23
      exact absurd hdimg23 (by decide)
    · rw [htpi, hpidim] at hdimg23
      exact absurd hdimg23 (by decide)
  have hQp : Q (u + u') = 2 * c := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hu, hu', huu']; ring
  have hQp' : Q (v + v') = 2 * c := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hv, hv', hvv']; ring
  have h2c : (2 : ZMod 3) * c ≠ 0 := mul_ne_zero (by decide) hc
  have hpne : Q (u + u') ≠ 0 := by rw [hQp]; exact h2c
  have hp'ne : Q (v + v') ≠ 0 := by rw [hQp']; exact h2c
  have ha₀Ω : a₀ ∈ omegaGroup hQ := by
    rw [ha₀def, reflTot_of_ne hpne, reflTot_of_ne hp'ne]
    exact reflOf_mul_reflOf_mem_omegaGroup hQ _ _ hpne hp'ne (hQp.trans hQp'.symm)
  have hw_Ω : g₂ * g₃ ∈ omegaGroup hQ := by
    rw [← hw_comm]
    exact mul_mem ((omegaGroup_normal hQ).conj_mem a₀ ha₀Ω t) (inv_mem ha₀Ω)
  obtain ⟨d, hddef⟩ : ∃ d : OGroup Q, d = reflTot Q v * reflTot Q v' := ⟨_, rfl⟩
  have htd : t * d = d * t := by
    have h : t * d * t⁻¹ = d := by
      rw [hddef]
      calc t * (reflTot Q v * reflTot Q v') * t⁻¹
          = (t * reflTot Q v * t⁻¹) * (t * reflTot Q v' * t⁻¹) := by group
        _ = reflTot Q ((t : V ≃ₗ[ZMod 3] V) v) * reflTot Q ((t : V ≃ₗ[ZMod 3] V) v') := by
            rw [reflTot_conj, reflTot_conj]
        _ = reflTot Q v * reflTot Q v' := by rw [htv, htv', reflTot_neg]
    exact mul_inv_eq_iff_eq_mul.mp h
  have hE1 : σ * d * σ⁻¹ * d⁻¹ = g₂ * g₃ := by
    have h1 : σ * d * σ⁻¹ = reflTot Q u * reflTot Q u' := by
      rw [hddef]
      calc σ * (reflTot Q v * reflTot Q v') * σ⁻¹
          = (σ * reflTot Q v * σ⁻¹) * (σ * reflTot Q v' * σ⁻¹) := by group
        _ = reflTot Q ((σ : V ≃ₗ[ZMod 3] V) v) * reflTot Q ((σ : V ≃ₗ[ZMod 3] V) v') := by
            rw [reflTot_conj, reflTot_conj]
        _ = reflTot Q u * reflTot Q u' := by rw [hσv, hσv']
    rw [h1, hddef, mul_inv_rev, reflTot_inv, reflTot_inv, hg₂def, hg₃def,
      reflTot_comm hv'ne hvne hv'v]
  obtain ⟨σ₂, hσ₂def⟩ : ∃ s : OGroup Q, s = d * σ * d⁻¹ := ⟨_, rfl⟩
  have hσ₂Ω : σ₂ ∈ omegaGroup hQ := by
    rw [hσ₂def]; exact (omegaGroup_normal hQ).conj_mem σ hσΩ d
  have hσ₂3 : σ₂ ^ 3 = 1 := by rw [hσ₂def, conj_pow, hσ3]; group
  have hct_d : Commute t d := htd
  have hct_σ : Commute t σ := hσt.symm
  have hct_σ₂ : Commute t σ₂ := by
    rw [hσ₂def]; exact (hct_d.mul_right hct_σ).mul_right hct_d.inv_right
  have hmem : ∀ (g : OGroup Q) (hg : g ∈ omegaGroup hQ), Commute t g →
      omegaToProj hQ ⟨g, hg⟩ ∈ ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)) := by
    intro g hg hgc
    exact ff6m_omegaToProj_mem_ffFix hQ hdim hsgn hg hgc.eq
  have hodd : ∀ (g : OGroup Q) (hg : g ∈ omegaGroup hQ), g ^ 3 = 1 →
      Odd (orderOf (omegaToProj hQ ⟨g, hg⟩)) := by
    intro g hg h3
    apply ff_odd_orderOf_of_pow_three
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_omegaToProj, ← map_pow, h3, map_one, Subgroup.coe_one]
  generalize hC : ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)) = C at hmem ⊢
  have hσR : omegaToProj hQ ⟨σ, hσΩ⟩ ∈ twoRes C :=
    Subgroup.subset_closure ⟨hmem σ hσΩ hct_σ, hodd σ hσΩ hσ3⟩
  have hσ₂R : omegaToProj hQ ⟨σ₂, hσ₂Ω⟩ ∈ twoRes C :=
    Subgroup.subset_closure ⟨hmem σ₂ hσ₂Ω hct_σ₂, hodd σ₂ hσ₂Ω hσ₂3⟩
  have hw_eq : g₂ * g₃ = σ * σ₂⁻¹ := by rw [← hE1, hσ₂def]; group
  have hwR : omegaToProj hQ ⟨g₂ * g₃, hw_Ω⟩ ∈ twoRes C := by
    have hsub : (⟨g₂ * g₃, hw_Ω⟩ : omegaGroup hQ) =
        ⟨σ, hσΩ⟩ * (⟨σ₂, hσ₂Ω⟩)⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv]
      exact hw_eq
    have h : omegaToProj hQ ⟨g₂ * g₃, hw_Ω⟩ =
        omegaToProj hQ ⟨σ, hσΩ⟩ * (omegaToProj hQ ⟨σ₂, hσ₂Ω⟩)⁻¹ := by
      rw [hsub, map_mul, map_inv]
    rw [h]
    exact mul_mem hσR (inv_mem hσ₂R)
  have hw_self' : omegaToProj hQ ⟨g₂ * g₃, hw_Ω⟩ *
      omegaToProj hQ ⟨g₂ * g₃, hw_Ω⟩ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_omegaToProj, ← map_mul, hw_self, map_one, Subgroup.coe_one]
  have hw_ne' : omegaToProj hQ ⟨g₂ * g₃, hw_Ω⟩ ≠ 1 := by
    intro h
    refine hw_ne ?_
    have := congrArg (fun z : ↥(omegaProj hQ) => (z : ProjOrth Q)) h
    rwa [coe_omegaToProj, Subgroup.coe_one] at this
  refine ⟨omegaToProj hQ ⟨g₂ * g₃, hw_Ω⟩, hwR, hw_self', hw_ne',
    omegaToProj hQ ⟨a₀, ha₀Ω⟩, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_ffSimOmegaAct, coe_omegaToProj]
  change toProj Q (simAct Q (orthToSim Q t) a₀) * (toProj Q a₀)⁻¹ = toProj Q (g₂ * g₃)
  rw [simAct_orthToSim, ← map_inv, ← map_mul, hw_comm]

private theorem ff6m_K3_cover_of_involution (hQ : Q.Nondegenerate)
    (hdim : Module.finrank (ZMod 3) V = 6) (hsgn : quadSign Q = -1) {t : OGroup Q}
    (htt : t * t = 1) {α : ℤˣ} (hty : invType t = (3, α)) :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoRes (ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t))) ∧
      w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (projOrthToProjSim Q (toProj Q t)) a * a⁻¹ = w := by
  have hdimW : Module.finrank (ZMod 3) (commSp t) = 3 := by
    simpa only [invType, invDim] using congrArg Prod.fst hty
  have hdimU : Module.finrank (ZMod 3) (fixSp t) = 3 := by
    have := finrank_fixSp_add_finrank_commSp (Q := Q) t
    omega
  have hQU := nondegenerate_restrict_fixSp hQ htt
  have hQW := nondegenerate_restrict_commSp hQ htt
  obtain ⟨frU, hnU⟩ := ff_exists_k3Frame hQU hdimU
  obtain ⟨frW, hnW⟩ := ff_exists_k3Frame hQW hdimW
  have hcc := ff6m_frameNorm_eq hQ htt hdim hsgn hty
  have hQu : Q (frU.u : V) = (frameNorm (Q.restrict (fixSp t)) : ZMod 3) := hnU
  have hQv : Q (frU.v : V) = (frameNorm (Q.restrict (fixSp t)) : ZMod 3) :=
    (frU.huv'.symm.trans hnU : _)
  have hQu' : Q (frW.u : V) = (frameNorm (Q.restrict (fixSp t)) : ZMod 3) :=
    hnW.trans hcc.symm
  have hQv' : Q (frW.v : V) = (frameNorm (Q.restrict (fixSp t)) : ZMod 3) :=
    (frW.huv'.symm.trans hnW).trans hcc.symm
  have hσΩ : blockHom htt (frU.sig, frW.sig) ∈ omegaGroup hQ := by
    have h : blockHom htt (frU.sig, frW.sig) =
        blockHom htt (frU.sig, 1) * blockHom htt (1, frW.sig) := by
      rw [← map_mul]; simp
    rw [h]
    exact mul_mem (blockHom_left_mem_omegaGroup hQ htt (by omega) (frU.sig_mem hQU))
      (blockHom_right_mem_omegaGroup hQ htt (by omega) (frW.sig_mem hQW))
  have hσ3 : blockHom htt (frU.sig, frW.sig) ^ 3 = 1 := by
    rw [← map_pow, Prod.pow_def]
    simp only [frU.sig_cube hdimU, frW.sig_cube hdimW]
    exact map_one _
  have hσt : blockHom htt (frU.sig, frW.sig) * t = t * blockHom htt (frU.sig, frW.sig) := by
    have h : blockHom htt (frU.sig, frW.sig) ∈ (blockHom htt).range := ⟨_, rfl⟩
    rw [range_blockHom hQ htt] at h
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  have hσv : ((blockHom htt (frU.sig, frW.sig) : OGroup Q) : V ≃ₗ[ZMod 3] V) (frU.v : V) =
      (frU.u : V) := by
    have h := blockHom_apply htt (frU.sig, frW.sig) frU.v 0
    simpa [frU.sig_apply_v] using h
  have hσv' : ((blockHom htt (frU.sig, frW.sig) : OGroup Q) : V ≃ₗ[ZMod 3] V) (frW.v : V) =
      (frW.u : V) := by
    have h := blockHom_apply htt (frU.sig, frW.sig) 0 frW.v
    simpa [frW.sig_apply_v] using h
  exact ff6m_K3_cover_of_data hQ hdim hsgn htt (frameNorm_ne_zero (Q.restrict (fixSp t)))
    hQu hQv hQu' hQv' frU.huv (ff_polar_fixSp_commSp hQ htt frU.u.2 frW.u.2)
    (ff_polar_fixSp_commSp hQ htt frU.u.2 frW.v.2)
    (ff_polar_fixSp_commSp hQ htt frU.v.2 frW.u.2)
    (ff_polar_fixSp_commSp hQ htt frU.v.2 frW.v.2) frW.huv
    (mem_fixSp_iff.mp frU.u.2) (mem_fixSp_iff.mp frU.v.2)
    ((mem_commSp_iff htt).mp frW.u.2) ((mem_commSp_iff htt).mp frW.v.2)
    hσΩ hσ3 hσt hσv hσv'

theorem ff6m_K3_cover (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = -1)
    {x : ProjSim Q} (hx : KM3 x) :
    ∃ w : ↥(omegaProj hQ), w ∈ twoRes (ffFix hQ (by omega) x) ∧ w * w = 1 ∧ w ≠ 1 ∧
      ∃ a : ↥(omegaProj hQ), ffSimOmegaAct hQ (by omega) x a * a⁻¹ = w := by
  simp only [KM3, SimHasType, HasType] at hx
  obtain ⟨α, y, hyx, -, t, htt, hty, hty'⟩ := hx
  rw [← hyx, ← hty']
  exact ff6m_K3_cover_of_involution hQ hdim hsgn htt hty

end CFSG.OddStandard.SmallF3.Omega
