module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModelK3Aux5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff_odd_orderOf_of_pow_three {G : Type} [Group G] {g : G} (h : g ^ 3 = 1) :
    Odd (orderOf g) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one h) with h1 | h3
  · rw [h1]; exact odd_one
  · rw [h3]; decide

theorem ff_mem_twoPrimeRes_of_invol {G : Type} [Group G] {R : Subgroup G} {w : G}
    (hw : w ∈ R) (hw2 : w * w = 1) : w ∈ twoPrimeRes R := by
  by_cases hw1 : w = 1
  · rw [hw1]; exact (twoPrimeRes R).one_mem
  · have hw2' : w ^ 2 = 1 := by rw [pow_two]; exact hw2
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one hw2'
    have hord : orderOf w = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hw1
      · exact h
    exact Subgroup.subset_closure ⟨hw, 1, by rw [hord]; rfl⟩

theorem ff_invType_reflPair_opp (hQ : Q.Nondegenerate) {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0)
    (hab : polar Q a b = 0) (hba : Q b = -Q a) :
    invType (reflOf Q a ha * reflOf Q b hb) = (2, 1) := by
  have hcase : Q a = 1 ∨ Q a = -1 := by
    revert ha; generalize Q a = x; revert x; decide
  rcases hcase with h1 | h1
  · exact ff_invType_reflPair hQ ha hb hab h1 (by rw [hba, h1])
  · have hb1 : Q b = 1 := by rw [hba, h1]; exact neg_neg 1
    rw [mul_comm_reflOf_of_orth a b ha hb hab]
    exact ff_invType_reflPair hQ hb ha ((QuadraticMap.polar_comm Q b a).trans hab) hb1 h1

theorem ff_k3_pair_sq {a b : V} (ha : Q a ≠ 0) (hb : Q b ≠ 0) (hab : polar Q a b = 0) :
    (reflTot Q a * reflTot Q b) * (reflTot Q a * reflTot Q b) = 1 := by
  calc (reflTot Q a * reflTot Q b) * (reflTot Q a * reflTot Q b)
      = reflTot Q a * (reflTot Q b * reflTot Q a) * reflTot Q b := by group
    _ = reflTot Q a * (reflTot Q a * reflTot Q b) * reflTot Q b := by
        rw [reflTot_comm hb ha ((QuadraticMap.polar_comm Q b a).trans hab)]
    _ = 1 := by rw [← mul_assoc, reflTot_mul_self, one_mul, reflTot_mul_self]

@[expose] noncomputable def ffProjOmega (hQ : Q.Nondegenerate) (g : OGroup Q)
    (hg : g ∈ omegaGroup hQ) : ↥(omegaProj hQ) :=
  ⟨toProj Q g, (mem_omegaProj_iff hQ).mpr ⟨g, hg, rfl⟩⟩

theorem coe_ffProjOmega (hQ : Q.Nondegenerate) (g : OGroup Q) (hg : g ∈ omegaGroup hQ) :
    ((ffProjOmega hQ g hg : ↥(omegaProj hQ)) : ProjOrth Q) = toProj Q g := rfl

theorem ff_K3_cover_of_data (hQ : Q.Nondegenerate) (hdim : Module.finrank (ZMod 3) V = 6)
    (hsgn : quadSign Q = 1) {t : OGroup Q} (htt : t * t = 1) {c : ZMod 3} (hc : c ≠ 0)
    {u v u' v' : V} (hu : Q u = c) (hv : Q v = c) (hu' : Q u' = -c) (hv' : Q v' = -c)
    (huv : polar Q u v = 0) (huu' : polar Q u u' = 0) (huv' : polar Q u v' = 0)
    (hvu' : polar Q v u' = 0) (hvv' : polar Q v v' = 0) (hu'v' : polar Q u' v' = 0)
    (htu : (t : V ≃ₗ[ZMod 3] V) u = u) (htv : (t : V ≃ₗ[ZMod 3] V) v = v)
    (htu' : (t : V ≃ₗ[ZMod 3] V) u' = -u') (htv' : (t : V ≃ₗ[ZMod 3] V) v' = -v')
    {σ : OGroup Q} (hσΩ : σ ∈ omegaGroup hQ) (hσ3 : σ ^ 3 = 1) (hσt : σ * t = t * σ)
    (hσv : (σ : V ≃ₗ[ZMod 3] V) v = u) (hσv' : (σ : V ≃ₗ[ZMod 3] V) v' = u') :
    ∃ w : ↥(omegaProj hQ),
      w ∈ twoPrimeRes (twoRes (ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)))) ∧
      w * w = 1 ∧ KM0 (projOrthToProjSim Q (w : ProjOrth Q)) ∧
      ∃ a : ↥(omegaProj hQ),
        ffSimOmegaAct hQ (by omega) (projOrthToProjSim Q (toProj Q t)) a * a⁻¹ = w := by
  classical
  have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
  have hune : Q u ≠ 0 := by rw [hu]; exact hc
  have hvne : Q v ≠ 0 := by rw [hv]; exact hc
  have hu'ne : Q u' ≠ 0 := by rw [hu']; exact hc'
  have hv'ne : Q v' ≠ 0 := by rw [hv']; exact hc'
  have hvu : polar Q v u = 0 := (QuadraticMap.polar_comm Q v u).trans huv
  have hu'v : polar Q u' v = 0 := (QuadraticMap.polar_comm Q u' v).trans hvu'
  have hv'v : polar Q v' v = 0 := (QuadraticMap.polar_comm Q v' v).trans hvv'
  have hv'u' : polar Q v' u' = 0 := (QuadraticMap.polar_comm Q v' u').trans hu'v'
  have key : ∀ x : ZMod 3, -x + -x = x := by decide
  have hQs : Q (u' + v') = c := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hu', hv', hu'v', add_zero, key]
  have hQs' : Q (u' - v') = c := by
    rw [ff_map_sub, hu', hv', hu'v', sub_zero, key]
  have hus : polar Q u (u' + v') = 0 := by
    rw [QuadraticMap.polar_add_right, huu', huv', add_zero]
  have hus' : polar Q u (u' - v') = 0 := by
    rw [QuadraticMap.polar_sub_right, huu', huv', sub_zero]
  have hvs : polar Q v (u' + v') = 0 := by
    rw [QuadraticMap.polar_add_right, hvu', hvv', add_zero]
  have hvs' : polar Q v (u' - v') = 0 := by
    rw [QuadraticMap.polar_sub_right, hvu', hvv', sub_zero]
  have hss' : polar Q (u' + v') (u' - v') = 0 := by
    rw [QuadraticMap.polar_comm Q (u' + v') (u' - v'), ff_polar_sub_add, ff_k3_polar_self,
      ff_k3_polar_self, hu', hv', hu'v', hv'u']
    ring
  have hts : (t : V ≃ₗ[ZMod 3] V) (u' + v') = -(u' + v') := by
    rw [map_add, htu', htv', neg_add]
  have hts' : (t : V ≃ₗ[ZMod 3] V) (u' - v') = -(u' - v') := by
    rw [map_sub, htu', htv']; abel
  have hcomm := ff_k3_commutator (t := t) hc hu hv hQs hQs' huv hus hus' hvs hvs' hss' htu htv
    hts hts'
  rw [ff_k3_refl_sum_diff hu'ne (hu'.trans hv'.symm) hu'v'] at hcomm
  obtain ⟨a₀, ha₀def⟩ : ∃ a : OGroup Q,
      a = reflTot Q (u + (u' + v')) * reflTot Q (v + (u' - v')) := ⟨_, rfl⟩
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
  have hty₂ : invType g₂ = (2, 1) := by
    rw [hg₂r]; exact ff_invType_reflPair_opp hQ hune hu'ne huu' (by rw [hu, hu'])
  have hty₃ : invType g₃ = (2, 1) := by
    rw [hg₃r]; exact ff_invType_reflPair_opp hQ hvne hv'ne hvv' (by rw [hv, hv'])
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
  have hw_type : invType (g₂ * g₃) = (4, 1) := ff_invType_reflQuad hQ hg₂sq hg₃sq hty₂ hty₃ horth
  have hw_self : (g₂ * g₃) * (g₂ * g₃) = 1 := mul_mul_self_of_orth hQ hg₂sq hg₃sq horth
  have hw_ne : toProj Q (g₂ * g₃) ≠ 1 := by
    intro h1
    have hker : g₂ * g₃ ∈ (toProj Q).ker := MonoidHom.mem_ker.mpr h1
    rw [QuotientGroup.ker_mk' (piGroup Q)] at hker
    rcases mem_piGroup_iff.mp hker with ht1 | htpi
    · rw [ht1, invType_one] at hw_type
      exact absurd hw_type (by decide)
    · rw [htpi, invType_piOrth hQ, hdim, hsgn] at hw_type
      exact absurd hw_type (by decide)
  have hQp : Q (u + (u' + v')) = 2 * c := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hu, hQs, hus]; ring
  have hQp' : Q (v + (u' - v')) = 2 * c := by
    rw [CFSG.RankThree.OrthogonalInvolutions.map_add_eq, hv, hQs', hvs']; ring
  have h2c : (2 : ZMod 3) * c ≠ 0 := mul_ne_zero (by decide) hc
  have hpne : Q (u + (u' + v')) ≠ 0 := by rw [hQp]; exact h2c
  have hp'ne : Q (v + (u' - v')) ≠ 0 := by rw [hQp']; exact h2c
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
      ffProjOmega hQ g hg ∈ ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)) := by
    intro g hg hgc
    exact (ff_mem_ffFix_iff hQ hdim hsgn htt (ffProjOmega hQ g hg)).mpr
      ⟨g, Subgroup.mem_inf.mpr ⟨hg, Subgroup.mem_centralizer_singleton_iff.mpr hgc.eq.symm⟩,
        rfl⟩
  have hodd : ∀ (g : OGroup Q) (hg : g ∈ omegaGroup hQ), g ^ 3 = 1 →
      Odd (orderOf (ffProjOmega hQ g hg)) := by
    intro g hg h3
    apply ff_odd_orderOf_of_pow_three
    apply Subtype.ext
    rw [Subgroup.coe_pow, coe_ffProjOmega, ← map_pow, h3, map_one, Subgroup.coe_one]
  generalize hC : ffFix hQ (by omega) (projOrthToProjSim Q (toProj Q t)) = C at hmem ⊢
  have hσR : ffProjOmega hQ σ hσΩ ∈ twoRes C :=
    Subgroup.subset_closure ⟨hmem σ hσΩ hct_σ, hodd σ hσΩ hσ3⟩
  have hσ₂R : ffProjOmega hQ σ₂ hσ₂Ω ∈ twoRes C :=
    Subgroup.subset_closure ⟨hmem σ₂ hσ₂Ω hct_σ₂, hodd σ₂ hσ₂Ω hσ₂3⟩
  have hw_eq : g₂ * g₃ = σ * σ₂⁻¹ := by rw [← hE1, hσ₂def]; group
  have hwR : ffProjOmega hQ (g₂ * g₃) hw_Ω ∈ twoRes C := by
    have h : ffProjOmega hQ (g₂ * g₃) hw_Ω =
        ffProjOmega hQ σ hσΩ * (ffProjOmega hQ σ₂ hσ₂Ω)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_ffProjOmega]
      rw [hw_eq, map_mul, map_inv]
    rw [h]
    exact mul_mem hσR (inv_mem hσ₂R)
  have hw_self' : ffProjOmega hQ (g₂ * g₃) hw_Ω * ffProjOmega hQ (g₂ * g₃) hw_Ω = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_ffProjOmega, ← map_mul, hw_self, map_one, Subgroup.coe_one]
  refine ⟨ffProjOmega hQ (g₂ * g₃) hw_Ω, ff_mem_twoPrimeRes_of_invol hwR hw_self', hw_self', ?_,
    ffProjOmega hQ a₀ ha₀Ω, ?_⟩
  · exact ⟨toProj Q (g₂ * g₃), rfl, hw_ne, g₂ * g₃, hw_self, hw_type, rfl⟩
  · apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, coe_ffSimOmegaAct, coe_ffProjOmega]
    change toProj Q (simAct Q (orthToSim Q t) a₀) * (toProj Q a₀)⁻¹ = toProj Q (g₂ * g₃)
    rw [simAct_orthToSim, ← map_inv, ← map_mul, hw_comm]

end CFSG.OddStandard.SmallF3.Omega
