module

public import CFSG.LargeExtraspecial.AS35YRFrame

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal

namespace AS35YR

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

namespace Frame

variable {F : Frame q}

theorem zmod2_cases_YR : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

theorem q_eq_zero_of_mem_ell {z : V} (hz : z ∈ F.ell) : q z = 0 := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [QuadraticMap.map_add q, QuadraticMap.map_smul, QuadraticMap.map_smul, F.qa, F.qb,
    polar_smul_left, polar_smul_right, F.ab]
  simp

theorem apply_eq_of_mem_ell {g : V ≃ₗ[ZMod 2] V} (ga : g F.a = F.a) (gb : g F.b = F.b) {z : V}
    (hz : z ∈ F.ell) : g z = z := by
  obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
  rw [map_add, map_smul, map_smul, ga, gb]

theorem polar_proj_proj {x x' : V} (ha : polar q x F.a = 0) (hb : polar q x F.b = 0)
    (ha' : polar q x' F.a = 0) (hb' : polar q x' F.b = 0) :
    polar q x x' = polar q (F.proj x) (F.proj x') := by
  have hz := F.sub_proj_mem_ell x
  have hz' := F.sub_proj_mem_ell x'
  have e : x = F.proj x + (x - F.proj x) := by abel
  have e' : x' = F.proj x' + (x' - F.proj x') := by abel
  have h1 : polar q (F.proj x) (x' - F.proj x') = 0 := by
    rw [polar_comm]
    exact polar_ell_of_perp hz' (by rw [F.polar_proj_a, ha]) (by rw [F.polar_proj_b, hb])
  have h2 : polar q (x - F.proj x) (F.proj x') = 0 :=
    polar_ell_of_perp hz (by rw [F.polar_proj_a, ha']) (by rw [F.polar_proj_b, hb'])
  have h3 : polar q (x - F.proj x) (x' - F.proj x') = 0 :=
    polar_ell_of_perp hz (by
      rw [polar_sub_left, F.polar_proj_a, ha', sub_self]) (by
      rw [polar_sub_left, F.polar_proj_b, hb', sub_self])
  conv_lhs => rw [e, e']
  rw [polar_add_left, polar_add_right, polar_add_right, h1, h2, h3, add_zero, add_zero, add_zero]

theorem eq_one_or_eq_t {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p) (hc : F.tau p F.c = 0)
    (hc' : F.tau p F.c' = 0) : p = 1 ∨ p = F.t := by
  have hNc : p F.c - F.c ∈ F.ell := by
    have := F.sub_proj_mem_ell (p F.c - F.c)
    rwa [← tau_def, hc, sub_zero] at this
  have hNc' : p F.c' - F.c' ∈ F.ell := by
    have := F.sub_proj_mem_ell (p F.c' - F.c')
    rwa [← tau_def, hc', sub_zero] at this
  have hperp : ∀ u, polar q u F.a = 0 → polar q u F.b = 0 → p u = u := by
    intro u ha hb
    have hmem := hp.sub_mem u ha hb
    have h1 : polar q (p u - u) F.c = 0 := by
      rw [hp.adjoint ha hb, polar_comm]
      exact polar_ell_of_perp hNc ha hb
    have h2 : polar q (p u - u) F.c' = 0 := by
      rw [hp.adjoint ha hb, polar_comm]
      exact polar_ell_of_perp hNc' ha hb
    exact sub_eq_zero.mp (F.eq_zero_of_mem_ell hmem h1 h2)
  have hiso := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hp.mem F.c F.c'
  have hqc := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hp.mem F.c
  have hqc' := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hp.mem F.c'
  have ec : p F.c = F.c + (p F.c - F.c) := by abel
  have ec' : p F.c' = F.c' + (p F.c' - F.c') := by abel
  rw [ec, QuadraticMap.map_add q, q_eq_zero_of_mem_ell hNc, add_zero] at hqc
  rw [ec', QuadraticMap.map_add q, q_eq_zero_of_mem_ell hNc', add_zero] at hqc'
  have hβ : polar q (p F.c - F.c) F.c = 0 := by
    rw [polar_comm]
    linear_combination hqc
  have hγ : polar q (p F.c' - F.c') F.c' = 0 := by
    rw [polar_comm]
    linear_combination hqc'
  have hba : polar q F.b F.a = 0 := by rw [polar_comm]; exact F.ab
  have hcross : polar q (p F.c - F.c) (p F.c' - F.c') = 0 :=
    polar_ell_of_perp hNc (polar_ell_of_perp hNc' (polar_self_eq_zero F.qa) F.ab)
      (polar_ell_of_perp hNc' hba (polar_self_eq_zero F.qb))
  rw [ec, ec', polar_add_left, polar_add_right, polar_add_right, hcross, add_zero,
    F.cc'] at hiso
  have hαδ : polar q (p F.c - F.c) F.c' = polar q (p F.c' - F.c') F.c := by
    rw [zero_add] at hiso
    rw [polar_comm q (p F.c' - F.c') F.c]
    exact (eq_neg_of_add_eq_zero_right hiso).trans (ZMod.neg_eq_self_mod_two _)
  have hpc : p F.c = F.c + polar q (p F.c - F.c) F.c' • F.a := by
    conv_lhs => rw [ec, F.eq_of_mem_ell hNc, hβ, zero_smul, add_zero]
  have hpc' : p F.c' = F.c' + polar q (p F.c - F.c) F.c' • F.b := by
    conv_lhs => rw [ec', F.eq_of_mem_ell hNc', hγ, zero_smul, zero_add, ← hαδ]
  rcases zmod2_cases_YR (polar q (p F.c - F.c) F.c') with h0 | h1
  · left
    rw [h0, zero_smul, add_zero] at hpc hpc'
    refine LinearEquiv.toLinearMap_injective (F.linearMap_ext (fun u ha hb => ?_) ?_ ?_)
    · simp [hperp u ha hb]
    · simp [hpc]
    · simp [hpc']
  · right
    rw [h1, one_smul] at hpc hpc'
    refine LinearEquiv.toLinearMap_injective (F.linearMap_ext (fun u ha hb => ?_) ?_ ?_)
    · simp only [LinearEquiv.coe_coe]
      rw [hperp u ha hb, F.t_apply, ha, hb, zero_smul, zero_smul, add_zero, add_zero]
    · simp only [LinearEquiv.coe_coe]
      rw [hpc, F.t_apply, polar_comm q F.c F.a, F.ac, polar_comm q F.c F.b, F.bc, zero_smul,
        add_zero, one_smul]
    · simp only [LinearEquiv.coe_coe]
      rw [hpc', F.t_apply, polar_comm q F.c' F.a, F.ac', polar_comm q F.c' F.b, F.bc',
        zero_smul, add_zero, one_smul]

theorem polar_nn {p₁ p₂ : V ≃ₗ[ZMod 2] V} (h₁ : F.InU p₁) (h₂ : F.InU p₂) (v y : V) :
    polar q (p₁ (p₂ v - v) - (p₂ v - v)) y = polar q (F.tau p₂ v) (F.tau p₁ y) := by
  rw [h₁.adjoint (h₂.polar_sub_a v) (h₂.polar_sub_b v),
    F.polar_proj_proj (h₂.polar_sub_a v) (h₂.polar_sub_b v) (h₁.polar_sub_a y)
      (h₁.polar_sub_b y)]
  rfl

theorem nn_mem_ell {p₁ p₂ : V ≃ₗ[ZMod 2] V} (h₁ : F.InU p₁) (h₂ : F.InU p₂) (v : V) :
    p₁ (p₂ v - v) - (p₂ v - v) ∈ F.ell :=
  h₁.sub_mem _ (h₂.polar_sub_a v) (h₂.polar_sub_b v)

theorem commute_of_polar {p₁ p₂ : V ≃ₗ[ZMod 2] V} (h₁ : F.InU p₁) (h₂ : F.InU p₂)
    (h : polar q (F.tau p₂ F.c) (F.tau p₁ F.c') = polar q (F.tau p₁ F.c) (F.tau p₂ F.c')) :
    p₁ * p₂ = p₂ * p₁ := by
  have key : ∀ v, (polar q (F.tau p₂ v) (F.tau p₁ F.c) = polar q (F.tau p₁ v) (F.tau p₂ F.c)) →
      (polar q (F.tau p₂ v) (F.tau p₁ F.c') = polar q (F.tau p₁ v) (F.tau p₂ F.c')) →
      p₁ (p₂ v) = p₂ (p₁ v) := by
    intro v hc hc'
    have e : p₁ (p₂ v) - p₂ (p₁ v) =
        (p₁ (p₂ v - v) - (p₂ v - v)) - (p₂ (p₁ v - v) - (p₁ v - v)) := by
      rw [map_sub, map_sub]
      abel
    have hmem : p₁ (p₂ v) - p₂ (p₁ v) ∈ F.ell := by
      rw [e]
      exact Submodule.sub_mem _ (nn_mem_ell h₁ h₂ v) (nn_mem_ell h₂ h₁ v)
    have hzc : polar q (p₁ (p₂ v) - p₂ (p₁ v)) F.c = 0 := by
      rw [e, polar_sub_left, polar_nn h₁ h₂, polar_nn h₂ h₁, hc, sub_self]
    have hzc' : polar q (p₁ (p₂ v) - p₂ (p₁ v)) F.c' = 0 := by
      rw [e, polar_sub_left, polar_nn h₁ h₂, polar_nn h₂ h₁, hc', sub_self]
    exact sub_eq_zero.mp (F.eq_zero_of_mem_ell hmem hzc hzc')
  refine LinearEquiv.toLinearMap_injective (F.linearMap_ext (fun u ha hb => ?_) ?_ ?_)
  ·
    simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply]
    have hz₁ := h₁.sub_mem u ha hb
    have hz₂ := h₂.sub_mem u ha hb
    have e₁ : p₁ (p₂ u) = p₁ u + (p₂ u - u) := by
      have e : p₂ u = u + (p₂ u - u) := by abel
      rw [e, map_add, apply_eq_of_mem_ell h₁.fix_a h₁.fix_b hz₂]
      abel
    have e₂ : p₂ (p₁ u) = p₂ u + (p₁ u - u) := by
      have e : p₁ u = u + (p₁ u - u) := by abel
      rw [e, map_add, apply_eq_of_mem_ell h₂.fix_a h₂.fix_b hz₁]
      abel
    rw [e₁, e₂]
    abel
  · simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply]
    exact key F.c (polar_comm _ _ _) (h.trans rfl)
  · simp only [LinearEquiv.coe_coe, LinearEquiv.mul_apply]
    refine key F.c' ?_ (polar_comm _ _ _)
    rw [polar_comm q (F.tau p₂ F.c'), polar_comm q (F.tau p₁ F.c')]
    exact h.symm

theorem proj_apply_of_fix {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (ga : g F.a = F.a) (gb : g F.b = F.b) (gc : g F.c = F.c) (gc' : g F.c' = F.c') (u : V) :
    F.proj (g u) = g (F.proj u) := by
  have h1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg u F.c
  have h2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg u F.c'
  rw [gc] at h1
  rw [gc'] at h2
  rw [proj_apply, proj_apply, map_sub, map_add, map_smul, map_smul, ga, gb, h1, h2]

theorem tau_conj_of_fix {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (ga : g F.a = F.a) (gb : g F.b = F.b) (gc : g F.c = F.c) (gc' : g F.c' = F.c')
    {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p) :
    F.InU (g * p * g⁻¹) ∧ ∀ v, g v = v → F.tau (g * p * g⁻¹) v = g (F.tau p v) := by
  have hginv : ∀ v, g v = v → g⁻¹ v = v := fun v hv => by
    have h := g.symm_apply_apply v
    rw [hv] at h
    exact h
  have hgi := inv_mem hg
  refine ⟨⟨mul_mem (mul_mem hg hp.mem) hgi, ?_, ?_, ?_⟩, ?_⟩
  · simp only [LinearEquiv.mul_apply]
    rw [hginv _ ga, hp.fix_a, ga]
  · simp only [LinearEquiv.mul_apply]
    rw [hginv _ gb, hp.fix_b, gb]
  · intro v ha hb
    have ha' : polar q (g⁻¹ v) F.a = 0 := by
      have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgi v F.a
      rw [hginv _ ga] at this
      rw [this, ha]
    have hb' : polar q (g⁻¹ v) F.b = 0 := by
      have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hgi v F.b
      rw [hginv _ gb] at this
      rw [this, hb]
    have hmem := hp.sub_mem _ ha' hb'
    have e : (g * p * g⁻¹) v - v = g (p (g⁻¹ v) - g⁻¹ v) := by
      simp only [LinearEquiv.mul_apply, map_sub]
      rw [show g (g⁻¹ v) = v from g.apply_symm_apply v]
    rw [e]
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    rw [← hαβ, map_add, map_smul, map_smul, ga, gb]
    exact Submodule.mem_span_pair.mpr ⟨α, β, rfl⟩
  · intro v hv
    rw [tau_def, tau_def, ← proj_apply_of_fix hg ga gb gc gc']
    congr 1
    simp only [LinearEquiv.mul_apply, map_sub]
    rw [hginv v hv, hv]

theorem tau_conj_of_ell {s : V ≃ₗ[ZMod 2] V} (hs : s ∈ TauCeti.QuadraticMap.orthogonalGroup q)
    (hss : s * s = 1) (sa : s F.a ∈ F.ell) (sb : s F.b ∈ F.ell)
    (sperp : ∀ u, polar q u F.a = 0 → polar q u F.b = 0 → s u - u ∈ F.ell)
    {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p) :
    F.InU (s * p * s⁻¹) ∧ ∀ v, F.tau (s * p * s⁻¹) v = F.tau p (s v) := by
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hss' : ∀ v, s (s v) = v := fun v => by
    rw [← LinearEquiv.mul_apply, hss]
    rfl
  have hfix : ∀ {z}, z ∈ F.ell → p z = z := fun hz => apply_eq_of_mem_ell hp.fix_a hp.fix_b hz
  have hperp : ∀ u, polar q u F.a = 0 → polar q u F.b = 0 →
      polar q (s u) F.a = 0 ∧ polar q (s u) F.b = 0 := by
    intro u ha hb
    have e1 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hs u (s F.a)
    have e2 := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hs u (s F.b)
    rw [hss'] at e1 e2
    refine ⟨?_, ?_⟩
    · rw [e1, polar_comm]
      exact polar_ell_of_perp sa ha hb
    · rw [e2, polar_comm]
      exact polar_ell_of_perp sb ha hb
  have hsell : ∀ {z}, z ∈ F.ell → s z ∈ F.ell := by
    intro z hz
    obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hz
    rw [map_add, map_smul, map_smul]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ sa) (Submodule.smul_mem _ _ sb)
  have hproj : ∀ u, polar q u F.a = 0 → polar q u F.b = 0 → F.proj (s u) = F.proj u := by
    intro u ha hb
    have e : s u = u + (s u - u) := by abel
    rw [e, map_add, F.proj_eq_zero_of_mem_ell (sperp u ha hb), add_zero]
  rw [hsinv]
  refine ⟨⟨mul_mem (mul_mem hs hp.mem) hs, ?_, ?_, ?_⟩, ?_⟩
  · simp only [LinearEquiv.mul_apply]
    rw [hfix sa, hss']
  · simp only [LinearEquiv.mul_apply]
    rw [hfix sb, hss']
  · intro v ha hb
    obtain ⟨ha', hb'⟩ := hperp v ha hb
    have hmem := hp.sub_mem _ ha' hb'
    have e : (s * p * s) v - v = s (p (s v) - s v) := by
      simp only [LinearEquiv.mul_apply, map_sub]
      rw [hss']
    rw [e]
    exact hsell hmem
  · intro v
    have e : (s * p * s) v - v = s (p (s v) - s v) := by
      simp only [LinearEquiv.mul_apply, map_sub]
      rw [hss']
    rw [tau_def, tau_def, e, hproj _ (hp.polar_sub_a _) (hp.polar_sub_b _)]

noncomputable abbrev s₁ (F : Frame q) : V ≃ₗ[ZMod 2] V := eichler q F.a F.c

noncomputable abbrev s₂ (F : Frame q) : V ≃ₗ[ZMod 2] V := eichler q F.b F.c'

theorem s₁_apply (x : V) : F.s₁ x = x + polar q x F.a • F.c + polar q x F.c • F.a :=
  siegel_apply F.qa F.qc F.ac x

theorem s₂_apply (x : V) : F.s₂ x = x + polar q x F.b • F.c' + polar q x F.c' • F.b :=
  siegel_apply F.qb F.qc' F.bc' x

theorem s₁_mem : F.s₁ ∈ TauCeti.QuadraticMap.orthogonalGroup q := eichler_mem_orthogonalGroup q _ _

theorem s₂_mem : F.s₂ ∈ TauCeti.QuadraticMap.orthogonalGroup q := eichler_mem_orthogonalGroup q _ _

theorem s₁_mul_self : F.s₁ * F.s₁ = 1 := siegel_mul_self F.ac

theorem s₂_mul_self : F.s₂ * F.s₂ = 1 := siegel_mul_self F.bc'

theorem a_mem_ell : F.a ∈ F.ell := Submodule.subset_span (by simp)

theorem b_mem_ell : F.b ∈ F.ell := Submodule.subset_span (by simp)

theorem tau_conj_s₁ {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p) :
    F.InU (F.s₁ * p * F.s₁⁻¹) ∧ F.tau (F.s₁ * p * F.s₁⁻¹) F.c = F.tau p F.c ∧
      F.tau (F.s₁ * p * F.s₁⁻¹) F.c' = F.tau p F.c' + F.tau p F.c := by
  have hsa : F.s₁ F.a = F.a := by
    rw [s₁_apply, polar_self_eq_zero F.qa, F.ac]
    simp
  have hsb : F.s₁ F.b = F.b + F.a := by
    rw [s₁_apply, polar_comm q F.b F.a, F.ab, F.bc]
    simp
  have hsc : F.s₁ F.c = F.c := by
    rw [s₁_apply, polar_comm q F.c F.a, F.ac, polar_self_eq_zero F.qc]
    simp
  have hsc' : F.s₁ F.c' = F.c' + F.c := by
    rw [s₁_apply, polar_comm q F.c' F.a, F.ac', polar_comm q F.c' F.c, F.cc']
    simp
  obtain ⟨hU, hτ⟩ := tau_conj_of_ell F.s₁_mem F.s₁_mul_self (by rw [hsa]; exact F.a_mem_ell)
    (by rw [hsb]; exact Submodule.add_mem _ F.b_mem_ell F.a_mem_ell) (fun u ha hb => by
      rw [s₁_apply, ha, zero_smul, add_zero, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ F.a_mem_ell) hp
  refine ⟨hU, ?_, ?_⟩
  · rw [hτ, hsc]
  · rw [hτ, hsc', tau_add]

theorem tau_conj_s₂ {p : V ≃ₗ[ZMod 2] V} (hp : F.InU p) :
    F.InU (F.s₂ * p * F.s₂⁻¹) ∧ F.tau (F.s₂ * p * F.s₂⁻¹) F.c = F.tau p F.c + F.tau p F.c' ∧
      F.tau (F.s₂ * p * F.s₂⁻¹) F.c' = F.tau p F.c' := by
  have hsa : F.s₂ F.a = F.a + F.b := by
    rw [s₂_apply, F.ab, F.ac']
    simp
  have hsb : F.s₂ F.b = F.b := by
    rw [s₂_apply, polar_self_eq_zero F.qb, F.bc']
    simp
  have hsc : F.s₂ F.c = F.c + F.c' := by
    rw [s₂_apply, polar_comm q F.c F.b, F.bc, F.cc']
    simp
  have hsc' : F.s₂ F.c' = F.c' := by
    rw [s₂_apply, polar_comm q F.c' F.b, F.bc', polar_self_eq_zero F.qc']
    simp
  obtain ⟨hU, hτ⟩ := tau_conj_of_ell F.s₂_mem F.s₂_mul_self
    (by rw [hsa]; exact Submodule.add_mem _ F.a_mem_ell F.b_mem_ell)
    (by rw [hsb]; exact F.b_mem_ell) (fun u ha hb => by
      rw [s₂_apply, hb, zero_smul, add_zero, add_sub_cancel_left]
      exact Submodule.smul_mem _ _ F.b_mem_ell) hp
  refine ⟨hU, ?_, ?_⟩
  · rw [hτ, hsc, tau_add]
  · rw [hτ, hsc']

end Frame

end AS35YR

end CFSG.LargeExtraspecial
