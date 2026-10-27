module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LargeExtraspecial.S2OrthMinus
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S8

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_conj eichler_add_smul_self)

section Comm

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

theorem finrank_commSpace_mul_le (f g : M ≃ₗ[K] M) :
    finrank K (commSpace (f * g)) ≤ finrank K (commSpace f) + finrank K (commSpace g) := by
  have hle : commSpace (f * g) ≤ commSpace f ⊔ commSpace g := by
    intro v hv
    obtain ⟨w, rfl⟩ := mem_commSpace.mp hv
    have e : (f * g) w - w = (f (g w) - g w) + (g w - w) := by
      rw [LinearEquiv.mul_apply]; abel
    rw [e]
    exact Submodule.add_mem_sup (sub_mem_commSpace f _) (sub_mem_commSpace g w)
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

omit [FiniteDimensional K M] in
theorem finrank_commSpace_conj' (f h : M ≃ₗ[K] M) :
    finrank K (commSpace (h * f * h⁻¹)) = finrank K (commSpace f) := by
  have e : commSpace (h * f * h⁻¹) = (commSpace f).map (h : M →ₗ[K] M) := by
    ext v
    rw [mem_commSpace, Submodule.mem_map]
    constructor
    · rintro ⟨w, rfl⟩
      refine ⟨f (h.symm w) - h.symm w, sub_mem_commSpace f _, ?_⟩
      change h (f (h.symm w) - h.symm w) = h (f (h.symm w)) - w
      rw [map_sub, LinearEquiv.apply_symm_apply]
    · rintro ⟨u, hu, rfl⟩
      obtain ⟨w, rfl⟩ := mem_commSpace.mp hu
      refine ⟨h w, ?_⟩
      change h (f (h.symm (h w))) - h w = h (f w - w)
      rw [LinearEquiv.symm_apply_apply, map_sub]
  rw [e, LinearEquiv.finrank_map_eq]

end Comm

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V] {hq : q.polarBilin.Nondegenerate}
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem finrank_eq_two_mul_finrank_commSpace {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1) (hD : RadDecomp ρ ⊥ ⊤ p p₁)
    (x : omegaGroup q hq) (hx : (x : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p)
    (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) (hxa : ¬ IsTypeA q x 2) :
    finrank (ZMod 2) M = 2 * finrank (ZMod 2) (commSpace (ρ x)) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hpp₁' : polar q p₁ p = 1 := by rw [polar_comm]; exact hpp₁
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hdimV : finrank (ZMod 2) (perp q (⊥ : Submodule (ZMod 2) V)) = 2 * m := by
    rw [perp_bot, finrank_top]; exact hdim
  have hmem : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  have hx' : (x : V ≃ₗ[ZMod 2] V) ∈ radFix q ⊥ p := by rw [radFix_bot]; exact hx
  obtain ⟨h1, h2⟩ := timmesfeld_2_1_b0 ρ hF hm hdimV (fun _ _ _ _ => Submodule.mem_top) (hmem _)
    (hmem _) hp₁0 hp₁ hp hpp₁' hD.symm x hx' hx1 hxa
  simp only [top_inf_eq] at h1 h2
  have h3 := finrank_commSpace_add_finrank_fixSpace (ρ x)
  have e : commSpace (ρ x) = (⊤ : Submodule (ZMod 2) M).map ((ρ x : M →ₗ[ZMod 2] M) - 1) := by
    rw [Submodule.map_top]
  rw [e, h2, h1] at h3
  rw [e, h2]
  omega

omit hq in
theorem exists_eichler_of_mem_pointRadical (hq : q.polarBilin.Nondegenerate) {p p₁ : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) {x : V ≃ₗ[ZMod 2] V}
    (hx : x ∈ pointRadical q p) (hx1 : x ≠ 1) :
    ∃ u ∈ perp q (⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}), u ≠ 0 ∧ x = eichler q p u := by
  have hmem : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  obtain ⟨u, -, hpu, rfl⟩ := (mem_radFix_iff hq hp0 hp (hmem p) (F := ⊥)).mp
    (by rw [radFix_bot]; exact hx)
  set u' := u + polar q u p₁ • p with hu'
  have hpu' : polar q p u' = 0 := by
    rw [hu', polar_add_right, polar_smul_right, polar_self_eq_zero, smul_zero, add_zero, hpu]
  have hp₁u' : polar q p₁ u' = 0 := by
    rw [hu', polar_add_right, polar_smul_right, polar_comm q p₁ p, hpp₁, smul_eq_mul, mul_one,
      polar_comm, CharTwo.add_self_eq_zero]
  have hxu' : eichler q p u = eichler q p u' := by
    rw [hu', eichler_add_smul_self hp]
  refine ⟨u', mem_perp_sup_span_pair.mpr ⟨hmem _, hpu', hp₁u'⟩, ?_, hxu'⟩
  rintro h0
  apply hx1
  rw [hxu', h0]
  exact CFSG.ClassicalGroups.Orthogonal.eichler_zero_right (Q := q) p

theorem exists_mul_conj_not_isTypeA {m : ℕ} (hm : 3 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1)
    {x : V ≃ₗ[ZMod 2] V} (hx : x ∈ pointRadical q p) (hx1 : x ≠ 1) (hxa : IsTypeA q x 2) :
    ∃ g ∈ omegaGroup q hq, g p = p ∧
      x * (g * x * g⁻¹) ∈ pointRadical q p ∧ x * (g * x * g⁻¹) ≠ 1 ∧
      ¬ IsTypeA q (x * (g * x * g⁻¹)) 2 := by
  have hF : (⊥ : Submodule (ZMod 2) V) ⊓ perp q ⊥ = ⊥ := bot_inf_eq _
  have hmem : ∀ v : V, v ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun v => by
    rw [perp_bot]; exact Submodule.mem_top
  obtain ⟨u', hu'K, hu'0, rfl⟩ := exists_eichler_of_mem_pointRadical hq hp0 hp hpp₁ hx hx1
  have hpu' : polar q p u' = 0 := (mem_perp_sup_span_pair.mp hu'K).2.1
  have hK := sup_span_pair_inf_perp_eq_bot hF (hmem p) (hmem p₁) hpp₁
  have hKdim := finrank_perp_sup_span_pair hq hF (hmem p) (hmem p₁) hpp₁
  rw [perp_bot, finrank_top, hdim] at hKdim
  have hqu' : q u' = 0 := by
    rcases zmod2_eq_zero_or_eq_one (q u') with h | h
    · exact h
    · exact absurd hxa (not_isTypeA_eichler hq hp0 hp hpu' h)
  obtain ⟨u'', hu''K, hu'', hu'u''⟩ := exists_hyperbolic_partner hq hK hu'K hu'0 hqu'
  have hu''0 : u'' ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hu'u''
    exact zero_ne_one hu'u''
  obtain ⟨g, hg, hgu⟩ := exists_mem_radGen_apply_eq hq hK (by omega) hu'K hu''K hu'0 hu''0 hqu'
    hu''
  have hgΩ := radGen_le_omegaFix hq _ hg
  have hgO := mem_orthogonalGroup_of_mem_omegaFix hgΩ
  have hgp : g p = p := hgΩ.2 p (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hpu'' : polar q p u'' = 0 := (mem_perp_sup_span_pair.mp hu''K).2.1
  refine ⟨g, hgΩ.1, hgp, ?_⟩
  rw [eichler_conj hgO, hgp, hgu, eichler_mul hpu' hpu'']
  have hq1 : q (u' + u'') = 1 := by
    have h0 : q (u' + u'') = q u' + q u'' + polar q u' u'' := by rw [polar]; abel
    rw [h0, hqu', hu'', hu'u'']
    rfl
  have hpsum : polar q p (u' + u'') = 0 := by rw [polar_add_right, hpu', hpu'', add_zero]
  have hli : LinearIndependent (ZMod 2) ![p, u' + u''] := by
    refine (LinearIndependent.pair_iff' hp0).mpr fun a ha => ?_
    have h0 : q (a • p) = 1 := by rw [ha, hq1]
    rw [QuadraticMap.map_smul, hp, smul_zero] at h0
    exact zero_ne_one h0
  exact ⟨eichler_mem_pointRadical hp hpsum, eichler_ne_one hq hp hpsum hli,
    not_isTypeA_eichler hq hp0 hp hpsum hq1⟩

theorem finrank_le_four_mul_finrank_commSpace {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) (hgen : 3 ≤ m ∨ IsMinusType q ⊥ m) {p p₁ : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hD : RadDecomp ρ ⊥ ⊤ p p₁) (x : omegaGroup q hq)
    (hx : (x : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p) (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) :
    finrank (ZMod 2) M ≤ 4 * finrank (ZMod 2) (commSpace (ρ x)) := by
  by_cases hxa : IsTypeA q x 2
  · rcases Nat.lt_or_ge m 3 with hm2 | hm3
    ·
      exfalso
      have hmin : IsMinusType q ⊥ m := hgen.resolve_left (by omega)
      obtain ⟨u', hu'K, hu'0, hxu⟩ := exists_eichler_of_mem_pointRadical hq hp0 hp hpp₁ hx hx1
      obtain ⟨-, hpu', hp₁u'⟩ := mem_perp_sup_span_pair.mp hu'K
      have hqu' : q u' = 0 := by
        rcases zmod2_eq_zero_or_eq_one (q u') with h | h
        · exact h
        · rw [hxu] at hxa
          exact absurd hxa (not_isTypeA_eichler hq hp0 hp hpu' h)
      have hli : LinearIndependent (ZMod 2) ![p, u'] := by
        refine (LinearIndependent.pair_iff' hp0).mpr fun a ha => ?_
        have h0 : polar q p₁ (a • p) = 0 := by rw [ha, hp₁u']
        rw [polar_smul_right, polar_comm, hpp₁, smul_eq_mul, mul_one] at h0
        rw [h0, zero_smul] at ha
        exact hu'0 ha.symm
      have hT : ∀ v ∈ Submodule.span (ZMod 2) {p, u'}, q v = 0 := by
        intro v hv
        obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hv
        have h0 : q (a • p + b • u') = q (a • p) + q (b • u') + polar q (a • p) (b • u') := by
          rw [polar]; abel
        rw [h0, QuadraticMap.map_smul, QuadraticMap.map_smul, hp, hqu', polar_smul_left,
          polar_smul_right, hpu']
        simp
      have h2 := hmin _ (by rw [perp_bot]; exact le_top) hT
      rw [finrank_span_pair hli] at h2
      omega
    · obtain ⟨g, hgΩ, -, hy, hy1, hya⟩ := exists_mul_conj_not_isTypeA (hq := hq) hm3 hdim hp0 hp
        hpp₁ hx hx1 hxa
      set gΩ : omegaGroup q hq := ⟨g, hgΩ⟩ with hgΩdef
      have hy' := finrank_eq_two_mul_finrank_commSpace ρ hm hdim hp hp₁ hpp₁ hD
        (x * (gΩ * x * gΩ⁻¹)) hy hy1 hya
      have hle := finrank_commSpace_mul_le (ρ x) (ρ gΩ * ρ x * (ρ gΩ)⁻¹)
      rw [finrank_commSpace_conj'] at hle
      rw [map_mul, map_mul, map_mul, map_inv] at hy'
      omega
  · have := finrank_eq_two_mul_finrank_commSpace ρ hm hdim hp hp₁ hpp₁ hD x hx hx1 hxa
    omega

end CFSG.LargeExtraspecial.S8
