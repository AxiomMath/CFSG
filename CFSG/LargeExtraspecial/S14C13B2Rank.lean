module

public import CFSG.LargeExtraspecial.S2OrthOne
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_conj eichler_add_smul_self)

section Linear

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

theorem commSpace_mul_le (e f : M ≃ₗ[ZMod 2] M) :
    commSpace (e * f) ≤ commSpace e ⊔ commSpace f := by
  intro x hx
  obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
  have : (e * f) v - v = (e (f v) - f v) + (f v - v) := by
    rw [LinearEquiv.mul_apply]; abel
  rw [this]
  exact Submodule.add_mem_sup (sub_mem_commSpace e _) (sub_mem_commSpace f v)

theorem finrank_commSpace_mul_le [FiniteDimensional (ZMod 2) M] (e f : M ≃ₗ[ZMod 2] M) :
    finrank (ZMod 2) (commSpace (e * f)) ≤
      finrank (ZMod 2) (commSpace e) + finrank (ZMod 2) (commSpace f) :=
  (Submodule.finrank_mono (commSpace_mul_le e f)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

end Linear

section Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

omit [FiniteDimensional (ZMod 2) M] in
theorem radDecomp_of_isCompl {p p₁ : V}
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)))) :
    RadDecomp ρ ⊥ ⊤ p p₁ := by
  rw [RadDecomp, radFix_bot, radFix_bot, top_inf_eq, top_inf_eq]
  exact ⟨hc.sup_eq_top, hc.inf_eq_bot⟩

omit [FiniteDimensional (ZMod 2) M] in
theorem omegaInvariant_top : OmegaInvariant ρ ⊥ (⊤ : Submodule (ZMod 2) M) :=
  fun _ _ _ _ => Submodule.mem_top

theorem commSpace_eq_fixOf_of_not_isTypeA {m : ℕ} (hm : 2 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (x : omegaGroup q hq) (hx : (x : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p)
    (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) (hxa : ¬ IsTypeA q x 2) :
    fixSpace (ρ x) = fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) ∧
      commSpace (ρ x) = fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  have hD := (radDecomp_of_isCompl ρ hc).symm
  have hperp : ∀ y : V, y ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun y => by
    rw [perp_bot]; exact Submodule.mem_top
  obtain ⟨h1, h2⟩ := timmesfeld_2_1_b0 ρ (bot_inf_eq _) hm
    (by rw [perp_bot, finrank_top]; exact hdim)
    (omegaInvariant_top ρ) (hperp p₁) (hperp p) hp₁0 hp₁ hp hp₁p hD x
    (by rw [radFix_bot]; exact hx) hx1 hxa
  simp only [top_inf_eq, radFix_bot, Submodule.map_top] at h1 h2
  exact ⟨h1, h2⟩

theorem two_mul_finrank_fixOf_eq {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)))) :
    2 * finrank (ZMod 2) (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V))) =
      finrank (ZMod 2) M := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hperp : ∀ y : V, y ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun y => by
    rw [perp_bot]; exact Submodule.mem_top
  have h := (finrank_eq_two_mul ρ (bot_inf_eq _) (by rw [perp_bot, finrank_top]; omega)
    (omegaInvariant_top ρ) (hperp p) (hperp p₁) hp0 hp₁0 hp hp₁ (radDecomp_of_isCompl ρ hc)).2
  rw [top_inf_eq, radFix_bot, finrank_top] at h
  exact h.symm

omit [FiniteDimensional (ZMod 2) M] in
include hq in
theorem commute_of_mem_pointRadical {p : V} (hp0 : p ≠ 0) (hp : q p = 0)
    {x y : V ≃ₗ[ZMod 2] V} (hx : x ∈ pointRadical q p) (hy : y ∈ pointRadical q p) :
    x * y = y * x := by
  obtain ⟨a, hpa, rfl⟩ := (mem_pointRadical_iff hq hp0 hp).mp hx
  obtain ⟨b, hpb, rfl⟩ := (mem_pointRadical_iff hq hp0 hp).mp hy
  rw [eichler_mul hpa hpb, eichler_mul hpb hpa, add_comm]

omit [FiniteDimensional (ZMod 2) M] in
theorem pointRadical_le_omegaGroup {p : V} (hp0 : p ≠ 0) (hp : q p = 0) :
    pointRadical q p ≤ omegaGroup q hq := by
  intro x hx
  have := radFix_le_omegaFix hq (F := ⊥) hp0 hp (by rw [radFix_bot]; exact hx)
  rwa [omegaFix_bot] at this

omit [FiniteDimensional (ZMod 2) M] in
include hq in
theorem exists_nonsingular_perp_pair (h5 : 5 ≤ finrank (ZMod 2) V) {p p₁ : V}
    (hpp₁ : polar q p p₁ = 1) : ∃ w, polar q p w = 0 ∧ polar q p₁ w = 0 ∧ q w = 1 := by
  have hperp : ∀ y : V, y ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun y => by
    rw [perp_bot]; exact Submodule.mem_top
  have hF := sup_span_pair_inf_perp_eq_bot (q := q) (bot_inf_eq _) (hperp p) (hperp p₁) hpp₁
  have hdim := finrank_perp_sup_span_pair hq (bot_inf_eq _) (hperp p) (hperp p₁) hpp₁
  rw [perp_bot, finrank_top] at hdim
  obtain ⟨e, heF, he0, he⟩ := exists_singular_mem_perp (q := q)
    (F := ⊥ ⊔ Submodule.span (ZMod 2) {p, p₁}) (by omega)
  obtain ⟨f, hfF, hf, hef⟩ := exists_hyperbolic_partner hq hF heF he0 he
  rw [mem_perp_sup_span_pair] at heF hfF
  refine ⟨e + f, by rw [polar_add_right, heF.2.1, hfF.2.1, add_zero],
    by rw [polar_add_right, heF.2.2, hfF.2.2, add_zero], ?_⟩
  rw [QuadraticMap.map_add q e f, he, hf, hef, zero_add, zero_add]

omit [FiniteDimensional (ZMod 2) M] in
theorem exists_not_isTypeA_mem_pointRadical (h5 : 5 ≤ finrank (ZMod 2) V) {p p₁ : V}
    (hp0 : p ≠ 0) (hp : q p = 0) (hpp₁ : polar q p p₁ = 1) :
    ∃ c : omegaGroup q hq, (c : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p ∧
      (c : V ≃ₗ[ZMod 2] V) ≠ 1 ∧ ¬ IsTypeA q c 2 := by
  obtain ⟨w, hpw, -, hw⟩ := exists_nonsingular_perp_pair (hq := hq) h5 hpp₁
  have hE := eichler_mem_pointRadical hp hpw
  have hC := eichler_isTypeC hq hp0 hp hpw hw
  refine ⟨⟨eichler q p w, pointRadical_le_omegaGroup hp0 hp hE⟩, hE, hC.1.2.1, fun hA => ?_⟩
  obtain ⟨x, hx, hqx⟩ := hC.1.2.2.2.2.2
  exact hqx (hA.2.2.2.2 x hx)

theorem sub_mem_fixOf_of_mem_pointRadical {m : ℕ} (hm : 3 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (x : omegaGroup q hq) (hx : (x : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p) (v : M) :
    ρ x v - v ∈ fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) := by
  obtain ⟨c, hcL, hc1, hca⟩ := exists_not_isTypeA_mem_pointRadical (hq := hq) (by omega) hp0 hp hpp₁
  have hb0 := commSpace_eq_fixOf_of_not_isTypeA ρ (by omega) hdim hp hp₁ hpp₁ hc c hcL hc1 hca
  have hxc : x * c = c * x := Subtype.ext (commute_of_mem_pointRadical (hq := hq) hp0 hp hx hcL)
  rw [← hb0.1, mem_fixSpace]
  have h1 : ρ c v - v ∈ fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) := by
    rw [← hb0.2]; exact sub_mem_commSpace _ v
  have h2 : ρ x (ρ c v - v) = ρ c v - v := (mem_fixOf ρ).mp h1 x hx
  have h3 : ρ c (ρ x v) = ρ x (ρ c v) := by
    rw [← LinearEquiv.mul_apply, ← map_mul, ← hxc, map_mul, LinearEquiv.mul_apply]
  rw [map_sub, h3]
  rw [map_sub] at h2
  calc ρ x (ρ c v) - ρ c v = (ρ x (ρ c v) - ρ x v) + ρ x v - ρ c v := by abel
    _ = (ρ c v - v) + ρ x v - ρ c v := by rw [h2]
    _ = ρ x v - v := by abel

theorem finrank_le_four_mul_of_isTypeA {m : ℕ} (hm : 3 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0)
    (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (x : omegaGroup q hq) (hx : (x : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p)
    (hx1 : (x : V ≃ₗ[ZMod 2] V) ≠ 1) (hxa : IsTypeA q x 2) :
    finrank (ZMod 2) M ≤ 4 * finrank (ZMod 2) (commSpace (ρ x)) := by
  have hperp : ∀ y : V, y ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun y => by
    rw [perp_bot]; exact Submodule.mem_top
  have hdimF := finrank_perp_sup_span_pair hq (bot_inf_eq _) (hperp p) (hperp p₁) hpp₁
  rw [perp_bot, finrank_top] at hdimF
  have hF₀ := sup_span_pair_inf_perp_eq_bot (q := q) (bot_inf_eq _) (hperp p) (hperp p₁) hpp₁
  set F₀ := (⊥ : Submodule (ZMod 2) V) ⊔ Submodule.span (ZMod 2) {p, p₁} with hF₀def
  obtain ⟨u, hpu, hxu⟩ := (mem_pointRadical_iff hq hp0 hp).mp hx
  set u' := u + polar q u p₁ • p with hu'
  have hxu' : (x : V ≃ₗ[ZMod 2] V) = eichler q p u' := by
    rw [hxu, hu', eichler_add_smul_self hp]
  have hpu' : polar q p u' = 0 := by
    rw [hu', polar_add_right, polar_smul_right, polar_self_eq_zero q p, smul_zero, add_zero, hpu]
  have hp₁u' : polar q p₁ u' = 0 := by
    rw [hu', polar_add_right, polar_smul_right, polar_comm q p₁ p, hpp₁, smul_eq_mul, mul_one,
      polar_comm q p₁ u]
    exact zmod2_add_self _
  have hu'F : u' ∈ perp q F₀ := mem_perp_sup_span_pair.mpr ⟨hperp u', hpu', hp₁u'⟩
  have hu'0 : u' ≠ 0 := by
    intro h
    apply hx1
    rw [hxu', h, CFSG.ClassicalGroups.Orthogonal.eichler_zero_right]
  have hli : LinearIndependent (ZMod 2) ![p, u'] := by
    rw [linearIndependent_pair_iff]
    refine ⟨hp0, hu'0, fun h => hx1 ?_⟩
    rw [hxu', ← h]
    exact (eichler_eq_one_iff hq hp0 hp (polar_self_eq_zero q p)).mpr
      (Submodule.mem_span_singleton_self p)
  have hqu' : q u' = 0 := by
    refine hxa.2.2.2.2 u' ?_
    rw [hxu', commSpace_eichler hq hp hpu' hli]
    exact Submodule.subset_span (by simp)
  obtain ⟨v, hvF, hv, huv⟩ := exists_hyperbolic_partner hq hF₀ hu'F hu'0 hqu'
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at huv
    exact zero_ne_one huv
  have hpv : polar q p v = 0 := (mem_perp_sup_span_pair.mp hvF).2.1
  obtain ⟨g, hg, hgu⟩ := exists_mem_radGen_apply_eq hq hF₀ (by omega) hu'F hvF hu'0 hv0 hqu' hv
  have hgΩ := mem_omegaFix.mp (radGen_le_omegaFix hq F₀ hg)
  have hgp : g p = p := hgΩ.2 p (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
  have hEv := eichler_mem_pointRadical hp hpv
  have hpuv : polar q p (u' + v) = 0 := by rw [polar_add_right, hpu', hpv, add_zero]
  have hEw := eichler_mem_pointRadical hp hpuv
  set xv : omegaGroup q hq := ⟨eichler q p v, pointRadical_le_omegaGroup hp0 hp hEv⟩
  set xw : omegaGroup q hq := ⟨eichler q p (u' + v), pointRadical_le_omegaGroup hp0 hp hEw⟩
  set g' : omegaGroup q hq := ⟨g, hgΩ.1⟩
  have hw : q (u' + v) = 1 := by rw [QuadraticMap.map_add q u' v, hqu', hv, huv, zero_add, zero_add]
  have hC := eichler_isTypeC hq hp0 hp hpuv hw
  have hxw : xw = x * xv := Subtype.ext (by
    change eichler q p (u' + v) = (x : V ≃ₗ[ZMod 2] V) * eichler q p v
    rw [hxu', eichler_mul hpu' hpv])
  have hxv : xv = g' * x * g'⁻¹ := Subtype.ext (by
    change eichler q p v = g * (x : V ≃ₗ[ZMod 2] V) * g⁻¹
    rw [hxu', eichler_conj (mem_omegaGroup.mp hgΩ.1).1, hgp, hgu])
  have hb0 := commSpace_eq_fixOf_of_not_isTypeA ρ (by omega) hdim hp hp₁ hpp₁ hc xw hEw
    hC.1.2.1 (fun hA => by
      obtain ⟨y, hy, hqy⟩ := hC.1.2.2.2.2.2
      exact hqy (hA.2.2.2.2 y hy))
  have hdimM := two_mul_finrank_fixOf_eq ρ (by omega) hdim hp0 hp hp₁ hpp₁ hc
  have hle := finrank_commSpace_mul_le (ρ x) (ρ xv)
  rw [← map_mul, ← hxw, hb0.2] at hle
  have hconj : finrank (ZMod 2) (commSpace (ρ xv)) = finrank (ZMod 2) (commSpace (ρ x)) := by
    rw [hxv, map_mul, map_mul, map_inv]
    exact finrank_commSpace_conj _ _
  omega

end Module

end CFSG.LargeExtraspecial.S14
