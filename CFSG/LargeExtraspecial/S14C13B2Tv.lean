module

public import CFSG.LargeExtraspecial.S14C13B2Rank
public import CFSG.LargeExtraspecial.S14C13B2Flag

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LargeExtraspecial.OrthoF2
open CFSG.LargeExtraspecial.S2
open TauCeti.QuadraticMap (orthogonalGroup)
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_conj)

section Linear

variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]

theorem mul_self_eq_one_of_finrank_commSpace_eq_one {e : M ≃ₗ[ZMod 2] M}
    (h : finrank (ZMod 2) (commSpace e) = 1) : e * e = 1 := by
  obtain ⟨c, hc0, hc⟩ := finrank_eq_one_iff'.mp h
  have hspan : ∀ x ∈ commSpace e, ∃ a : ZMod 2, a • (c : M) = x := by
    intro x hx
    obtain ⟨a, ha⟩ := hc ⟨x, hx⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  have h2 : ∀ w : M, w + w = 0 := fun w => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hcc : e c = c := by
    obtain ⟨a, ha⟩ := hspan _ (sub_mem_commSpace e c)
    rcases zmod2_eq_zero_or_eq_one a with rfl | rfl
    · rw [zero_smul] at ha
      exact (sub_eq_zero.mp ha.symm)
    · exfalso
      rw [one_smul] at ha
      have h3 : e (c : M) = 0 := by rw [← eq_sub_iff_add_eq.mp ha, h2]
      exact hc0 (Subtype.ext (e.injective (h3.trans (map_zero e).symm)))
  refine LinearEquiv.ext fun v => ?_
  obtain ⟨a, ha⟩ := hspan _ (sub_mem_commSpace e v)
  have hv : e v = v + a • (c : M) := by rw [ha]; abel
  change e (e v) = v
  rw [hv, map_add, map_smul, hcc, hv, add_assoc, h2, add_zero]

end Linear

section Module

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V} {hq : q.polarBilin.Nondegenerate}
  {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
  (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

include hq in
theorem exists_singular_mem_commSpace {g : V ≃ₗ[ZMod 2] V} (hg : g ∈ omegaGroup q hq)
    (hgg : g * g = 1) (hg1 : g ≠ 1) : ∃ p ∈ commSpace g, p ≠ 0 ∧ q p = 0 := by
  obtain ⟨hgO, hev⟩ := mem_omegaGroup.mp hg
  have h1 := one_le_finrank_commSpace hg1
  have h2 : 2 ≤ finrank (ZMod 2) (commSpace g) := by
    obtain ⟨k, hk⟩ := hev
    omega
  set T := commSpace g
  set b := Module.finBasis (ZMod 2) T
  set x : T := b ⟨0, by omega⟩
  set y : T := b ⟨1, by omega⟩
  have hli : LinearIndependent (ZMod 2) ![x, y] := by
    have := b.linearIndependent.comp ![⟨0, by omega⟩, ⟨1, by omega⟩] (by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨hx0, hy0, hxy⟩ := linearIndependent_pair_iff.mp hli
  have hpol : polar q x y = 0 := polar_commSpace_eq_zero hgO hgg x.2 y.2
  by_cases hqx : q x = 0
  · exact ⟨x, x.2, fun h => hx0 (Subtype.ext h), hqx⟩
  by_cases hqy : q y = 0
  · exact ⟨y, y.2, fun h => hy0 (Subtype.ext h), hqy⟩
  refine ⟨x + y, Submodule.add_mem _ x.2 y.2, fun h => hxy (Subtype.ext ?_), ?_⟩
  · have := congrArg (fun v => v + (y : V)) h
    simpa [add_assoc, ← two_smul (ZMod 2) (y : V), show (2 : ZMod 2) = 0 from rfl] using this
  · rw [QuadraticMap.map_add q x y, hpol, zmod2_eq_one_of_ne_zero hqx,
      zmod2_eq_one_of_ne_zero hqy]
    rfl

omit [FiniteDimensional (ZMod 2) M] in
theorem apply_mem_fixOf_of_apply_eq {p : V} (hp0 : p ≠ 0) (hp : q p = 0) (y : omegaGroup q hq)
    (hyp : (y : V ≃ₗ[ZMod 2] V) p = p) {v : M}
    (hv : v ∈ fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V))) :
    ρ y v ∈ fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) := by
  intro x hx
  have hperp : ∀ w : V, w ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun w => by
    rw [perp_bot]; exact Submodule.mem_top
  have hyO : ((y⁻¹ : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q :=
    (mem_omegaGroup.mp (y⁻¹).2).1
  have hyip : ((y⁻¹ : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) p = p := by
    rw [show ((y⁻¹ : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) = (y : V ≃ₗ[ZMod 2] V)⁻¹ from rfl]
    conv_lhs => rw [← hyp]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' _ p
  have hconj : ((y⁻¹ * x * y : omegaGroup q hq) : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p := by
    have := conj_mem_radFix hq (F := ⊥) hp0 hp (hperp p) hyO (by rw [fixGroup_bot]; trivial)
      (t := (x : V ≃ₗ[ZMod 2] V)) (by rw [radFix_bot]; exact hx)
    rw [radFix_bot, hyip] at this
    convert this using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  have h1 := hv _ hconj
  rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h1
  have h2 := congrArg (ρ y) h1
  rwa [← LinearEquiv.mul_apply, ← map_mul, ← LinearEquiv.mul_apply, ← map_mul,
    mul_inv_cancel, one_mul] at h2

theorem finrank_commSpace_ne_one (hdim : finrank (ZMod 2) V = 8)
    (hdimM : 5 ≤ finrank (ZMod 2) M) {p₀ p₀₁ : V} (hp₀0 : p₀ ≠ 0) (hp₀ : q p₀ = 0)
    (hp₀₁ : q p₀₁ = 0) (hpp₀ : polar q p₀ p₀₁ = 1)
    (hc₀ : IsCompl (fixOf ρ (pointRadical q p₀ : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₀₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hfaith : ∀ g, ρ g = 1 → g = 1) (g : omegaGroup q hq) :
    finrank (ZMod 2) (commSpace (ρ g)) ≠ 1 := by
  intro h1
  have hperp : ∀ y : V, y ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun y => by
    rw [perp_bot]; exact Submodule.mem_top
  have hgg : g * g = 1 :=
    hfaith _ (by rw [map_mul]; exact mul_self_eq_one_of_finrank_commSpace_eq_one h1)
  have hgg' : (g : V ≃ₗ[ZMod 2] V) * g = 1 := congrArg Subtype.val hgg
  have hg1 : (g : V ≃ₗ[ZMod 2] V) ≠ 1 := fun h => by
    have : g = 1 := Subtype.ext h
    rw [this, map_one] at h1
    have h0 : commSpace (1 : M ≃ₗ[ZMod 2] M) = ⊥ := by
      rw [eq_bot_iff]; rintro _ ⟨v, rfl⟩; simp
    rw [h0, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨p, hpT, hp0, hp⟩ := exists_singular_mem_commSpace (hq := hq) g.2 hgg' hg1
  have hgp : (g : V ≃ₗ[ZMod 2] V) p = p := mem_fixSpace.mp (commSpace_le_fixSpace hgg' hpT)
  obtain ⟨p₁, -, hp₁, hpp₁⟩ := exists_hyperbolic_partner hq (bot_inf_eq _) (hperp p) hp0 hp
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hD := radDecomp_of_pair ρ (bot_inf_eq _) (by rw [perp_bot, finrank_top]; omega)
    (omegaInvariant_top ρ) (hperp p₀) (hperp p₀₁) (hperp p) (hperp p₁) hp₀0 hp0 hp₀ hp₀₁ hp
    hp₁ hpp₀ hpp₁ (radDecomp_of_isCompl ρ hc₀)
  rw [RadDecomp, radFix_bot, radFix_bot, top_inf_eq, top_inf_eq] at hD
  have hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))) := IsCompl.of_eq hD.2 hD.1
  have hgF : (g : V ≃ₗ[ZMod 2] V) ∈ omegaFix q hq ⊥ := by rw [omegaFix_bot]; exact g.2
  obtain ⟨ℓ, hℓ, hy⟩ := exists_mem_radFix_inv_mul_mem hq (hperp p) (hperp p₁) hp0 hp hp₁ hpp₁
    hgF hgp
  rw [radFix_bot] at hℓ
  obtain ⟨hyΩ, hyF⟩ := mem_omegaFix.mp hy
  obtain ⟨-, hyp, hyp₁⟩ := mem_fixGroup_sup_span_pair.mp hyF
  set ℓΩ : omegaGroup q hq := ⟨ℓ, pointRadical_le_omegaGroup hp0 hp hℓ⟩ with hℓΩ
  set yΩ : omegaGroup q hq := ⟨ℓ⁻¹ * g, hyΩ⟩ with hyΩdef
  have hgly : g = ℓΩ * yΩ := Subtype.ext (by
    change (g : V ≃ₗ[ZMod 2] V) = ℓ * (ℓ⁻¹ * g)
    rw [mul_inv_cancel_left])
  set P := fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)) with hP
  set P₁ := fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V)) with hP₁
  by_cases hy1 : yΩ = 1
  · have hgL : (g : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p := by
      rw [hgly, hy1, mul_one]; exact hℓ
    have h2 := two_mul_finrank_fixOf_eq ρ (m := 4) (by norm_num) (by rw [hdim]) hp0 hp hp₁
      hpp₁ hc
    by_cases hA : IsTypeA q g 2
    · have := finrank_le_four_mul_of_isTypeA ρ (m := 4) (by norm_num) (by rw [hdim]) hp0 hp hp₁
        hpp₁ hc g hgL hg1 hA
      omega
    · have hb := commSpace_eq_fixOf_of_not_isTypeA ρ (m := 4) (by norm_num) (by rw [hdim]) hp
        hp₁ hpp₁ hc g hgL hg1 hA
      rw [hb.2] at h1
      omega
  have hyO : (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp hyΩ).1
  have hyy : (ℓ⁻¹ * g) * (ℓ⁻¹ * g) = (1 : V ≃ₗ[ZMod 2] V) := by
    have hmem1 : (ℓ⁻¹ * g) * (ℓ⁻¹ * g) ∈ radFix q ⊥ p := by
      have hc1 := conj_mem_radFix hq (F := ⊥) hp0 hp (hperp p) (mem_omegaGroup.mp g.2).1
        (by rw [fixGroup_bot]; trivial) (t := ℓ⁻¹) (by rw [radFix_bot]; exact inv_mem hℓ)
      rw [hgp] at hc1
      have e : (ℓ⁻¹ * g) * (ℓ⁻¹ * g) = ℓ⁻¹ * ((g : V ≃ₗ[ZMod 2] V) * ℓ⁻¹ *
          (g : V ≃ₗ[ZMod 2] V)⁻¹) * ((g : V ≃ₗ[ZMod 2] V) * g) := by group
      rw [e, hgg', mul_one]
      exact mul_mem (by rw [radFix_bot]; exact inv_mem hℓ) hc1
    have hmem2 : (ℓ⁻¹ * g) * (ℓ⁻¹ * g) ∈
        omegaFix q hq ((⊥ : Submodule (ZMod 2) V) ⊔ Submodule.span (ZMod 2) {p, p₁}) :=
      mul_mem hy hy
    have hbot := radFix_inf_omegaFix_eq_bot hq (F := ⊥) hp0 hp hpp₁
    have : (ℓ⁻¹ * g) * (ℓ⁻¹ * g) ∈ (⊥ : Subgroup (V ≃ₗ[ZMod 2] V)) := hbot ▸ ⟨hmem1, hmem2⟩
    exact Subgroup.mem_bot.mp this
  have hy1' : (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) ≠ 1 := fun h => hy1 (Subtype.ext h)
  set F₂ := (⊥ : Submodule (ZMod 2) V) ⊔ Submodule.span (ZMod 2) {p, p₁} with hF₂def
  have hF₂ : F₂ ⊓ perp q F₂ = ⊥ :=
    sup_span_pair_inf_perp_eq_bot (bot_inf_eq _) (hperp p) (hperp p₁) hpp₁
  have hdimF : finrank (ZMod 2) (perp q F₂) + 2 = 8 := by
    have := finrank_perp_sup_span_pair hq (bot_inf_eq _) (hperp p) (hperp p₁) hpp₁
    rw [perp_bot, finrank_top, hdim] at this
    exact this
  have hcomm_le : commSpace (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) ≤ perp q F₂ := by
    rintro _ ⟨v, rfl⟩
    rw [mem_perp]
    intro f hf
    have hyf : (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) f = f := hyF f hf
    change polar q f ((ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) v - v) = 0
    rw [polar_sub_right, ← hyf, TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hyO,
      hyf, sub_self]
  have hk := two_mul_finrank_le_of_polar_eq_zero hq hF₂ hcomm_le
    (fun x hx y hy => polar_commSpace_eq_zero hyO hyy hx hy)
  have hkev := (mem_omegaGroup.mp hyΩ).2
  have hk1 := one_le_finrank_commSpace hy1'
  have hfix := finrank_commSpace_add_finrank_fixSpace (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V)
  rw [hdim] at hfix
  have hF₂fix : F₂ ≤ fixSpace (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) := fun f hf => mem_fixSpace.mpr (hyF f hf)
  have hsup : fixSpace (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) ⊔ perp q F₂ = ⊤ := by
    rw [eq_top_iff]
    have hcompl : F₂ ⊔ perp q F₂ = ⊤ := by
      refine Submodule.eq_top_of_finrank_eq ?_
      have := Submodule.finrank_sup_add_finrank_inf_eq F₂ (perp q F₂)
      rw [hF₂, finrank_bot, add_zero] at this
      have hF2dim : finrank (ZMod 2) F₂ = 2 := by
        have := Submodule.finrank_add_finrank_le_of_disjoint (disjoint_iff.mpr hF₂)
        have hsp := finrank_span_pair (linearIndependent_pair_iff.mpr ⟨hp0, hp₁0, fun h => by
          rw [h, polar_self_eq_zero q p₁] at hpp₁; exact zero_ne_one hpp₁⟩)
        rw [hF₂def, bot_sup_eq, hsp]
      rw [this, hF2dim, hdim]
      omega
    rw [← hcompl]
    exact sup_le_sup_right hF₂fix _
  have hC4 : 4 ≤ finrank (ZMod 2) ↥(fixSpace (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) ⊓ perp q F₂) := by
    have := Submodule.finrank_sup_add_finrank_inf_eq (fixSpace (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V))
      (perp q F₂)
    rw [hsup, finrank_top, hdim] at this
    obtain ⟨r, hr⟩ := hkev
    omega
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ fixSpace (ℓ⁻¹ * g : V ≃ₗ[ZMod 2] V) ⊓ perp q F₂, q u ≠ 0 := by
    by_contra hall
    push Not at hall
    have := two_mul_finrank_le_of_polar_eq_zero hq hF₂ inf_le_right (fun x hx y hy => by
      rw [polar, hall _ (Submodule.add_mem _ hx hy), hall x hx, hall y hy]; rfl)
    omega
  have hu1' : q u = 1 := zmod2_eq_one_of_ne_zero hu1
  obtain ⟨huy, huF⟩ := hu
  have hp₁u : polar q p₁ u = 0 := (mem_perp_sup_span_pair.mp huF).2.2
  have hcL := eichler_mem_pointRadical hp₁ hp₁u
  have hC := eichler_isTypeC hq hp₁0 hp₁ hp₁u hu1'
  set cΩ : omegaGroup q hq := ⟨eichler q p₁ u, pointRadical_le_omegaGroup hp₁0 hp₁ hcL⟩
  have hcy : cΩ * yΩ = yΩ * cΩ := Subtype.ext (by
    change eichler q p₁ u * (ℓ⁻¹ * g) = (ℓ⁻¹ * g) * eichler q p₁ u
    have := eichler_conj hyO p₁ u
    rw [hyp₁, mem_fixSpace.mp huy] at this
    conv_lhs => rw [← this]
    group)
  have hb0 := commSpace_eq_fixOf_of_not_isTypeA ρ (m := 4) (by norm_num) (by rw [hdim]) hp₁ hp
    (by rw [polar_comm, hpp₁]) hc.symm cΩ hcL hC.1.2.1 (fun hA => by
      obtain ⟨z, hz, hqz⟩ := hC.1.2.2.2.2.2
      exact hqz (hA.2.2.2.2 z hz))
  have hℓP : ∀ v ∈ P, ρ ℓΩ v = v := fun v hv => hv ℓΩ hℓ
  have hℓQ : ∀ v, ρ ℓΩ v - v ∈ P := fun v =>
    sub_mem_fixOf_of_mem_pointRadical ρ (m := 4) (by norm_num) (by rw [hdim]) hp0 hp hp₁ hpp₁ hc
      ℓΩ hℓ v
  have hyP : ∀ v ∈ P, ρ yΩ v ∈ P := fun v hv => apply_mem_fixOf_of_apply_eq ρ hp0 hp yΩ hyp hv
  have hyP₁ : ∀ v ∈ P₁, ρ yΩ v ∈ P₁ := fun v hv =>
    apply_mem_fixOf_of_apply_eq ρ hp₁0 hp₁ yΩ hyp₁ hv
  set φy : M →ₗ[ZMod 2] M := (ρ yΩ : M →ₗ[ZMod 2] M) - 1 with hφy
  set ψ : M →ₗ[ZMod 2] M := (ρ cΩ : M →ₗ[ZMod 2] M) - 1 with hψ
  have hφyv : ∀ v, φy v = ρ yΩ v - v := fun v => rfl
  have hψv : ∀ v, ψ v = ρ cΩ v - v := fun v => rfl
  have hψφ : ∀ v, ψ (φy v) = φy (ψ v) := fun v => by
    have hcomm : ρ cΩ (ρ yΩ v) = ρ yΩ (ρ cΩ v) := by
      rw [← LinearEquiv.mul_apply, ← map_mul, hcy, map_mul, LinearEquiv.mul_apply]
    rw [hψv, hφyv, hφyv, hψv, map_sub, map_sub, hcomm]
    abel
  have hb1 : fixSpace (ρ cΩ) = P₁ := hb0.1
  have hb2 : commSpace (ρ cΩ) = P₁ := hb0.2
  have hψP₁ : ∀ v, ψ v ∈ P₁ := fun v => by rw [← hb2]; exact sub_mem_commSpace _ v
  have hψker : ∀ v ∈ P₁, ψ v = 0 := fun v hv => by
    rw [hψv, sub_eq_zero]; exact mem_fixSpace.mp (by rw [hb1]; exact hv)
  have hψinj : ∀ v ∈ P, ψ v = 0 → v = 0 := fun v hv h0 => by
    have hv₁ : v ∈ P₁ := by
      rw [← hb1, mem_fixSpace]; rw [hψv, sub_eq_zero] at h0; exact h0
    have : v ∈ P ⊓ P₁ := ⟨hv, hv₁⟩
    rw [hc.inf_eq_bot] at this
    exact this
  have hψonto : ∀ w ∈ P₁, ∃ v ∈ P, ψ v = w := by
    intro w hw
    rw [← hb2] at hw
    obtain ⟨m, rfl⟩ := mem_commSpace.mp hw
    have hm : m ∈ P ⊔ P₁ := by rw [hc.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨m₀, hm₀, m₁, hm₁, rfl⟩ := Submodule.mem_sup.mp hm
    refine ⟨m₀, hm₀, ?_⟩
    have h1 := hψker m₁ hm₁
    rw [hψv] at h1
    rw [hψv, map_add, add_sub_add_comm, h1, add_zero]
  have hPφ : (P.map φy).map ψ = P₁.map φy := by
    ext w
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨ψ v, hψP₁ v, (hψφ v).symm⟩
    · rintro ⟨w₁, hw₁, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hψonto w₁ hw₁
      exact ⟨φy v, ⟨v, hv, rfl⟩, hψφ v⟩
  have hφyP : P.map φy ≤ P := by
    rintro _ ⟨v, hv, rfl⟩
    exact sub_mem (hyP v hv) hv
  have hφyP₁ : P₁.map φy ≤ P₁ := by
    rintro _ ⟨v, hv, rfl⟩
    exact sub_mem (hyP₁ v hv) hv
  have hr1 : finrank (ZMod 2) ((P.map φy).map ψ) = finrank (ZMod 2) (P.map φy) := by
    have h := finrank_map_add_finrank_inf_ker_of ψ (P.map φy)
    have hk : P.map φy ⊓ LinearMap.ker ψ = ⊥ := by
      rw [eq_bot_iff]
      rintro v ⟨hv, hv0⟩
      exact hψinj v (hφyP hv) hv0
    rw [hk, finrank_bot, add_zero] at h
    exact h
  set φ : M →ₗ[ZMod 2] M := (ρ g : M →ₗ[ZMod 2] M) - 1 with hφ
  have hφv : ∀ v, φ v = ρ ℓΩ (ρ yΩ v) - v := fun v => by
    change ρ g v - v = _
    rw [hgly, map_mul, LinearEquiv.mul_apply]
  have hφP : P.map φ = P.map φy := by
    ext w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, by rw [hφv, hℓP _ (hyP v hv), hφyv]⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨v, hv, by rw [hφv, hℓP _ (hyP v hv), hφyv]⟩
  have hφQ : ((⊤ : Submodule (ZMod 2) M).map φ).map P.mkQ =
      ((⊤ : Submodule (ZMod 2) M).map φy).map P.mkQ := by
    have hmk : ∀ v, P.mkQ (φ v) = P.mkQ (φy v) := fun v => by
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, hφv, hφyv]
      have := hℓQ (ρ yΩ v)
      convert this using 1
      abel
    ext w
    constructor
    · rintro ⟨_, ⟨v, -, rfl⟩, rfl⟩
      exact ⟨φy v, ⟨v, Submodule.mem_top, rfl⟩, (hmk v).symm⟩
    · rintro ⟨_, ⟨v, -, rfl⟩, rfl⟩
      exact ⟨φ v, ⟨v, Submodule.mem_top, rfl⟩, hmk v⟩
  have hflag := finrank_map_add_finrank_map_mkQ_le φ (le_top : P ≤ ⊤) (by rw [hφP]; exact hφyP)
  have htop : finrank (ZMod 2) ((⊤ : Submodule (ZMod 2) M).map φ) = 1 := by
    rw [Submodule.map_top]; exact h1
  have hP₁Q : finrank (ZMod 2) (P₁.map φy) ≤
      finrank (ZMod 2) (((⊤ : Submodule (ZMod 2) M).map φy).map P.mkQ) := by
    have h := finrank_map_add_finrank_inf_ker_of P.mkQ (P₁.map φy)
    have hk : P₁.map φy ⊓ LinearMap.ker P.mkQ = ⊥ := by
      rw [Submodule.ker_mkQ, eq_bot_iff]
      rintro v ⟨hv, hv'⟩
      have : v ∈ P ⊓ P₁ := ⟨hv', hφyP₁ hv⟩
      rw [hc.inf_eq_bot] at this
      exact this
    rw [hk, finrank_bot, add_zero] at h
    rw [← h]
    exact Submodule.finrank_mono (Submodule.map_mono (Submodule.map_mono le_top))
  rw [hφP, hφQ, htop] at hflag
  rw [hPφ] at hr1
  have hz : finrank (ZMod 2) (P.map φy) = 0 := by omega
  have hz₁ : finrank (ZMod 2) (P₁.map φy) = 0 := by omega
  rw [Submodule.finrank_eq_zero] at hz hz₁
  apply hy1
  apply hfaith
  refine LinearEquiv.ext fun v => ?_
  have hv : v ∈ P ⊔ P₁ := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨v₀, hv₀, v₁, hv₁, rfl⟩ := Submodule.mem_sup.mp hv
  have e₀ : φy v₀ = 0 := by
    have : φy v₀ ∈ P.map φy := ⟨v₀, hv₀, rfl⟩
    rw [hz] at this; exact this
  have e₁ : φy v₁ = 0 := by
    have : φy v₁ ∈ P₁.map φy := ⟨v₁, hv₁, rfl⟩
    rw [hz₁] at this; exact this
  rw [hφyv, sub_eq_zero] at e₀ e₁
  change ρ yΩ (v₀ + v₁) = v₀ + v₁
  rw [map_add, e₀, e₁]

end Module

end CFSG.LargeExtraspecial.S14
