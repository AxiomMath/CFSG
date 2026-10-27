module

public import CFSG.LargeExtraspecial.S2SixTwo

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V] {hq : q.polarBilin.Nondegenerate}
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
variable (ρ : omegaGroup q hq →* (M ≃ₗ[ZMod 2] M))

theorem inner_of_finrank_two {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    {α : omegaGroup q hq → omegaGroup q hq} {τ : M →ₗ[ZMod 2] M} (hF : F ⊓ perp q F = ⊥)
    (hdim : finrank (ZMod 2) (perp q F) = 2 * 2) (hN : OmegaInvariant ρ F N) {p p₁ : V}
    (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0)
    (hpp₁ : polar q p p₁ = 1) (hD : RadDecomp ρ F N p p₁) (hdimN : finrank (ZMod 2) N = 2)
    (hα : IsAutOn F α) (hαp : MapsRad F α p p) (hτ : Realizes ρ F N α τ) :
    ∃ x : omegaGroup q hq, (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F ∧
      ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α g = x * g * x⁻¹ := by
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  obtain ⟨E, hE, hα₁p, hα₁p₁⟩ := hα.exists_mapsRad_conj hF (by omega) hpF hp₁F hp0 hp hp₁ hpp₁
    hαp
  have hEF : (E : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hE.2
  have hα₁ := hα.conj hEF
  have hτ₁ := hτ.conj hN hEF
  set α₁ : omegaGroup q hq → omegaGroup q hq := fun g => E * α g * E⁻¹ with hα₁def
  set τ₁ := (ρ E : M →ₗ[ZMod 2] M) ∘ₗ τ with hτ₁def
  have htwo := finrank_eq_two_mul ρ hF (by omega) hN hpF hp₁F hp0 hp₁0 hp hp₁ hD
  have hW : finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) = 1 := by
    omega
  have hW₁ : finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p₁ : Set (V ≃ₗ[ZMod 2] V))) = 1 := by
    omega
  have h1 := eq_self_of_finrank_eq_one hW (fun v hv => hτ₁.mem_fix hα₁ hα₁p hv)
    (fun v hv => hτ₁.2.1 v hv.1)
  have h2 := eq_self_of_finrank_eq_one hW₁ (fun v hv => hτ₁.mem_fix hα₁ hα₁p₁ hv)
    (fun v hv => hτ₁.2.1 v hv.1)
  have hid : ∀ v ∈ N, τ₁ v = v := by
    intro v hv
    rw [← hD.1] at hv
    obtain ⟨w, hw, w₁, hw₁, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, h1 w hw, h2 w₁ hw₁]
  have hρ : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → ∀ v ∈ N,
      ρ (α₁ g) v = ρ g v := by
    intro g hg v hv
    have := hτ₁.2.2 g hg v hv
    rw [hid _ (hN g hg v hv), hid v hv] at this
    exact this.symm
  have e1 := eq_self_of_finrank_two ρ hα₁ hF hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD hdimN hα₁p hρ
  have e2 := eq_self_of_finrank_two ρ hα₁ hF hdim hN hp₁F hpF hp₁0 hp₁ hp hp₁p hD.symm hdimN
    hα₁p₁ hρ
  have hid' := hα₁.eq_self_of_forall_radFix hF le_rfl hdim hpF hp₁F hp0 hp hp₁ hpp₁ e1 e2
  refine ⟨E⁻¹ * 1, coe_mul_mem_fixGroup (coe_inv_mem_fixGroup hEF) (one_mem _), fun g hg => ?_⟩
  refine IsAutOn.inner_of_conj (fun g hg => ?_) g hg
  have := hid' g hg
  simp only [hα₁def] at this
  rw [this]
  group

theorem timmesfeld_2_6_2_rel : ∀ (m : ℕ) {F : Submodule (ZMod 2) V} {N : Submodule (ZMod 2) M}
    {p p₁ : V} {α : omegaGroup q hq → omegaGroup q hq} {τ : M →ₗ[ZMod 2] M},
    F ⊓ perp q F = ⊥ → 2 ≤ m → finrank (ZMod 2) (perp q F) = 2 * m → OmegaInvariant ρ F N →
    p ∈ perp q F → p₁ ∈ perp q F → p ≠ 0 → q p = 0 → q p₁ = 0 → polar q p p₁ = 1 →
    RadDecomp ρ F N p p₁ → finrank (ZMod 2) N = 2 ^ (m - 1) → IsAutOn F α →
    MapsRad F α p p → Realizes ρ F N α τ →
    ∃ x : omegaGroup q hq, (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F ∧
      ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α g = x * g * x⁻¹ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F N p p₁ α τ hF hm hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD hdimN hα hαp hτ
  rcases Nat.lt_or_ge m 3 with h2 | h3
  · obtain rfl : m = 2 := by omega
    exact inner_of_finrank_two ρ hF hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD hdimN hα hαp hτ
  have hp₁0 : p₁ ≠ 0 := by
    rintro rfl
    rw [polar_zero_right] at hpp₁
    exact zero_ne_one hpp₁
  have hp₁p : polar q p₁ p = 1 := by rw [polar_comm, hpp₁]
  have h4 : 4 ≤ finrank (ZMod 2) (perp q F) := by omega
  obtain ⟨E, hE, hα₁p, hα₁p₁⟩ := hα.exists_mapsRad_conj hF h4 hpF hp₁F hp0 hp hp₁ hpp₁ hαp
  have hEF : (E : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hE.2
  have hα₁ := hα.conj hEF
  have hτ₁ := hτ.conj hN hEF
  set α₁ : omegaGroup q hq → omegaGroup q hq := fun g => E * α g * E⁻¹ with hα₁def
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hKF : fixGroup K ≤ fixGroup F := fixGroup_anti le_sup_left
  have hKK : K ⊓ perp q K = ⊥ := sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (perp q K) + 2 = finrank (ZMod 2) (perp q F) :=
    finrank_perp_sup_span_pair hq hF hpF hp₁F hpp₁
  obtain ⟨p₂, hp₂K, hp₂0, hp₂⟩ := exists_singular_mem_perp (q := q) (F := K) (by omega)
  obtain ⟨p₂₁, hp₂₁K, hp₂₁, hp₂p₂₁⟩ := exists_hyperbolic_partner hq hKK hp₂K hp₂0 hp₂
  obtain ⟨hp₂F, hpp₂, hp₁p₂⟩ := mem_perp_sup_span_pair.mp hp₂K
  obtain ⟨g, hg, hgp⟩ := exists_mem_radGen_apply_eq hq hF (by omega) hpF hp₂F hp0 hp₂0 hp hp₂
  have hgΩ := radGen_le_omegaFix hq F hg
  set g' : omegaGroup q hq := ⟨g, hgΩ.1⟩
  have hg'F : (g' : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hgΩ.2
  have hm2 := hα₁.mapsRad_apply hp0 hp hpF hα₁p hg'F
  change MapsRad F α₁ (g p) _ at hm2
  rw [hgp] at hm2
  set p₂' := (α₁ g' : V ≃ₗ[ZMod 2] V) p with hp₂'def
  have hα₁gO : (α₁ g' : V ≃ₗ[ZMod 2] V) ∈ orthogonalGroup q := (mem_omegaGroup.mp (α₁ g').2).1
  have hp₂'F : p₂' ∈ perp q F := apply_mem_perp hα₁gO (hα₁.mem g' hg'F) hpF
  have hp₂'q : q p₂' = 0 := by
    rw [hp₂'def, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hα₁gO, hp]
  have hp₂'0 : p₂' ≠ 0 := fun h => hp0 ((α₁ g' : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h)
  have hpne : p ≠ p₂ := by
    rintro rfl
    rw [hp₁p] at hp₁p₂
    exact one_ne_zero hp₁p₂
  have hp₁ne : p₁ ≠ p₂ := by
    rintro rfl
    rw [hpp₁] at hpp₂
    exact one_ne_zero hpp₂
  have hpp₂' := (hα₁.mapsRad_polar_eq_zero hF h4 hpF hp₂F hpF hp₂'F hp0 hp₂0 hp0 hp₂'0 hp hp₂ hp
    hp₂'q hpne hpp₂ hα₁p hm2).2
  have hp₁p₂' := (hα₁.mapsRad_polar_eq_zero hF h4 hp₁F hp₂F hp₁F hp₂'F hp₁0 hp₂0 hp₁0 hp₂'0 hp₁
    hp₂ hp₁ hp₂'q hp₁ne hp₁p₂ hα₁p₁ hm2).2
  have hp₂'K : p₂' ∈ perp q K := mem_perp_sup_span_pair.mpr ⟨hp₂'F, hpp₂', hp₁p₂'⟩
  obtain ⟨y, hy, hyp⟩ := exists_mem_radGen_apply_eq hq hKK (by omega) hp₂'K hp₂K hp₂'0 hp₂0
    hp₂'q hp₂
  have hyΩ := radGen_le_omegaFix hq K hy
  set y' : omegaGroup q hq := ⟨y, hyΩ.1⟩
  have hy'K : (y' : V ≃ₗ[ZMod 2] V) ∈ fixGroup K := hyΩ.2
  have hy'F : (y' : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hKF hy'K
  obtain ⟨-, hyp0, hyp₁⟩ := mem_fixGroup_sup_span_pair.mp hy'K
  have hα₂ := hα₁.conj hy'F
  have hτ₂ := hτ₁.conj hN hy'F
  set α₂ : omegaGroup q hq → omegaGroup q hq := fun g => y' * α₁ g * y'⁻¹ with hα₂def
  have hα₂p : MapsRad F α₂ p p := by
    have := hα₁p.conj hy'F hp0 hp hpF
    rwa [hyp0] at this
  have hα₂p₁ : MapsRad F α₂ p₁ p₁ := by
    have := hα₁p₁.conj hy'F hp₁0 hp₁ hp₁F
    rwa [hyp₁] at this
  have hα₂p₂ : MapsRad F α₂ p₂ p₂ := by
    have := hm2.conj hy'F hp₂'0 hp₂'q hp₂'F
    rwa [show (y' : V ≃ₗ[ZMod 2] V) p₂' = p₂ from hyp] at this
  have hKα₂ := hα₂.restrict_levi hF h4 hpF hp₁F hp0 hp₁0 hp hp₁ hα₂p hα₂p₁
  have hα₂K : IsAutOn K α₂ := hα₂.restrict hKF hKα₂
  have hα₂p₂K : MapsRad K α₂ p₂ p₂ := hα₂p₂.restrict hKF hKα₂
  obtain ⟨hWinv, hDW⟩ := timmesfeld_2_1_b2 ρ hF h3 hdim hN hpF hp₁F hp0 hp hp₁ hpp₁ hD hp₂K
    hp₂₁K hp₂0 hp₂ hp₂₁ hp₂p₂₁
  have htwo := finrank_eq_two_mul ρ hF (by omega) hN hpF hp₁F hp0 hp₁0 hp hp₁ hD
  have hdimW : finrank (ZMod 2) ↥(N ⊓ fixOf ρ (radFix q F p : Set (V ≃ₗ[ZMod 2] V))) =
      2 ^ (m - 1 - 1) := by
    have : 2 ^ (m - 1) = 2 * 2 ^ (m - 1 - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have hτ₂W := hτ₂.restrict hKF inf_le_left (fun v hv => hτ₂.mem_fix hα₂ hα₂p hv)
  obtain ⟨y₀, hy₀K, hy₀⟩ := ih (m - 1) (by omega) hKK (by omega) (by omega) hWinv hp₂K hp₂₁K
    hp₂0 hp₂ hp₂₁ hp₂p₂₁ hDW hdimW hα₂K hα₂p₂K hτ₂W
  have hy₀F : (y₀ : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hKF hy₀K
  have hy₀iF := coe_inv_mem_fixGroup hy₀F
  have hα₃ := hα₂.conj hy₀iF
  obtain ⟨-, hy₀p, hy₀p₁⟩ := mem_fixGroup_sup_span_pair.mp (coe_inv_mem_fixGroup hy₀K)
  have hα₃p : MapsRad F (fun g => y₀⁻¹ * α₂ g * y₀⁻¹⁻¹) p p := by
    have := hα₂p.conj hy₀iF hp0 hp hpF
    rwa [hy₀p] at this
  have hα₃p₁ : MapsRad F (fun g => y₀⁻¹ * α₂ g * y₀⁻¹⁻¹) p₁ p₁ := by
    have := hα₂p₁.conj hy₀iF hp₁0 hp₁ hp₁F
    rwa [hy₀p₁] at this
  have hα₃Y : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K →
      y₀⁻¹ * α₂ g * y₀⁻¹⁻¹ = g := by
    intro g hg
    rw [hy₀ g hg]
    group
  have hα₃Y' : ∀ g : omegaGroup q hq,
      (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p₁, p}) →
      y₀⁻¹ * α₂ g * y₀⁻¹⁻¹ = g := by
    rw [Set.pair_comm]
    exact hα₃Y
  have e1 := hα₃.eq_self_of_forall_levi hF h3 hdim hpF hp₁F hp0 hp hpp₁ hα₃p hα₃Y
  have e2 := hα₃.eq_self_of_forall_levi hF h3 hdim hp₁F hpF hp₁0 hp₁ hp₁p hα₃p₁ hα₃Y'
  have hid := hα₃.eq_self_of_forall_radFix hF (by omega) hdim hpF hp₁F hp0 hp hp₁ hpp₁ e1 e2
  have k1 : ∀ g : omegaGroup q hq, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      y' * α₁ g * y'⁻¹ = y₀ * g * y₀⁻¹ := by
    intro g hg
    have := hid g hg
    simp only [hα₂def] at this
    calc y' * α₁ g * y'⁻¹ = y₀ * (y₀⁻¹ * (y' * α₁ g * y'⁻¹) * y₀⁻¹⁻¹) * y₀⁻¹ := by group
      _ = y₀ * g * y₀⁻¹ := by rw [this]
  have k2 := IsAutOn.inner_of_conj (α := α₁) k1
  refine ⟨E⁻¹ * (y'⁻¹ * y₀), coe_mul_mem_fixGroup (coe_inv_mem_fixGroup hEF)
    (coe_mul_mem_fixGroup (coe_inv_mem_fixGroup hy'F) hy₀F), fun g hg => ?_⟩
  exact IsAutOn.inner_of_conj (α := α) (fun g hg => k2 g hg) g hg

theorem timmesfeld_2_6_2_omegaGroup {m : ℕ} (hm : 2 ≤ m) (hdim : finrank (ZMod 2) V = 2 * m)
    {p p₁ : V} (hp0 : p ≠ 0) (hp : q p = 0) (hp₁ : q p₁ = 0) (hpp₁ : polar q p p₁ = 1)
    (hc : IsCompl (fixOf ρ (pointRadical q p : Set (V ≃ₗ[ZMod 2] V)))
      (fixOf ρ (pointRadical q p₁ : Set (V ≃ₗ[ZMod 2] V))))
    (hdimM : finrank (ZMod 2) M = 2 ^ (m - 1)) (α : omegaGroup q hq ≃* omegaGroup q hq)
    (hαL : ∀ g : omegaGroup q hq,
      (g : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p ↔ (α g : V ≃ₗ[ZMod 2] V) ∈ pointRadical q p)
    (τ : M ≃ₗ[ZMod 2] M) (hτ : ∀ g v, τ (ρ g v) = ρ (α g) (τ v)) :
    ∃ x : omegaGroup q hq, ∀ g, α g = x * g * x⁻¹ := by
  have hD : RadDecomp ρ ⊥ ⊤ p p₁ := by
    rw [RadDecomp, radFix_bot, radFix_bot, top_inf_eq, top_inf_eq]
    exact ⟨hc.sup_eq_top, hc.inf_eq_bot⟩
  have hfix : ∀ g : V ≃ₗ[ZMod 2] V, g ∈ fixGroup (⊥ : Submodule (ZMod 2) V) := fun g => by
    rw [fixGroup_bot]
    exact Subgroup.mem_top g
  have hperp : ∀ x : V, x ∈ perp q (⊥ : Submodule (ZMod 2) V) := fun x => by
    rw [perp_bot]
    exact Submodule.mem_top
  have hα : IsAutOn (⊥ : Submodule (ZMod 2) V) (α : omegaGroup q hq → omegaGroup q hq) :=
    { mem := fun g _ => hfix _
      map_mul := fun g h _ _ => map_mul α g h
      inj := fun g h _ _ e => α.injective e
      surj := fun h _ => ⟨α.symm h, hfix _, α.apply_symm_apply h⟩ }
  have hαp : MapsRad (⊥ : Submodule (ZMod 2) V) (α : omegaGroup q hq → omegaGroup q hq) p p := by
    intro g _
    rw [radFix_bot]
    exact hαL g
  have hτ' : Realizes ρ ⊥ ⊤ (α : omegaGroup q hq → omegaGroup q hq) (τ : M →ₗ[ZMod 2] M) :=
    ⟨fun _ _ => Submodule.mem_top, fun v _ h => τ.map_eq_zero_iff.mp h,
      fun g _ v _ => hτ g v⟩
  obtain ⟨x, -, hx⟩ := timmesfeld_2_6_2_rel ρ m (bot_inf_eq _) hm
    (by rw [perp_bot, finrank_top]; exact hdim) (fun g _ v _ => Submodule.mem_top) (hperp p)
    (hperp p₁) hp0 hp hp₁ hpp₁ hD (by rw [finrank_top]; exact hdimM) hα hαp hτ'
  exact ⟨x, fun g => hx g (hfix _)⟩

end S2

end CFSG.LargeExtraspecial
