module

public import CFSG.LargeExtraspecial.S2SixSp

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module CFSG.RankThree.OrthogonalInvolutions OrthoF2
open LinearMap (BilinForm)

namespace S2

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {f : BilinForm (ZMod 2) V}
variable [FiniteDimensional (ZMod 2) V]

theorem sp_timmesfeld_2_6_2_rel (hf : f.IsAlt) (hnd : f.Nondegenerate) :
    ∀ (m : ℕ) {F : Submodule (ZMod 2) V} {p p₁ : V} {α : SpG f → SpG f},
    F ⊓ spPerp f F = ⊥ → 1 ≤ m → finrank (ZMod 2) (spPerp f F) = 2 * m → p ∈ spPerp f F →
    p₁ ∈ spPerp f F → f p p₁ = 1 → SpAutOn F α → SpMapsRad F α p p →
    ∃ x : SpG f, (x : V ≃ₗ[ZMod 2] V) ∈ fixGroup F ∧
      ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α g = x * g * x⁻¹ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro F p p₁ α hF hm hdim hpF hp₁F hpp₁ hα hαp
  obtain ⟨hp0, hp₁0, -⟩ := linearIndependent_pair_iff.mp (linearIndependent_of_apply_eq_one hf hpp₁)
  have hp₁p : f p₁ p = 1 := by rw [isAlt_symm hf, hpp₁]
  obtain ⟨E, hE, hα₁p, hα₁p₁⟩ := hα.exists_mapsRad_conj hf hnd hF hpF hp₁F hpp₁ hαp
  have hEF : (E : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hE.2
  have hα₁ := hα.conj hEF
  set α₁ : SpG f → SpG f := fun g => E * α g * E⁻¹ with hα₁def
  suffices hid : ∃ z : SpG f, (z : V ≃ₗ[ZMod 2] V) ∈ fixGroup F ∧
      ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F → α₁ g = z * g * z⁻¹ by
    obtain ⟨z, hzF, hz⟩ := hid
    exact ⟨E⁻¹ * z, sp_coe_mul_mem_fixGroup (sp_coe_inv_mem_fixGroup hEF) hzF,
      fun g hg => SpAutOn.inner_of_conj (α := α) hz g hg⟩
  rcases Nat.lt_or_ge m 2 with h1 | h2
  ·
    obtain rfl : m = 1 := by omega
    refine ⟨1, one_mem _, fun g hg => ?_⟩
    have e1 := hα₁.eq_self_of_finrank_two hf hnd hF hdim hpF hp₁F hpp₁ hα₁p
    have e2 := hα₁.eq_self_of_finrank_two hf hnd hF hdim hp₁F hpF hp₁p hα₁p₁
    rw [hα₁.eq_self_of_forall_radFix hf hnd hF hdim hpF hp₁F hpp₁ e1 e2 g hg]
    group
  set K := F ⊔ Submodule.span (ZMod 2) {p, p₁} with hKdef
  have hKF : fixGroup K ≤ fixGroup F := fixGroup_anti le_sup_left
  have hKK : K ⊓ spPerp f K = ⊥ := sup_span_pair_inf_spPerp_eq_bot hf hF hpF hp₁F hpp₁
  have hKdim : finrank (ZMod 2) (spPerp f K) + 2 = finrank (ZMod 2) (spPerp f F) :=
    finrank_spPerp_sup_span_pair hf hnd hF hpF hp₁F hpp₁
  have hne : spPerp f K ≠ ⊥ := fun h => by
    rw [h, finrank_bot] at hKdim
    omega
  obtain ⟨p₂, hp₂K, hp₂0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨p₂₁, hp₂₁K, hp₂p₂₁⟩ := sp_exists_partner hf hnd hKK hp₂K hp₂0
  obtain ⟨hp₂F, hpp₂, hp₁p₂⟩ := mem_spPerp_sup_span_pair.mp hp₂K
  obtain ⟨g, hg, hgp⟩ := exists_mem_spRadGen_apply_eq hf hnd hF hpF hp₂F hp0 hp₂0
  have hgS := spRadGen_le_spFix F hg
  set g' : SpG f := ⟨g, hgS.1⟩
  have hg'F : (g' : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hgS.2
  have hm2 := hα₁.mapsRad_apply hf hnd hp0 hpF hα₁p hg'F
  change SpMapsRad F α₁ (g p) _ at hm2
  rw [hgp] at hm2
  set p₂' := (α₁ g' : V ≃ₗ[ZMod 2] V) p with hp₂'def
  have hp₂'F : p₂' ∈ spPerp f F := apply_mem_spPerp (α₁ g').2 (hα₁.mem g' hg'F) hpF
  have hp₂'0 : p₂' ≠ 0 := fun h => hp0 ((α₁ g' : V ≃ₗ[ZMod 2] V).map_eq_zero_iff.mp h)
  have hpne : p ≠ p₂ := by
    rintro rfl
    rw [hp₁p] at hp₁p₂
    exact one_ne_zero hp₁p₂
  have hp₁ne : p₁ ≠ p₂ := by
    rintro rfl
    rw [hpp₁] at hpp₂
    exact one_ne_zero hpp₂
  have hpp₂' := (hα₁.mapsRad_polar_eq_zero hf hnd hF hpF hp₂F hpF hp₂'F hp0 hp₂0 hp0 hp₂'0 hpne
    hpp₂ hα₁p hm2).2
  have hp₁p₂' := (hα₁.mapsRad_polar_eq_zero hf hnd hF hp₁F hp₂F hp₁F hp₂'F hp₁0 hp₂0 hp₁0 hp₂'0
    hp₁ne hp₁p₂ hα₁p₁ hm2).2
  have hp₂'K : p₂' ∈ spPerp f K := mem_spPerp_sup_span_pair.mpr ⟨hp₂'F, hpp₂', hp₁p₂'⟩
  obtain ⟨y, hy, hyp⟩ := exists_mem_spRadGen_apply_eq hf hnd hKK hp₂'K hp₂K hp₂'0 hp₂0
  have hyS := spRadGen_le_spFix K hy
  set y' : SpG f := ⟨y, hyS.1⟩
  have hy'K : (y' : V ≃ₗ[ZMod 2] V) ∈ fixGroup K := hyS.2
  have hy'F : (y' : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hKF hy'K
  obtain ⟨-, hyp0, hyp₁⟩ := mem_fixGroup_sup_span_pair.mp hy'K
  have hα₂ := hα₁.conj hy'F
  set α₂ : SpG f → SpG f := fun g => y' * α₁ g * y'⁻¹ with hα₂def
  have hα₂p : SpMapsRad F α₂ p p := by
    have := hα₁p.conj hf hnd hy'F hp0 hpF
    rwa [hyp0] at this
  have hα₂p₁ : SpMapsRad F α₂ p₁ p₁ := by
    have := hα₁p₁.conj hf hnd hy'F hp₁0 hp₁F
    rwa [hyp₁] at this
  have hα₂p₂ : SpMapsRad F α₂ p₂ p₂ := by
    have := hm2.conj hf hnd hy'F hp₂'0 hp₂'F
    rwa [show (y' : V ≃ₗ[ZMod 2] V) p₂' = p₂ from hyp] at this
  have hKα₂ := hα₂.restrict_levi hf hnd hF hpF hp₁F hp0 hp₁0 hα₂p hα₂p₁
  have hα₂K : SpAutOn K α₂ := hα₂.restrict hKF hKα₂
  have hα₂p₂K : SpMapsRad K α₂ p₂ p₂ := hα₂p₂.restrict hKF hKα₂
  obtain ⟨y₀, hy₀K, hy₀⟩ := ih (m - 1) (by omega) hKK (by omega) (by omega) hp₂K hp₂₁K hp₂p₂₁
    hα₂K hα₂p₂K
  have hy₀F : (y₀ : V ≃ₗ[ZMod 2] V) ∈ fixGroup F := hKF hy₀K
  have hy₀iF := sp_coe_inv_mem_fixGroup hy₀F
  have hα₃ := hα₂.conj hy₀iF
  obtain ⟨-, hy₀p, hy₀p₁⟩ := mem_fixGroup_sup_span_pair.mp (sp_coe_inv_mem_fixGroup hy₀K)
  have hα₃p : SpMapsRad F (fun g => y₀⁻¹ * α₂ g * y₀⁻¹⁻¹) p p := by
    have := hα₂p.conj hf hnd hy₀iF hp0 hpF
    rwa [hy₀p] at this
  have hα₃p₁ : SpMapsRad F (fun g => y₀⁻¹ * α₂ g * y₀⁻¹⁻¹) p₁ p₁ := by
    have := hα₂p₁.conj hf hnd hy₀iF hp₁0 hp₁F
    rwa [hy₀p₁] at this
  have hα₃Y : ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup K →
      y₀⁻¹ * α₂ g * y₀⁻¹⁻¹ = g := by
    intro g hg
    rw [hy₀ g hg]
    group
  have hα₃Y' : ∀ g : SpG f,
      (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup (F ⊔ Submodule.span (ZMod 2) {p₁, p}) →
      y₀⁻¹ * α₂ g * y₀⁻¹⁻¹ = g := by
    rw [Set.pair_comm]
    exact hα₃Y
  have e1 := hα₃.eq_self_of_forall_levi hf hnd hF h2 hdim hpF hp₁F hpp₁ hα₃p hα₃Y
  have e2 := hα₃.eq_self_of_forall_levi hf hnd hF h2 hdim hp₁F hpF hp₁p hα₃p₁ hα₃Y'
  have hid := hα₃.eq_self_of_forall_radFix hf hnd hF hdim hpF hp₁F hpp₁ e1 e2
  have k1 : ∀ g : SpG f, (g : V ≃ₗ[ZMod 2] V) ∈ fixGroup F →
      y' * α₁ g * y'⁻¹ = y₀ * g * y₀⁻¹ := by
    intro g hg
    have := hid g hg
    simp only [hα₂def] at this
    calc y' * α₁ g * y'⁻¹ = y₀ * (y₀⁻¹ * (y' * α₁ g * y'⁻¹) * y₀⁻¹⁻¹) * y₀⁻¹ := by group
      _ = y₀ * g * y₀⁻¹ := by rw [this]
  exact ⟨y'⁻¹ * y₀, sp_coe_mul_mem_fixGroup (sp_coe_inv_mem_fixGroup hy'F) hy₀F,
    fun g hg => SpAutOn.inner_of_conj (α := α₁) k1 g hg⟩

theorem sp_timmesfeld_2_6_2_spGroup (hf : f.IsAlt) (hnd : f.Nondegenerate) {m : ℕ} (hm : 1 ≤ m)
    (hdim : finrank (ZMod 2) V = 2 * m) {p : V} (hp0 : p ≠ 0) (α : SpG f ≃* SpG f)
    (hαL : ∀ g : SpG f,
      (g : V ≃ₗ[ZMod 2] V) ∈ spPointRadical f p ↔ (α g : V ≃ₗ[ZMod 2] V) ∈ spPointRadical f p) :
    ∃ x : SpG f, ∀ g, α g = x * g * x⁻¹ := by
  have hfix : ∀ g : V ≃ₗ[ZMod 2] V, g ∈ fixGroup (⊥ : Submodule (ZMod 2) V) := fun g => by
    rw [fixGroup_bot]
    exact Subgroup.mem_top g
  have hperp : ∀ x : V, x ∈ spPerp f (⊥ : Submodule (ZMod 2) V) := fun x => by
    rw [spPerp_bot]
    exact Submodule.mem_top
  obtain ⟨p₁, -, hpp₁⟩ := sp_exists_partner hf hnd (bot_inf_eq _) (hperp p) hp0
  have hα : SpAutOn (⊥ : Submodule (ZMod 2) V) (α : SpG f → SpG f) :=
    { mem := fun g _ => hfix _
      map_mul := fun g h _ _ => map_mul α g h
      inj := fun g h _ _ e => α.injective e
      surj := fun h _ => ⟨α.symm h, hfix _, α.apply_symm_apply h⟩ }
  have hαp : SpMapsRad (⊥ : Submodule (ZMod 2) V) (α : SpG f → SpG f) p p := by
    intro g _
    rw [spRadFix_bot]
    exact hαL g
  obtain ⟨x, -, hx⟩ := sp_timmesfeld_2_6_2_rel hf hnd m (bot_inf_eq _) hm
    (by rw [spPerp_bot, finrank_top]; exact hdim) (hperp p) (hperp p₁) hpp₁ hα hαp
  exact ⟨x, fun g => hx g (hfix _)⟩

end S2

end CFSG.LargeExtraspecial
