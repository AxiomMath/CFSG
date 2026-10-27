module

public import CFSG.LargeExtraspecial.S4EightF5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler)

section Abstract

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  {q : QuadraticForm (ZMod 2) U}

omit [FiniteDimensional (ZMod 2) U] in
theorem map_conj_pointRadical {x : U ≃ₗ[ZMod 2] U}
    (hx : x ∈ TauCeti.QuadraticMap.orthogonalGroup q) (p : U) :
    (pointRadical q p).map (MulAut.conj x).toMonoidHom = pointRadical q (x p) := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    exact conj_mem_pointRadical hx hw
  · intro w hw
    refine ⟨x⁻¹ * w * x⁻¹⁻¹, ?_, by simp [mul_assoc]⟩
    have := conj_mem_pointRadical (inv_mem hx) hw
    rwa [show x⁻¹ (x p) = p from x.symm_apply_apply p] at this

theorem exists_isPGroup_gt_pointRadical (hq : q.polarBilin.Nondegenerate)
    (h6 : 6 ≤ finrank (ZMod 2) U) {a : U} (ha0 : a ≠ 0) (ha : q a = 0) :
    ∃ P : Subgroup (U ≃ₗ[ZMod 2] U), IsPGroup 2 P ∧ pointRadical q a < P ∧
      P ≤ omegaGroup q hq := by
  have : Finite U := Module.finite_of_finite (ZMod 2)
  have : Finite (U ≃ₗ[ZMod 2] U) := finite_linearEquiv_of_finite
  have hbot : (⊥ : Submodule (ZMod 2) U) ⊓ S2.perp q ⊥ = ⊥ := bot_inf_eq _
  have hmem : ∀ v : U, v ∈ S2.perp q ⊥ := fun v => by rw [S2.perp_bot]; trivial
  obtain ⟨a', -, -, haa'⟩ := S2.exists_hyperbolic_partner hq hbot (hmem a) ha0 ha
  have hP₁inf := S2.sup_span_pair_inf_perp_eq_bot hbot (hmem a) (hmem a') haa'
  have hP₁dim := S2.finrank_perp_sup_span_pair hq hbot (hmem a) (hmem a') haa'
  rw [S2.perp_bot, finrank_top] at hP₁dim
  obtain ⟨d, hdP, hd0, hd⟩ := S2.exists_singular_mem_perp (q := q)
    (F := ⊥ ⊔ Submodule.span (ZMod 2) {a, a'}) (by omega)
  obtain ⟨d', hd'P, -, hdd'⟩ := S2.exists_hyperbolic_partner hq hP₁inf hdP hd0 hd
  have hP₂dim := S2.finrank_perp_sup_span_pair hq hP₁inf hdP hd'P hdd'
  obtain ⟨-, hda, hda'⟩ := S2.mem_perp_sup_span_pair.mp hdP
  obtain ⟨-, hd'a, hd'a'⟩ := S2.mem_perp_sup_span_pair.mp hd'P
  have hne : S2.perp q ((⊥ ⊔ Submodule.span (ZMod 2) {a, a'}) ⊔
      Submodule.span (ZMod 2) {d, d'}) ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hP₂dim
    omega
  obtain ⟨u, huP, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨huP₁, hud, hud'⟩ := S2.mem_perp_sup_span_pair.mp huP
  obtain ⟨-, hua, hua'⟩ := S2.mem_perp_sup_span_pair.mp huP₁
  set E := eichler q d u with hEdef
  have hEO : E ∈ TauCeti.QuadraticMap.orthogonalGroup q :=
    CFSG.ClassicalGroups.Orthogonal.eichler_mem_orthogonalGroup q d u
  have hEa : E a = a := by
    rw [hEdef, eichler_apply_zmod2 hd hud, hda, hua]
    simp
  have hEsq : E * E = 1 := eichler_mul_self hud
  have hEnorm : E ∈ normalizer (pointRadical q a : Set (U ≃ₗ[ZMod 2] U)) :=
    CFSG.LargeExtraspecial.S4.mem_normalizer_of_conj_le fun w hw => by
      have := conj_mem_pointRadical hEO hw
      rwa [hEa] at this
  have hEnot : E ∉ pointRadical q a := by
    intro hE
    have h1 := hE.2.2.1 d' hd'a
    have hcalc : E d' - d' = u + q u • d := by
      rw [hEdef, eichler_apply_zmod2 hd hud]
      have e1 : polar q d' d = 1 := by rw [polar_comm]; exact hdd'
      simp only [e1, hud', one_smul, mul_one, zero_add]
      abel
    rw [hcalc] at h1
    rcases mem_span_singleton_iff.mp h1 with h0 | h1'
    ·
      have : polar q d' (u + q u • d) = 0 := by rw [h0, polar_zero_right]
      rw [polar_add_right, polar_smul_right, hud', polar_comm q d' d, hdd',
        smul_eq_mul, mul_one, zero_add] at this
      rw [this, zero_smul, add_zero] at h0
      exact hu0 h0
    · have : polar q a' (u + q u • d) = 1 := by rw [h1', polar_comm, haa']
      rw [polar_add_right, polar_smul_right, hua', hda', smul_zero, add_zero] at this
      exact zero_ne_one this
  have hE2 : IsPGroup 2 (zpowers E) := by
    have hdvd : orderOf E ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hEsq])
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  have hN2 : IsPGroup 2 (pointRadical q a) := by
    have := isElementaryAbelian_pointRadical hq ha0 ha
    exact CFSG.IsElementaryAbelian.isPGroup 2 _
  refine ⟨pointRadical q a ⊔ zpowers E, ?_, ?_, ?_⟩
  · rw [sup_comm]
    exact IsPGroup.to_sup_of_normal_right' hE2 hN2 (zpowers_le.mpr hEnorm)
  · exact lt_of_le_of_ne le_sup_left fun h => hEnot (h ▸ mem_sup_right (mem_zpowers E))
  · exact sup_le (pointRadical_le_omegaGroup hq ha0 ha)
      (zpowers_le.mpr (S2.eichler_mem_omegaGroup hq d u))

end Abstract

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {g : G}

variable (H : Hyp4 S g) (C : Cons311 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
  (hVQ : ¬ V S g t ≤ S.Qa g) {F : Subgroup S.O} (hFodd : Odd (Nat.card F))
  (hFR : F ≤ Rbar S g t) (hLF : S.Lbar g ≤ normalizer (F : Set S.O))
include H C ht ht1 hVQ hFodd hFR hLF

theorem false_of_omegaCase_of_beta_ne_zero (hΩ : OmegaCase H C ht ht1 hVQ)
    (h6 : 6 ≤ finrank (ZMod 2) (Vt S g t)) {f₁ f₂ : S.O} (hf₁ : f₁ ∈ F) (hf₂ : f₂ ∈ F)
    (hβne : beta H C ht ht1 hVQ (orbV H.conj_mem ht (hFR hf₁))
      (orbV H.conj_mem ht (hFR hf₂)) ≠ 0) : False := by
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  obtain ⟨Q, hQ, hQβ, hX, hE, hsing⟩ := hΩ.exists_form
  set Fh := FhatV S H.conj_mem t F with hFh
  have hFh2 := odd_card_FhatV H.conj_mem hFodd hFR
  have hEN := LmodN_le_normalizer_FhatV H.conj_mem ht (F := F) hLF
  have hpol : ∀ x y, polar Q x y = beta H C ht ht1 hVQ x y := fun x y => by
    rw [← polarBilin_apply_apply, hQβ]
  have hsingf : ∀ {f : S.O} (hf : f ∈ F), Q (orbV H.conj_mem ht (hFR hf)) = 0 := by
    intro f hf
    have h0 : orbV H.conj_mem ht (hFR hf) ≠ 0 := fun h0 => by
      have := congrArg Subtype.val h0
      rw [coe_orbV, ZeroMemClass.coe_zero] at this
      have h3 := congrArg ((f⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) this
      rw [inv_apply_apply_O, map_zero] at h3
      exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne h3
    exact (hsing _ h0).mpr ⟨_, ⟨f, hFR hf, fun v => coe_resV_apply H.conj_mem _ v⟩, rfl⟩
  have hN : ∀ {f : S.O} (hf : f ∈ F), pointRadical Q (orbV H.conj_mem ht (hFR hf)) ≤
      Fh ⊔ LmodN S g t := by
    intro f hf
    have hxX : resV H.conj_mem t ⟨f, hFR hf⟩ ∈ RmodN S g t :=
      ⟨f, hFR hf, fun v => coe_resV_apply H.conj_mem _ v⟩
    have hxO : resV H.conj_mem t ⟨f, hFR hf⟩ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      (omegaGroup_le Q hQ) (hX ▸ hxX)
    rw [orbV, ← map_conj_pointRadical hxO, ← hE]
    rintro _ ⟨w, hw, rfl⟩
    have hx := resV_mem_FhatV H.conj_mem hf (hFR hf)
    exact mul_mem (mul_mem (mem_sup_left hx) (mem_sup_right hw)) (inv_mem (mem_sup_left hx))
  obtain ⟨k, hk⟩ := even_finrank_Vt H C ht ht1 hVQ
  have hβ1 : polar Q (orbV H.conj_mem ht (hFR hf₁)) (orbV H.conj_mem ht (hFR hf₂)) = 1 := by
    rw [hpol]
    exact zmod2_eq_one_of_ne_zero hβne
  have hb0 : orbV H.conj_mem ht (hFR hf₁) ≠ 0 := fun h0 => by
    rw [h0, polar_zero_left] at hβ1
    exact zero_ne_one hβ1
  have hgen := S2.omegaFix_eq_closure_radFix hQ (F := ⊥) (bot_inf_eq _) (m := k) (by omega)
    (by rw [S2.perp_bot, finrank_top, hk]; ring) (by rw [S2.perp_bot]; trivial)
    (by rw [S2.perp_bot]; trivial) hb0 (hsingf hf₁) (hsingf hf₂) hβ1
  rw [S2.omegaFix_bot, S2.radFix_bot, S2.radFix_bot] at hgen
  have hΩFE : omegaGroup Q hQ ≤ Fh ⊔ LmodN S g t := by
    rw [hgen, closure_le]
    rintro w (hw | hw)
    · exact hN hf₁ hw
    · exact hN hf₂ hw
  have haQ : Q (aV ht) = 0 := (hsing _ (aV_ne_zero H ht)).mpr ⟨1, one_mem _, rfl⟩
  obtain ⟨P, hP2, hPlt, hPΩ⟩ := exists_isPGroup_gt_pointRadical hQ h6 (aV_ne_zero H ht) haQ
  have hc1 := Subgroup.card_lt_of_lt hPlt
  have hc2 := card_le_of_isPGroup_le_sup hFh2 hEN hP2 (hPΩ.trans hΩFE)
  rw [hE] at hc2
  omega

end CFSG.LargeExtraspecial.S4
