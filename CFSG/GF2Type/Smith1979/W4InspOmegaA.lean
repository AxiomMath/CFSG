module

public import CFSG.LargeExtraspecial.S2OrthB1
public import CFSG.LargeExtraspecial.S2Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4Insp

open Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S2
  CFSG.LargeExtraspecial.OrthoF2 CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul eichler_conj eichler_add_smul_self
  eichler_apply_self eichler_apply_of_polar_eq_zero eichler_zero_right reflect reflect_conj
  reflect_inv reflect_mul_self reflect_mem_orthogonalGroup reflect_eq_reflection
  reflect_apply_of_map_eq_one reflect_apply_of_polar_eq_zero)

namespace OmegaA

section Basic

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem mem_perp_bot (v : V) : v ∈ perp q (⊥ : Submodule (ZMod 2) V) := by
  rw [perp_bot]
  exact Submodule.mem_top

theorem mem_sup_span_pair_left (F : Submodule (ZMod 2) V) (p p₁ : V) :
    p ∈ F ⊔ Submodule.span (ZMod 2) {p, p₁} :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem exists_eichler_eq_of_mem_perp {F : Submodule (ZMod 2) V} {p p₁ : V} (hp : q p = 0)
    (hpF : p ∈ perp q F) (hp₁F : p₁ ∈ perp q F) (hpp₁ : polar q p p₁ = 1) {u : V}
    (huF : u ∈ perp q F) (hpu : polar q p u = 0) :
    ∃ u' ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}), eichler q p u = eichler q p u' := by
  have h := sub_mem_perp_sup_span_pair hpF hp₁F hpp₁ huF
  have hup : polar q u p = 0 := by rw [polar_comm]; exact hpu
  rw [hup, zero_smul, sub_zero] at h
  refine ⟨_, h, ?_⟩
  conv_lhs => rw [← sub_add_cancel u (polar q u p₁ • p)]
  exact eichler_add_smul_self hp _ _

theorem odd_orderOf_of_pow_three {G : Type*} [Group G] {y : G} (h : y ^ 3 = 1) :
    Odd (orderOf y) := by
  have h1 : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one h
  rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h <;> rw [h] <;> decide

theorem pow_three_eq_one_of_braid {G : Type*} [Group G] {a b : G} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a * b * a = b * a * b) : (a * b) ^ 3 = 1 := by
  calc (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = (b * a * b) * (b * a * b) := by rw [hab]
    _ = b * a * (b * b) * a * b := by simp only [mul_assoc]
    _ = 1 := by rw [hb, mul_one, mul_assoc b a a, ha, mul_one, hb]

theorem reflect_mul_reflect_pow_three {c c' : V} (hc : q c = 1) (hc' : q c' = 1)
    (hcc' : polar q c c' = 1) : (reflect q c * reflect q c') ^ 3 = 1 := by
  have hc'c : polar q c' c = 1 := by rw [polar_comm]; exact hcc'
  refine pow_three_eq_one_of_braid (reflect_mul_self q c) (reflect_mul_self q c') ?_
  have h1 := reflect_conj (reflect_mem_orthogonalGroup q c) c'
  have h2 := reflect_conj (reflect_mem_orthogonalGroup q c') c
  rw [reflect_inv, reflect_apply_of_map_eq_one hc, hc'c, one_smul] at h1
  rw [reflect_inv, reflect_apply_of_map_eq_one hc', hcc', one_smul, add_comm] at h2
  rw [h1, h2]

end Basic

section General

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem exists_mem_perp_polar_eq_one_map_eq (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F))
    {w : V} (hwF : w ∈ perp q F) (hw0 : w ≠ 0) (ε : ZMod 2) :
    ∃ z ∈ perp q F, polar q w z = 1 ∧ q z = ε := by
  obtain ⟨z₀, hz₀F, hz₀w⟩ := exists_mem_perp_polar_eq_one hq hF hwF hw0
  have hwz₀ : polar q w z₀ = 1 := by rw [polar_comm]; exact hz₀w
  by_cases hε : q z₀ = ε
  · exact ⟨z₀, hz₀F, hwz₀, hε⟩
  · have hK := sup_span_pair_inf_perp_eq_bot hF hwF hz₀F hwz₀
    have hdim := finrank_perp_sup_span_pair hq hF hwF hz₀F hwz₀
    have hne : perp q (F ⊔ Submodule.span (ZMod 2) {w, z₀}) ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hdim
      omega
    obtain ⟨v, hvK, hv⟩ := exists_mem_perp_map_eq_one hq hK hne
    obtain ⟨hvF, hwv, hz₀v⟩ := mem_perp_sup_span_pair.mp hvK
    refine ⟨z₀ + v, Submodule.add_mem _ hz₀F hvF, ?_, ?_⟩
    · rw [polar_add_right, hwz₀, hwv, add_zero]
    · rw [map_add_eq, hv, hz₀v, add_zero]
      exact (by decide : ∀ a b : ZMod 2, a ≠ b → a + 1 = b) _ _ hε

theorem exists_hyperbolic_pair_finrank_perp (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) {x : V} (hx0 : x ≠ 0) (hxq : q x = 0) :
    ∃ p₁ : V, q p₁ = 0 ∧ polar q x p₁ = 1 ∧
      finrank (ZMod 2) (perp q (⊥ ⊔ Submodule.span (ZMod 2) {x, p₁})) = 6 := by
  obtain ⟨p₁, -, hp₁, hxp₁⟩ :=
    exists_hyperbolic_partner hq (bot_inf_eq _) (mem_perp_bot x) hx0 hxq
  have h := finrank_perp_sup_span_pair hq (bot_inf_eq _) (mem_perp_bot x) (mem_perp_bot p₁) hxp₁
  rw [perp_bot, finrank_top, hV] at h
  exact ⟨p₁, hp₁, hxp₁, by omega⟩

theorem eichler_mem_of_singular (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) {p p₁ : V} (hp : q p = 0) (hpF : p ∈ perp q F)
    (hp₁F : p₁ ∈ perp q F) (hpp₁ : polar q p p₁ = 1)
    (h3 : 3 ≤ finrank (ZMod 2) (perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁})))
    (H : Subgroup (V ≃ₗ[ZMod 2] V))
    (hH : ∀ s ∈ perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}), q s = 0 → eichler q p s ∈ H)
    {u : V} (huF : u ∈ perp q F) (hpu : polar q p u = 0) : eichler q p u ∈ H := by
  obtain ⟨u', hu'K, hu⟩ := exists_eichler_eq_of_mem_perp hp hpF hp₁F hpp₁ huF hpu
  rw [hu]
  have hK : (F ⊔ Submodule.span (ZMod 2) {p, p₁}) ⊓
      perp q (F ⊔ Submodule.span (ZMod 2) {p, p₁}) = ⊥ :=
    sup_span_pair_inf_perp_eq_bot hF hpF hp₁F hpp₁
  rcases zmod2_eq_zero_or_eq_one (q u') with h0 | h1
  · exact hH u' hu'K h0
  · have hu'0 : u' ≠ 0 := by
      rintro rfl
      rw [map_zero] at h1
      exact zero_ne_one h1
    obtain ⟨s, hsK, hu's, hs⟩ := exists_mem_perp_polar_eq_one_map_eq hq hK h3 hu'K hu'0 0
    have hps : polar q p s = 0 := (mem_perp_sup_span_pair.mp hsK).2.1
    have hpu' : polar q p u' = 0 := (mem_perp_sup_span_pair.mp hu'K).2.1
    have hpus : polar q p (u' + s) = 0 := by rw [polar_add_right, hpu', hps, add_zero]
    have hq' : q (u' + s) = 0 := by
      rw [map_add_eq, h1, hs, hu's]
      decide
    have e : eichler q p u' = eichler q p s * eichler q p (u' + s) := by
      rw [eichler_mul hps hpus, ← add_assoc, add_comm s u', add_assoc, vec_add_self, add_zero]
    rw [e]
    exact mul_mem (hH s hsK hs) (hH _ (Submodule.add_mem _ hu'K hsK) hq')

theorem eichler_eq_one_or_isTypeA (hq : q.polarBilin.Nondegenerate) {p s : V} (hp0 : p ≠ 0)
    (hp : q p = 0) (hs : q s = 0) (hps : polar q p s = 0) :
    eichler q p s = 1 ∨ IsTypeA q (eichler q p s) 2 := by
  by_cases hs0 : s = 0
  · left
    rw [hs0]
    exact eichler_zero_right q p
  by_cases hsp : p = s
  · left
    rw [← hsp]
    exact eichler_self hp
  · right
    exact (eichler_isTypeA hq hp hps (OrthoF2.linearIndependent_pair_iff.mpr ⟨hp0, hs0, hsp⟩)
      hs).1

theorem eichler_mem_closure_isTypeA (hq : q.polarBilin.Nondegenerate) {x p s : V} (hp0 : p ≠ 0)
    (hp : q p = 0) (hs : q s = 0) (hps : polar q p s = 0) (hxp : polar q x p = 0)
    (hxs : polar q x s = 0) :
    eichler q p s ∈ Subgroup.closure
      {τ : V ≃ₗ[ZMod 2] V | τ ∈ omegaGroup q hq ∧ τ x = x ∧ IsTypeA q τ 2} := by
  rcases eichler_eq_one_or_isTypeA hq hp0 hp hs hps with h | h
  · rw [h]
    exact one_mem _
  · exact Subgroup.subset_closure ⟨eichler_mem_omegaGroup hq p s,
      eichler_apply_of_polar_eq_zero hxp hxs, h⟩

theorem reflect_mul_reflect_mem_omegaGroup (hq : q.polarBilin.Nondegenerate) {a b : V}
    (ha : q a = 1) (hb : q b = 1) : reflect q a * reflect q b ∈ omegaGroup q hq := by
  have hfr : ∀ v, q v = 1 → finrank (ZMod 2) (commSpace (reflect q v)) = 1 := fun v hv => by
    haveI : Invertible (q v) := invertibleOfNonzero (by rw [hv]; exact one_ne_zero)
    rw [reflect_eq_reflection]
    exact finrank_commSpace_reflection hq v
  have ha' := reflect_mem_orthogonalGroup q a
  have hb' := reflect_mem_orthogonalGroup q b
  refine mem_omegaGroup.mpr ⟨mul_mem ha' hb', ?_⟩
  rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hq ha' hb', hfr a ha,
    hfr b hb]
  decide

theorem eichler_mem_closure_odd_of_map_eq_one (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F))
    {x : V} (hxF : x ∈ F) {w : V} (hwF : w ∈ perp q F) (hw : q w = 1) :
    eichler q x w ∈ Subgroup.closure
      {y : V ≃ₗ[ZMod 2] V | y ∈ omegaGroup q hq ∧ y x = x ∧ Odd (orderOf y)} := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [map_zero] at hw
    exact zero_ne_one hw
  obtain ⟨z, hzF, hwz, hz⟩ := exists_mem_perp_polar_eq_one_map_eq hq hF h3 hwF hw0 1
  have hxw : polar q x w = 0 := mem_perp.mp hwF x hxF
  have hxz : polar q x z = 0 := mem_perp.mp hzF x hxF
  have hwx : polar q w x = 0 := by rw [polar_comm]; exact hxw
  have hzx : polar q z x = 0 := by rw [polar_comm]; exact hxz
  have hzw : polar q z w = 1 := by rw [polar_comm]; exact hwz
  set ρ := reflect q w * reflect q z with hρ
  have hρΩ : ρ ∈ omegaGroup q hq := reflect_mul_reflect_mem_omegaGroup hq hw hz
  have hρO := omegaGroup_le q hq hρΩ
  have hρx : ρ x = x := by
    rw [hρ, LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero hzx,
      reflect_apply_of_polar_eq_zero hwx]
  have hρ3 : ρ ^ 3 = 1 := reflect_mul_reflect_pow_three hw hz hwz
  have hρz : ρ z = z + w := by
    rw [hρ, LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero (polar_self_eq_zero q z),
      reflect_apply_of_map_eq_one hw, hzw, one_smul]
  set E := eichler q x z with hE
  have hEΩ : E ∈ omegaGroup q hq := eichler_mem_omegaGroup hq x z
  have hEx : E x = x := eichler_apply_self x z
  have hEinv : E⁻¹ = E := inv_eq_of_mul_eq_one_right (eichler_mul_self hxz)
  have hEinvx : E⁻¹ x = x := by rw [hEinv]; exact hEx
  have hconj : ρ * E * ρ⁻¹ = eichler q x (z + w) := by rw [hE, eichler_conj hρO, hρx, hρz]
  have hxzw : polar q x (z + w) = 0 := by rw [polar_add_right, hxz, hxw, add_zero]
  have hdecomp : eichler q x w = (E * ρ * E⁻¹) * ρ⁻¹ := by
    calc eichler q x w = E * eichler q x (z + w) := by
          rw [hE, eichler_mul hxz hxzw, ← add_assoc, vec_add_self, zero_add]
      _ = E * (ρ * E * ρ⁻¹) := by rw [hconj]
      _ = (E * ρ * E⁻¹) * ρ⁻¹ := by rw [hEinv]; group
  have hmem : ∀ g : V ≃ₗ[ZMod 2] V, g ∈ omegaGroup q hq → g x = x → g ^ 3 = 1 →
      g ∈ Subgroup.closure
        {y : V ≃ₗ[ZMod 2] V | y ∈ omegaGroup q hq ∧ y x = x ∧ Odd (orderOf y)} :=
    fun g hg hgx hg3 => Subgroup.subset_closure ⟨hg, hgx, odd_orderOf_of_pow_three hg3⟩
  rw [hdecomp]
  refine mul_mem (hmem _ (mul_mem (mul_mem hEΩ hρΩ) (inv_mem hEΩ)) ?_ ?_)
    (hmem _ (inv_mem hρΩ) ?_ ?_)
  · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hEinvx, hρx, hEx]
  · rw [conj_pow, hρ3, mul_one, mul_inv_cancel]
  · conv_lhs => rw [← hρx]
    exact CFSG.ClassicalGroups.Orthogonal.LinearEquiv.inv_apply_apply' ρ x
  · rw [inv_pow, hρ3, inv_one]

theorem eichler_mem_closure_odd_of_map_eq_zero (hq : q.polarBilin.Nondegenerate)
    {F : Submodule (ZMod 2) V} (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F))
    {x : V} (hxF : x ∈ F) {w : V} (hwF : w ∈ perp q F) (hw : q w = 0) :
    eichler q x w ∈ Subgroup.closure
      {y : V ≃ₗ[ZMod 2] V | y ∈ omegaGroup q hq ∧ y x = x ∧ Odd (orderOf y)} := by
  have h1 := finrank_perp_sup_span_singleton_add_one hq F w
  obtain ⟨w₁, hw₁T, hw₁⟩ := exists_mem_map_eq_one_of_lt hq hF
    (T := perp q (F ⊔ (ZMod 2) ∙ w)) (fun v hv => (mem_perp_sup.mp hv).1) (by omega)
  obtain ⟨hw₁F, hw₁w⟩ := mem_perp_sup.mp hw₁T
  have hww₁ : polar q w w₁ = 0 := mem_perp.mp hw₁w w (Submodule.mem_span_singleton_self w)
  have hq₂ : q (w + w₁) = 1 := by
    rw [map_add_eq, hw, hw₁, hww₁]
    decide
  have hxw₁ : polar q x w₁ = 0 := mem_perp.mp hw₁F x hxF
  have hxw : polar q x w = 0 := mem_perp.mp hwF x hxF
  have hxww₁ : polar q x (w + w₁) = 0 := by rw [polar_add_right, hxw, hxw₁, add_zero]
  have e : eichler q x w = eichler q x w₁ * eichler q x (w + w₁) := by
    rw [eichler_mul hxw₁ hxww₁, add_comm w w₁, ← add_assoc, vec_add_self, zero_add]
  rw [e]
  exact mul_mem (eichler_mem_closure_odd_of_map_eq_one hq hF h3 hxF hw₁F hw₁)
    (eichler_mem_closure_odd_of_map_eq_one hq hF h3 hxF (Submodule.add_mem _ hwF hw₁F) hq₂)

theorem eichler_mem_closure_odd (hq : q.polarBilin.Nondegenerate) {F : Submodule (ZMod 2) V}
    (hF : F ⊓ perp q F = ⊥) (h3 : 3 ≤ finrank (ZMod 2) (perp q F)) {x : V} (hxF : x ∈ F)
    {u : V} (huF : u ∈ perp q F) :
    eichler q x u ∈ Subgroup.closure
      {y : V ≃ₗ[ZMod 2] V | y ∈ omegaGroup q hq ∧ y x = x ∧ Odd (orderOf y)} := by
  rcases zmod2_eq_zero_or_eq_one (q u) with h | h
  · exact eichler_mem_closure_odd_of_map_eq_zero hq hF h3 hxF huF h
  · exact eichler_mem_closure_odd_of_map_eq_one hq hF h3 hxF huF h

end General

end OmegaA

section Main

open OmegaA

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem stab_le_closure_isTypeA (hq : q.polarBilin.Nondegenerate) (hV : finrank (ZMod 2) V = 8)
    {x : V} (hx0 : x ≠ 0) (hxq : q x = 0) :
    ∀ k ∈ omegaGroup q hq, k x = x →
      k ∈ Subgroup.closure
        {τ : V ≃ₗ[ZMod 2] V | τ ∈ omegaGroup q hq ∧ τ x = x ∧ IsTypeA q τ 2} := by
  intro k hk hkx
  obtain ⟨p₁, hp₁, hxp₁, hKdim⟩ := exists_hyperbolic_pair_finrank_perp hq hV hx0 hxq
  have hK := sup_span_pair_inf_perp_eq_bot (bot_inf_eq _) (mem_perp_bot x) (mem_perp_bot p₁) hxp₁
  have hxK := mem_sup_span_pair_left (⊥ : Submodule (ZMod 2) V) x p₁
  obtain ⟨t, ht, hty⟩ := exists_mem_radFix_inv_mul_mem hq (mem_perp_bot x) (mem_perp_bot p₁) hx0
    hxq hp₁ hxp₁ (by rw [omegaFix_bot]; exact hk) hkx
  obtain ⟨u, huF, hxu, rfl⟩ := (mem_radFix_iff hq hx0 hxq (mem_perp_bot x)).mp ht
  have htH : eichler q x u ∈ Subgroup.closure
      {τ : V ≃ₗ[ZMod 2] V | τ ∈ omegaGroup q hq ∧ τ x = x ∧ IsTypeA q τ 2} := by
    refine eichler_mem_of_singular hq (bot_inf_eq _) hxq (mem_perp_bot x) (mem_perp_bot p₁) hxp₁
      (by omega) _ ?_ huF hxu
    intro s hs hsq
    exact eichler_mem_closure_isTypeA hq hx0 hxq hsq (mem_perp_sup_span_pair.mp hs).2.1
      (polar_self_eq_zero q x) (mem_perp.mp hs x hxK)
  have hrad : radGen q (⊥ ⊔ Submodule.span (ZMod 2) {x, p₁}) ≤ Subgroup.closure
      {τ : V ≃ₗ[ZMod 2] V | τ ∈ omegaGroup q hq ∧ τ x = x ∧ IsTypeA q τ 2} := by
    rw [radGen, Subgroup.closure_le]
    rintro t' ⟨p, hpK, hp0, hpq, ht'⟩
    obtain ⟨u', hu'K, hpu', rfl⟩ := (mem_radFix_iff hq hp0 hpq hpK).mp ht'
    obtain ⟨p', hp'K, -, hpp'⟩ := exists_hyperbolic_partner hq hK hpK hp0 hpq
    have hdim' := finrank_perp_sup_span_pair hq hK hpK hp'K hpp'
    refine eichler_mem_of_singular hq hK hpq hpK hp'K hpp' (by omega) _ ?_ hu'K hpu'
    intro s hs hsq
    exact eichler_mem_closure_isTypeA hq hp0 hpq hsq (mem_perp_sup_span_pair.mp hs).2.1
      (mem_perp.mp hpK x hxK) (mem_perp.mp (perp_sup_span_pair_le hs) x hxK)
  have hyH := hrad (omegaFix_le_radGen hq 3 _ (by norm_num) hK (by omega) hty)
  have e : k = eichler q x u * ((eichler q x u)⁻¹ * k) := by group
  rw [e]
  exact mul_mem htH hyH

theorem pointRadical_le_closure_odd (hq : q.polarBilin.Nondegenerate)
    (hV : finrank (ZMod 2) V = 8) {x : V} (hx0 : x ≠ 0) (hxq : q x = 0) :
    pointRadical q x ≤ Subgroup.closure
      {y : V ≃ₗ[ZMod 2] V | y ∈ omegaGroup q hq ∧ y x = x ∧ Odd (orderOf y)} := by
  intro r hr
  obtain ⟨u, hxu, rfl⟩ := (mem_pointRadical_iff hq hx0 hxq).mp hr
  obtain ⟨p₁, -, hxp₁, hKdim⟩ := exists_hyperbolic_pair_finrank_perp hq hV hx0 hxq
  have hK := sup_span_pair_inf_perp_eq_bot (bot_inf_eq _) (mem_perp_bot x) (mem_perp_bot p₁) hxp₁
  obtain ⟨u', hu'K, hu⟩ := exists_eichler_eq_of_mem_perp hxq (mem_perp_bot x) (mem_perp_bot p₁)
    hxp₁ (mem_perp_bot u) hxu
  rw [hu]
  exact eichler_mem_closure_odd hq hK (by omega) (mem_sup_span_pair_left _ x p₁) hu'K

end Main

end CFSG.GF2Type.Smith1979.W4Insp
