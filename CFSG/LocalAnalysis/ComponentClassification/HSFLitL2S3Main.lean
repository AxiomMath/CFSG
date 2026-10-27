module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2S3Inv
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitL2Skeleton

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

@[expose] def FritzL2Lemma36Final : Prop :=
  HaradaInput → ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ∀ (t : X) (L : Subgroup X) (A : L2Data t L), Nat.card A.K = 2 →
      (∀ g : A.T, (g : X) ^ 2 = 1 → A.ψ g ∈ D16) →
      (∃ k, ∃ hk : k ∈ A.T, A.ψ ⟨k, hk⟩ = k8) →
      (∃ d, ∃ hd : d ∈ A.T, d ^ 2 = 1 ∧ A.ψ ⟨d, hd⟩ = d8) → SectRank4 X

@[expose] def FritzL2Lemma378 : Prop :=
  HaradaInput → ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    ∀ (t : X) (L : Subgroup X) (A : L2Data t L) (k : X) (hk : k ∈ A.T), k ^ 2 = 1 →
      A.ψ ⟨k, hk⟩ = k8 → Nat.card A.K ≠ 2 → SectRank4 X

theorem inv_D16_mul_R8_eq_d8 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, (u = 1 ∨ u = -1) →
    dbit8 b = 1 → aff8 u b * aff8 u b = 1 → ∃ c : ZMod 8, aff8 u b * aff8 1 (2 * c) = d8 := by
  decide

theorem odd_mul_R8_eq_d8 : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, dbit8 b = 1 →
    (∃ u' : (ZMod 8)ˣ, ∃ c : ZMod 8, (u' = 1 ∨ u' = -1) ∧ aff8 u b * aff8 u' (2 * c) = d8) ∨
      ∃ u' : (ZMod 8)ˣ, ∃ c : ZMod 8, (u' = 1 ∨ u' = -1) ∧
        aff8 u b * k8 * aff8 u' (2 * c) = d8 := by
  decide

theorem even_mem_R8_or : ∀ u : (ZMod 8)ˣ, ∀ b : ZMod 8, dbit8 b = 0 →
    (∃ u' : (ZMod 8)ˣ, ∃ c : ZMod 8, (u' = 1 ∨ u' = -1) ∧ aff8 u b = aff8 u' (2 * c)) ∨
      ∃ u' : (ZMod 8)ˣ, ∃ c : ZMod 8, (u' = 1 ∨ u' = -1) ∧ aff8 u b = aff8 u' (2 * c) * k8 := by
  decide

theorem aff8_mem_R8K {u : (ZMod 8)ˣ} {b : ZMod 8} (hb : dbit8 b = 0) : aff8 u b ∈ R8K := by
  rcases even_mem_R8_or u b hb with ⟨u', c, hu', h⟩ | ⟨u', c, hu', h⟩
  · rw [h]
    exact mem_sup_left ⟨u', c, hu', rfl⟩
  · rw [h]
    exact mul_mem (mem_sup_left ⟨u', c, hu', rfl⟩) (mem_sup_right (mem_zpowers k8))

namespace L2Data

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} (A : L2Data t L)

theorem sq_eq_one_of_mul_mem_R {g r : X} (hg : g ∈ A.T) (hg2 : g ^ 2 = 1) (hr : r ∈ A.R)
    (h : A.ψ ⟨g * r, mul_mem hg hr.1⟩ * A.ψ ⟨g * r, mul_mem hg hr.1⟩ = 1) : (g * r) ^ 2 = 1 := by
  have hgr : g * r * g⁻¹ ∈ A.R :=
    mem_inf.mpr ⟨mul_mem (mul_mem hg (mem_inf.mp hr).1) (inv_mem hg),
      (mem_normalizer_iff.mp (A.config.le_normalizer (A.T_le_centralizer hg)) r).mp
        (mem_inf.mp hr).2⟩
  have heq : (g * r) ^ 2 = g * r * g⁻¹ * r := by
    calc (g * r) ^ 2 = g * r * g⁻¹ * g ^ 2 * r := by rw [pow_two, pow_two]; group
      _ = g * r * g⁻¹ * r := by rw [hg2, mul_one]
  have hm : (g * r) ^ 2 ∈ A.R := heq ▸ mul_mem hgr hr
  refine A.eq_of_ψ_eq hm (one_mem _) ?_
  have e : (⟨(g * r) ^ 2, hm.1⟩ : A.T) = ⟨(g * r) ^ 2, pow_mem (mul_mem hg hr.1) 2⟩ := rfl
  rw [e, A.ψ_sq (mul_mem hg hr.1), h]
  exact (map_one A.ψ).symm

theorem exists_inv_k8_of_field {k : X} (hk : k ∈ A.T) (hk2 : k ^ 2 = 1) {u : (ZMod 8)ˣ}
    {b : ZMod 8} (hub : aff8 u b = A.ψ ⟨k, hk⟩) (hd : dbit8 b = 0) (hf : fbit8 u = 1) :
    ∃ k', ∃ hk' : k' ∈ A.T, k' ^ 2 = 1 ∧ A.ψ ⟨k', hk'⟩ = k8 := by
  obtain ⟨u', c, hu', hc⟩ := field_mul_R8_eq_k8 u b hd hf
  obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq (σ := aff8 u' (2 * c)) ⟨u', c, hu', rfl⟩
  have hψ : A.ψ ⟨k * r, mul_mem hk hr.1⟩ = k8 := by rw [A.ψ_mul hk hr.1, hψr, ← hc, hub]
  exact ⟨k * r, mul_mem hk hr.1, A.sq_eq_one_of_mul_mem_R hk hk2 hr (by rw [hψ]; decide), hψ⟩

theorem exists_inv_d8 (hH : HaradaInput) (hnot : ¬ SectRank4 X)
    (hinv : ∀ g : A.T, (g : X) ^ 2 = 1 → A.ψ g ∈ D16) :
    ∃ d, ∃ hd : d ∈ A.T, d ^ 2 = 1 ∧ A.ψ ⟨d, hd⟩ = d8 := by
  obtain ⟨d, hd, hd2, hdR⟩ := A.exists_inv_not_mem_R8 hH hnot
  obtain ⟨u, b, hu, hub⟩ := hinv ⟨d, hd⟩ hd2
  have hdb : dbit8 b = 1 := dbit8_eq_one_of_not_mem_R8 hu (by rw [hub]; exact hdR)
  have hψd2 : aff8 u b * aff8 u b = 1 := by
    rw [hub, ← A.ψ_sq hd]
    have : (⟨d ^ 2, pow_mem hd 2⟩ : A.T) = 1 := Subtype.ext hd2
    rw [this, map_one]
  obtain ⟨c, hc⟩ := inv_D16_mul_R8_eq_d8 u b hu hdb hψd2
  obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq (σ := aff8 1 (2 * c)) ⟨1, c, Or.inl rfl, rfl⟩
  have hψ : A.ψ ⟨d * r, mul_mem hd hr.1⟩ = d8 := by rw [A.ψ_mul hd hr.1, hψr, ← hc, hub]
  exact ⟨d * r, mul_mem hd hr.1, A.sq_eq_one_of_mul_mem_R hd hd2 hr (by rw [hψ]; decide), hψ⟩

theorem exists_inv_k8 (h36 : FritzL2Lemma36Final) (hH : HaradaInput) [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) (hnot : ¬ SectRank4 X) :
    ∃ k, ∃ hk : k ∈ A.T, k ^ 2 = 1 ∧ A.ψ ⟨k, hk⟩ = k8 := by
  by_cases hF : ∃ k, ∃ hk : k ∈ A.T, k ^ 2 = 1 ∧
      ∃ u b, aff8 u b = A.ψ ⟨k, hk⟩ ∧ dbit8 b = 0 ∧ fbit8 u = 1
  · obtain ⟨k, hk, hk2, u, b, hub, hd, hf⟩ := hF
    exact A.exists_inv_k8_of_field hk hk2 hub hd hf
  · exfalso
    have hinv : ∀ g : A.T, (g : X) ^ 2 = 1 → A.ψ g ∈ D16 := by
      intro g hg2
      obtain ⟨u, b, hub⟩ := A.exists_aff8 g
      refine ⟨u, b, ?_, hub⟩
      rw [← fbit8_eq_zero_iff]
      rcases zmod2_cases (fbit8 u) with h | h
      · exact h
      · exfalso
        rcases zmod2_cases (dbit8 b) with h' | h'
        · exact hF ⟨g, g.2, hg2, u, b, hub, h', h⟩
        · refine not_inv_FD u b h h' ?_
          rw [hub, ← map_mul]
          have : g * g = 1 := Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, hg2]; rfl)
          rw [this, map_one]
    have hK := A.card_K_of_inv_D16 hH hnot hinv
    exact hnot (h36 hH X hnonab t L A hK hinv (A.exists_k8 hH hnot)
      (A.exists_inv_d8 hH hnot hinv))

omit [Finite X] in
theorem exists_d8 {k : X} (hk : k ∈ A.T) (hψk : A.ψ ⟨k, hk⟩ = k8) (g : A.T) {u : (ZMod 8)ˣ}
    {b : ZMod 8} (hub : aff8 u b = A.ψ g) (hb : dbit8 b = 1) :
    ∃ d, ∃ hd : d ∈ A.T, A.ψ ⟨d, hd⟩ = d8 := by
  rcases odd_mul_R8_eq_d8 u b hb with ⟨u', c, hu', hc⟩ | ⟨u', c, hu', hc⟩
  · obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq (σ := aff8 u' (2 * c)) ⟨u', c, hu', rfl⟩
    exact ⟨g * r, mul_mem g.2 hr.1, by rw [A.ψ_mul g.2 hr.1, hψr, ← hc, hub]⟩
  · obtain ⟨r, hr, hψr⟩ := A.exists_mem_R_ψ_eq (σ := aff8 u' (2 * c)) ⟨u', c, hu', rfl⟩
    exact ⟨g * k * r, mul_mem (mul_mem g.2 hk) hr.1, by
      rw [A.ψ_mul (mul_mem g.2 hk) hr.1, A.ψ_mul g.2 hk, hψk, hψr, ← hc, hub]⟩

end L2Data

theorem fritzL2Section3_of_parts (h36 : FritzL2Lemma36Final) (h378 : FritzL2Lemma378) :
    FritzL2Section3 := by
  intro hH X _ _ _ hnonab hnot t L A
  obtain ⟨k, hk, hk2, hψk⟩ := A.exists_inv_k8 h36 hH hnonab hnot
  have hK : Nat.card A.K = 2 := by
    by_contra hK
    exact hnot (h378 hH X hnonab t L A k hk hk2 hψk hK)
  by_cases hR : ∀ (g : A.T) u b, aff8 u b = A.ψ g → dbit8 b = 0
  · refine Or.inl ⟨⟨k, hk, hk2, hψk, hK, fun g => ?_⟩⟩
    obtain ⟨u, b, hub⟩ := A.exists_aff8 g
    rw [← hub]
    exact aff8_mem_R8K (hR g u b hub)
  · push Not at hR
    obtain ⟨g, u, b, hub, hb⟩ := hR
    have hb1 : dbit8 b = 1 := (zmod2_cases (dbit8 b)).resolve_left hb
    obtain ⟨d, hd, hψd⟩ := A.exists_d8 hk hψk g hub hb1
    exact Or.inr ⟨⟨k, hk, hk2, hψk, d, hd, hψd, hK⟩⟩

end CFSG.ComponentClassification.HSFLit
