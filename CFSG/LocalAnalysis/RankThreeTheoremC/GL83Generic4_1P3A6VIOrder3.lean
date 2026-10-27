module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3U3Lemma42
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem a6vi_inv_conj_zpow (r w : G) (i : ℤ) : r⁻¹ * w ^ i * r = (r⁻¹ * w * r) ^ i := by
  have h := conj_zpow (i := i) (a := r⁻¹) (b := w)
  rw [inv_inv] at h
  exact h.symm

theorem a6vi_normal_form_eq {x u v : G} (hT : (zpowers u ⊔ zpowers v) ⊓ zpowers x = ⊥)
    (h12 : zpowers u ⊓ zpowers v = ⊥) {a b c a' b' c' : ℤ}
    (h : x ^ a * u ^ b * v ^ c = x ^ a' * u ^ b' * v ^ c') :
    x ^ a = x ^ a' ∧ u ^ b = u ^ b' ∧ v ^ c = v ^ c' := by
  have hx : (x ^ a')⁻¹ * x ^ a = u ^ b' * v ^ c' * (u ^ b * v ^ c)⁻¹ := by
    calc (x ^ a')⁻¹ * x ^ a = (x ^ a')⁻¹ * (x ^ a * u ^ b * v ^ c) * (u ^ b * v ^ c)⁻¹ := by group
      _ = (x ^ a')⁻¹ * (x ^ a' * u ^ b' * v ^ c') * (u ^ b * v ^ c)⁻¹ := by rw [h]
      _ = u ^ b' * v ^ c' * (u ^ b * v ^ c)⁻¹ := by group
  have hx1 : (x ^ a')⁻¹ * x ^ a = 1 := by
    have hmem : (x ^ a')⁻¹ * x ^ a ∈ (zpowers u ⊔ zpowers v) ⊓ zpowers x := by
      refine Subgroup.mem_inf.mpr
        ⟨?_, mul_mem (inv_mem (zpow_mem_zpowers x a')) (zpow_mem_zpowers x a)⟩
      rw [hx]
      exact mul_mem (mul_mem (mem_sup_left (zpow_mem_zpowers u b'))
        (mem_sup_right (zpow_mem_zpowers v c')))
        (inv_mem (mul_mem (mem_sup_left (zpow_mem_zpowers u b))
          (mem_sup_right (zpow_mem_zpowers v c))))
    rw [hT] at hmem
    exact mem_bot.mp hmem
  have hxa : x ^ a = x ^ a' := by
    have := congrArg (fun w => x ^ a' * w) hx1
    simpa using this
  rw [hxa] at h
  have h' : u ^ b * v ^ c = u ^ b' * v ^ c' := by
    have := congrArg (fun w => (x ^ a')⁻¹ * w) h
    simpa [mul_assoc] using this
  have hu : (u ^ b')⁻¹ * u ^ b = v ^ c' * (v ^ c)⁻¹ := by
    calc (u ^ b')⁻¹ * u ^ b = (u ^ b')⁻¹ * (u ^ b * v ^ c) * (v ^ c)⁻¹ := by group
      _ = (u ^ b')⁻¹ * (u ^ b' * v ^ c') * (v ^ c)⁻¹ := by rw [h']
      _ = v ^ c' * (v ^ c)⁻¹ := by group
  have hu1 : (u ^ b')⁻¹ * u ^ b = 1 := by
    have hmem : (u ^ b')⁻¹ * u ^ b ∈ zpowers u ⊓ zpowers v := by
      refine Subgroup.mem_inf.mpr
        ⟨mul_mem (inv_mem (zpow_mem_zpowers u b')) (zpow_mem_zpowers u b), ?_⟩
      rw [hu]
      exact mul_mem (zpow_mem_zpowers v c') (inv_mem (zpow_mem_zpowers v c))
    rw [h12] at hmem
    exact mem_bot.mp hmem
  have hub : u ^ b = u ^ b' := by
    have := congrArg (fun w => u ^ b' * w) hu1
    simpa using this
  refine ⟨hxa, hub, ?_⟩
  rw [hub] at h'
  exact mul_left_cancel h'

theorem a6vi_zpow_eq_of_three {w : G} (hw : orderOf w = 3) {a b : ℤ}
    (h : w ^ a = w ^ b) : (3 : ℤ) ∣ a - b := by
  have h1 : w ^ (a - b) = 1 := by rw [zpow_sub, h, mul_inv_cancel]
  have := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rwa [hw] at this

theorem a6vi_zpow_eq_of_dvd {w : G} (hw : w ^ 3 = 1) {a b : ℤ} (h : (3 : ℤ) ∣ a - b) :
    w ^ a = w ^ b := by
  obtain ⟨c, hc⟩ := h
  have hab : a = b + 3 * c := by linarith
  rw [hab, zpow_add, zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hw,
    one_zpow, mul_one]

theorem a6vi_exists_order_three {r x : G} (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxe₁ : Commute x (r * x * r⁻¹)) (hxe₂ : Commute x (r * (r * x * r⁻¹) * r⁻¹))
    (he₁₂ : Commute (r * x * r⁻¹) (r * (r * x * r⁻¹) * r⁻¹))
    (hT : (zpowers (r * (r * x * r⁻¹) * r⁻¹) ⊔ zpowers (r * x * r⁻¹)) ⊓ zpowers x = ⊥)
    (h12 : zpowers (r * (r * x * r⁻¹) * r⁻¹) ⊓ zpowers (r * x * r⁻¹) = ⊥)
    (hre₂ : r * (r * (r * x * r⁻¹) * r⁻¹) * r⁻¹ = x)
    (hr3 : r ^ 3 ∈ zpowers x ⊔ (zpowers (r * (r * x * r⁻¹) * r⁻¹) ⊔ zpowers (r * x * r⁻¹))) :
    ∃ k : ℤ, (r * x ^ (-k)) ^ 3 = 1 := by
  set e₁ := r * x * r⁻¹ with he₁
  set e₂ := r * e₁ * r⁻¹ with he₂
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have he₁3 : e₁ ^ 3 = 1 := by rw [he₁, conj_pow, hx3, mul_one, mul_inv_cancel]
  have he₂3 : e₂ ^ 3 = 1 := by rw [he₂, conj_pow, he₁3, mul_one, mul_inv_cancel]
  have he₁1 : e₁ ≠ 1 := by
    intro h; apply hx1
    have : x = r⁻¹ * e₁ * r := by rw [he₁]; group
    rw [this, h]; group
  have he₂1 : e₂ ≠ 1 := by
    intro h; apply he₁1
    have : e₁ = r⁻¹ * e₂ * r := by rw [he₂]; group
    rw [this, h]; group
  have he₁o : orderOf e₁ = 3 := orderOf_eq_prime he₁3 he₁1
  have he₂o : orderOf e₂ = 3 := orderOf_eq_prime he₂3 he₂1
  have hxT : ∀ t ∈ zpowers x, ∀ c ∈ zpowers e₂ ⊔ zpowers e₁, t * c = c * t := by
    intro t ht c hc
    have hle : zpowers e₂ ⊔ zpowers e₁ ≤ centralizer ({x} : Set G) :=
      sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxe₂.eq.symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxe₁.eq.symm))
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp ht
    exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp (hle hc)).symm j).eq
  have h21 : ∀ t ∈ zpowers e₂, ∀ c ∈ zpowers e₁, t * c = c * t := by
    intro t ht c hc
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ht
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hc
    exact ((Commute.zpow_left he₁₂.symm i).zpow_right j).eq
  obtain ⟨z₀, hz₀, t₀, ht₀, hc⟩ := u3l42_decomp hxT hr3
  obtain ⟨b₀, hb₀, a₀, ha₀, ht⟩ := u3l42_decomp h21 ht₀
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz₀
  obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb₀
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha₀
  have hcr : r * r ^ 3 * r⁻¹ = r ^ 3 := by rw [pow_three]; group
  have hconj : r * (x ^ k * (e₂ ^ j * e₁ ^ i)) * r⁻¹ = e₁ ^ k * (x ^ j * e₂ ^ i) := by
    have e : r * (x ^ k * (e₂ ^ j * e₁ ^ i)) * r⁻¹ =
        (r * x ^ k * r⁻¹) * ((r * e₂ ^ j * r⁻¹) * (r * e₁ ^ i * r⁻¹)) := by group
    rw [e, ← conj_zpow, ← conj_zpow, ← conj_zpow, hre₂]
  have hnorm : x ^ k * e₂ ^ j * e₁ ^ i = x ^ j * e₂ ^ i * e₁ ^ k := by
    have hc2 : r ^ 3 = x ^ k * (e₂ ^ j * e₁ ^ i) := by rw [hc, ht]
    have h1 : x ^ k * (e₂ ^ j * e₁ ^ i) = e₁ ^ k * (x ^ j * e₂ ^ i) := by
      calc x ^ k * (e₂ ^ j * e₁ ^ i) = r ^ 3 := hc2.symm
        _ = r * r ^ 3 * r⁻¹ := hcr.symm
        _ = r * (x ^ k * (e₂ ^ j * e₁ ^ i)) * r⁻¹ := by rw [← hc2]
        _ = e₁ ^ k * (x ^ j * e₂ ^ i) := hconj
    have c1 : e₁ ^ k * (x ^ j * e₂ ^ i) = x ^ j * e₂ ^ i * e₁ ^ k := by
      rw [((hxe₁.zpow_zpow j k).mul_left (he₁₂.symm.zpow_zpow i k)).symm.eq]
    rw [mul_assoc, h1, c1]
  obtain ⟨hk, hj, hi⟩ := a6vi_normal_form_eq hT h12 hnorm
  have dkj := a6vi_zpow_eq_of_three hxo hk
  have dji := a6vi_zpow_eq_of_three he₂o hj
  have dik := a6vi_zpow_eq_of_three he₁o hi
  have hjk : e₂ ^ j = e₂ ^ k := a6vi_zpow_eq_of_dvd he₂3 (by omega)
  have hik : e₁ ^ i = e₁ ^ k := a6vi_zpow_eq_of_dvd he₁3 (by omega)
  have hc' : r ^ 3 = x ^ k * e₂ ^ k * e₁ ^ k := by rw [hc, ht, hjk, hik, mul_assoc]
  refine ⟨k, ?_⟩
  have hx' : r⁻¹ * x * r = e₂ := by rw [← hre₂]; group
  have he₂' : r⁻¹ * e₂ * r = e₁ := by rw [he₂]; group
  have e : (r * x ^ (-k)) ^ 3 =
      r ^ 3 * (r⁻¹ * (r⁻¹ * x ^ (-k) * r) * r) * (r⁻¹ * x ^ (-k) * r) * x ^ (-k) := by
    rw [pow_three, pow_three]; group
  rw [e, a6vi_inv_conj_zpow, hx', a6vi_inv_conj_zpow, he₂', hc']
  group

end CFSG.LocalAnalysis.RankThreeTheoremC
