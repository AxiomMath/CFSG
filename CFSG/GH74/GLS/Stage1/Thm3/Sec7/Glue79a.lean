module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Dih
public import CFSG.GH74.GLS.Stage1.Thm3.Sec7.Glue77a

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec7

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
  CFSG.GH74.GLS.Stage1.Thm2.Recip
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G} {t u : G} {q : ℕ}

namespace Cfg7

theorem S_le_normP (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) :
    S ≤ normalizer ((Pz S z : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h.normP hII s hs x hx
  · intro hx
    have := h.normP hII s⁻¹ (S.inv_mem hs) _ hx
    simpa [mul_assoc] using this

theorem sq_mem_P (hII : II4_4_4_center) (h : Cfg7 G z S K₁ K₂ t u q) {w : G} (hw2 : w * w = 1)
    (hwt : t * w = w * t) (hSeq : S = Pz S z ⊔ Ysub t w) (hYS : Ysub t w ≤ S) :
    ∀ s ∈ S, s * s ∈ Pz S z := by
  intro s hs
  have hs' : s ∈ Ysub t w ⊔ Pz S z := by rw [sup_comm, ← hSeq]; exact hs
  obtain ⟨b, hb, p, hp, rfl⟩ := A.mem_sup_of_le_normalizer (hYS.trans (h.S_le_normP hII)) hs'
  have hb2 : b * b = 1 := by
    rcases A.mem_sup_zpowers_two h.t_sq hw2 hwt hb with rfl | rfl | rfl | rfl
    · exact mul_one 1
    · exact h.t_sq
    · exact hw2
    · calc t * w * (t * w) = (t * (w * t)) * w := by group
        _ = (t * (t * w)) * w := by rw [hwt]
        _ = (t * t) * (w * w) := by group
        _ = 1 := by rw [h.t_sq, hw2, mul_one]
  have e : b * p * (b * p) = (b * p * b⁻¹) * (b * b) * p := by group
  rw [e, hb2, mul_one]
  exact (Pz S z).mul_mem (h.normP hII b (hYS hb) p hp) hp

theorem exists_conj_in_coset (hII : II4_4_4_center) (hL79 : L79_C_S_u) (h : Cfg7 G z S K₁ K₂ t u q)
    (hc73 : Concl73 z S K₁ K₂) (hc74 : Concl74c z t) {w : G}
    (hconcl : Concl72abcf z S K₁ K₂ t q w) (hw1 : w ≠ 1) (hsq : ∀ s ∈ S, s * s ∈ Pz S z)
    {x : G} (hxS : x ∈ S) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxP : x ∉ Pz S z) :
    ∃ p ∈ Pz S z, IsConj z (p * x) := by
  by_contra hnot
  push Not at hnot
  have hM := h.m4 hII
  have hzS := h.z_mem_S hII
  have hzP := h.z_mem_Pz hII
  have hxo : orderOf x = 2 := orderOf_eq_prime (by simpa [pow_two] using hx2) hx1
  have hxconj : IsConj (t * z) x := by
    rcases hc74.1 x hxo with h1 | h1
    · have := hnot 1 (one_mem _)
      rw [one_mul] at this
      exact absurd h1 this
    · exact h1
  have hCS2 : IsPGroup 2 ↥(S ⊓ centralizer ({x} : Set G)) := (h.S_pgroup hII).to_le inf_le_left
  obtain ⟨V, hV, hCV⟩ := M.exists_syl2In_ge hCS2
    (inf_le_right : S ⊓ centralizer ({x} : Set G) ≤ centralizer ({x} : Set G))
  have hxz : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.1 (h.S_le_C hII hxS)
  have hzCS : z ∈ S ⊓ centralizer ({x} : Set G) :=
    Subgroup.mem_inf.2 ⟨hzS, Subgroup.mem_centralizer_singleton_iff.2 hxz.symm⟩
  have hzV : z ∈ V := hCV hzCS
  obtain ⟨V₁, V₂, n, hn3, hV₁V, hV₂V, hcomm, hinf, hsup, hd₁, hd₂, hxV₁, hxcen⟩ :=
    hL79 G z S K₁ K₂ t u q w h hconcl hw1 x hxconj V hV
  obtain ⟨hn2, k, hk, hk2, ⟨e⟩⟩ := hd₁
  have : NeZero k := ⟨by omega⟩
  have h4k : 4 ∣ k := by
    have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h2 : k = 2 ^ (n - 1) := by omega
    rw [h2]
    exact (pow_dvd_pow 2 (by omega : 2 ≤ n - 1))
  obtain ⟨⟨a, haV₁, haa⟩, hconjV⟩ := Dih.dih_facts h4k e hxV₁ hxcen hx1
  by_cases hcen : ∀ a ∈ V₁, a * z = z * a
  ·
    have haC : a ∈ centralizer ({z} : Set G) := Subgroup.mem_centralizer_singleton_iff.2 (hcen a haV₁)
    have haV : a ∈ V := hV₁V haV₁
    have hA2 : IsPGroup 2 ↥(zpowers a) := hV.2.1.to_le (zpowers_le.2 haV)
    obtain ⟨P', hP', haP'⟩ := M.exists_syl2In_ge hA2 (zpowers_le.2 haC)
    obtain ⟨c, hcC, hcP⟩ := hM.S_syl.exists_conj hP'
    have hca : c * a * c⁻¹ ∈ S := by
      have : a ∈ M.cj S c := hcP ▸ haP' (mem_zpowers a)
      exact M.mem_cj.1 this
    have hcx : c * x * c⁻¹ ∈ Pz S z := by
      have e1 : c * x * c⁻¹ = (c * a * c⁻¹) * (c * a * c⁻¹) := by rw [← haa]; group
      rw [e1]
      exact hsq _ hca
    have hcz : (c⁻¹)⁻¹ * z * c⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hcC
      rw [inv_inv]
      calc c * z * c⁻¹ = z * c * c⁻¹ := by rw [this]
        _ = z := by group
    exact hxP (h.P_of_conj hII hc73 hxS (g := c⁻¹) hcz (by simpa using hcx))
  ·
    push Not at hcen
    obtain ⟨a₀, ha₀, ha₀z⟩ := hcen
    have hzV' : z ∈ V₁ ⊔ V₂ := hsup ▸ hzV
    obtain ⟨z₁, hz₁, z₂, hz₂, hzz⟩ := A.mem_sup_of_commute hcomm hzV'
    have hz₁z₂ : z₁ * z₂ = z₂ * z₁ := hcomm z₁ hz₁ z₂ hz₂
    have hz₁sq : z₁ * z₁ = 1 := by
      have h1 : z₁ * z₁ * (z₂ * z₂) = 1 := by
        calc z₁ * z₁ * (z₂ * z₂) = z₁ * (z₁ * z₂) * z₂ := by group
          _ = z₁ * (z₂ * z₁) * z₂ := by rw [hz₁z₂]
          _ = (z₁ * z₂) * (z₁ * z₂) := by group
          _ = z * z := by rw [← hzz]
          _ = 1 := h.z_sq
      have h2 : z₁ * z₁ = (z₂ * z₂)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : z₁ * z₁ ∈ V₁ ⊓ V₂ := ⟨V₁.mul_mem hz₁ hz₁, by rw [h2]; exact V₂.inv_mem (V₂.mul_mem hz₂ hz₂)⟩
      rw [hinf, Subgroup.mem_bot] at h3
      exact h3
    have hnc : ∃ b ∈ V₁, b * z₁ ≠ z₁ * b := by
      refine ⟨a₀, ha₀, fun hh => ha₀z ?_⟩
      have h2 : a₀ * z₂ = z₂ * a₀ := hcomm a₀ ha₀ z₂ hz₂
      calc a₀ * z = a₀ * (z₁ * z₂) := by rw [hzz]
        _ = (a₀ * z₁) * z₂ := by group
        _ = (z₁ * a₀) * z₂ := by rw [hh]
        _ = z₁ * (a₀ * z₂) := by group
        _ = z₁ * (z₂ * a₀) := by rw [h2]
        _ = z * a₀ := by rw [hzz]; group
    obtain ⟨hh, hhV₁, hhe⟩ := hconjV z₁ hz₁ hz₁sq hnc
    apply hnot z hzP
    refine isConj_iff.2 ⟨hh, ?_⟩
    have hhz₂ : hh * z₂ = z₂ * hh := hcomm hh hhV₁ z₂ hz₂
    have hxz₂ : x * z₂ = z₂ * x := hcomm x hxV₁ z₂ hz₂
    calc hh * z * hh⁻¹ = (hh * z₁ * hh⁻¹) * (hh * z₂ * hh⁻¹) := by rw [hzz]; group
      _ = (z₁ * x) * z₂ := by
        rw [hhe]
        have : hh * z₂ * hh⁻¹ = z₂ := by
          calc hh * z₂ * hh⁻¹ = z₂ * hh * hh⁻¹ := by rw [hhz₂]
            _ = z₂ := by group
        rw [this]
      _ = z₁ * z₂ * x := by
        calc z₁ * x * z₂ = z₁ * (x * z₂) := by group
          _ = z₁ * (z₂ * x) := by rw [hxz₂]
          _ = z₁ * z₂ * x := by group
      _ = z * x := by rw [← hzz]

end Cfg7

end CFSG.GH74.GLS.Stage1.Thm3.Sec7
