module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoFinalBLines

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup JankoTwelve JankoFinal

namespace JankoFinalB

variable {G : Type} [Group G] [Finite G] {z : G} {fr : JankoFrame G z} {m s : G}
  {W : Subgroup G}

theorem false_of_transvection (h : Hyp fr) (p12 : JankoProp12 fr) (hW : JankoFinalW fr m W s)
    {p σ g₁ : G} (hp : fr.P3bar = zpowers p) (hp3 : orderOf p = 3)
    (hσ : zpowers σ = zpowers s) (hσE : σ ∈ fr.E) (hσ3 : orderOf σ = 3)
    (htσ : fr.t * σ * fr.t⁻¹ = σ⁻¹) (hg₁N : g₁ ∈ normalizer (W : Set G))
    (hg₁σ : g₁ * σ = σ * g₁) (hg₁p : g₁ * p * g₁⁻¹ = σ * p) : False := by
  obtain ⟨r, hrN, hrp, hrs, hrodd⟩ := exists_mem_normalizer_W_comm_p h hW hp
  have hZ : W ⊓ centralizer (W : Set G) = zpowers p ⊔ zpowers σ := by
    rw [center_W_eq h p12 hW, hp, hσ, sup_comm]
  have hσZ : σ ∈ W ⊓ centralizer (W : Set G) := hZ ▸ mem_sup_right (mem_zpowers σ)
  have hpZ : p ∈ W ⊓ centralizer (W : Set G) := hZ ▸ mem_sup_left (mem_zpowers p)
  have hpσ : p * σ = σ * p := mem_centralizer_iff.mp hσZ.2 p hpZ.1
  have hbot : zpowers p ⊓ zpowers σ = ⊥ := by
    rw [hσ, inf_comm, ← le_bot_iff, ← hW.E_inf_S, ← hp]
    exact inf_le_inf (zpowers_le.mpr hW.s_mem_E) (le_sup_left : fr.P3bar ≤ fr.P3bar ⊔ fr.P3bbar)
  have hrσ : r * σ * r⁻¹ ≠ σ := by
    intro hrσ
    apply hrs
    have hrC : r ∈ centralizer (zpowers σ : Set G) := by
      rw [centralizer_zpowers]
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hrσ)
    rw [hσ, centralizer_zpowers] at hrC
    rw [mem_centralizer_singleton_iff.mp hrC, mul_inv_cancel_right]
  have hmem : r * σ * r⁻¹ ∈ zpowers p ⊔ zpowers σ := hZ ▸ conj_mem_center hrN hσZ
  obtain ⟨u, huN, hup, huσ⟩ : ∃ u ∈ normalizer (W : Set G),
      u * p = p * u ∧ u * σ * u⁻¹ = p⁻¹ * σ := by
    rcases conj_eq_mul_or_eq_inv_mul hpσ hp3 hσ3 hbot hrp hrodd hrσ hmem with h1 | h1
    · refine ⟨r * r, mul_mem hrN hrN, ?_, ?_⟩
      · rw [mul_assoc, hrp, ← mul_assoc, hrp, mul_assoc]
      · have hpr : r * p * r⁻¹ = p := by rw [hrp, mul_inv_cancel_right]
        have hp2 : p * p = p⁻¹ :=
          eq_inv_of_mul_eq_one_left (by rw [← pow_three', ← hp3, pow_orderOf_eq_one])
        calc r * r * σ * (r * r)⁻¹ = r * (r * σ * r⁻¹) * r⁻¹ := by group
          _ = r * (p * σ) * r⁻¹ := by rw [h1]
          _ = r * p * r⁻¹ * (r * σ * r⁻¹) := by group
          _ = p * (p * σ) := by rw [hpr, h1]
          _ = p⁻¹ * σ := by rw [← mul_assoc, hp2]
    · exact ⟨r, hrN, hrp, h1⟩
  obtain ⟨hgp, hgσ⟩ := swap_conj hpσ.symm hg₁σ hg₁p hup huσ
  exact false_of_swap h hW hp hσ hσE htσ (mul_mem (mul_mem hg₁N huN) hg₁N) hgp hgσ

theorem false_of_jankoFinalW (h : Hyp fr) (p12 : JankoProp12 fr) (hW : JankoFinalW fr m W s) :
    False := by
  obtain ⟨p, hp, hp3⟩ := h.exists_P3bar_eq
  obtain ⟨g₁, hg₁N, hg₁s, hg₁p, hg₁odd⟩ := exists_mem_normalizer_W_ne h hW hp hp3
  have hZ : W ⊓ centralizer (W : Set G) = zpowers s ⊔ zpowers p := by
    rw [center_W_eq h p12 hW, hp]
  have hpZ : p ∈ W ⊓ centralizer (W : Set G) := hZ ▸ mem_sup_right (mem_zpowers p)
  have hsp : s * p = p * s := (mem_centralizer_iff.mp (s_mem_center h hW).2 p hpZ.1).symm
  have hbot : zpowers s ⊓ zpowers p = ⊥ := by
    rw [← le_bot_iff, ← hW.E_inf_S, ← hp]
    exact inf_le_inf (zpowers_le.mpr hW.s_mem_E) (le_sup_left : fr.P3bar ≤ fr.P3bar ⊔ fr.P3bbar)
  have hmem : g₁ * p * g₁⁻¹ ∈ zpowers s ⊔ zpowers p := hZ ▸ conj_mem_center hg₁N hpZ
  have hts : fr.t * s * fr.t⁻¹ = s⁻¹ := hW.t_mul_s
  rcases conj_eq_mul_or_eq_inv_mul hsp hW.orderOf_s hp3 hbot hg₁s hg₁odd hg₁p hmem with h1 | h1
  · exact false_of_transvection h p12 hW hp hp3 rfl hW.s_mem_E hW.orderOf_s hts hg₁N hg₁s h1
  · refine false_of_transvection h p12 hW hp hp3 zpowers_inv (inv_mem hW.s_mem_E)
      (by rw [orderOf_inv, hW.orderOf_s]) ?_ hg₁N (Commute.inv_right hg₁s).eq h1
    have ht' : fr.t * s⁻¹ * fr.t⁻¹ = (fr.t * s * fr.t⁻¹)⁻¹ := by group
    rw [ht', hts]

end JankoFinalB

open JankoFinalB in
theorem jankoStepFinal : JankoStepFinal := by
  intro G _ _ z fr hset hfrs p7 p9 p10 p11 p12
  obtain ⟨m, W, s, hW⟩ := exists_jankoFinalW' fr hset hfrs p7 p9 p10 p11 p12
  exact false_of_jankoFinalW ⟨hset, hfrs, p7, p9, p10, p11⟩ p12 hW

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
