module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Hyp
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Fusion

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

@[expose] def fusedSet (u t : G) : Set G :=
  {t' | IsConj t t' ∧ t' * u = u * t' ∧ t' * t = t * t'}

@[expose] def Sol78Fusion (u t : G) : Prop := ∀ t' ∈ fusedSet u t, t' = t ∨ t' = u * t

@[expose] def Sol78UMoves (L : Subgroup G) (u : G) : Prop :=
  ∀ s ∈ normalizer (L : Set G), s * s = 1 → s ∉ centralizer (L : Set G) →
    ∃ h ∈ L, (h * u * h⁻¹) * s = s * (h * u * h⁻¹)

omit [Finite G] in
theorem mul_self_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  rw [← pow_two, ← hx]
  exact pow_orderOf_eq_one x

omit [Finite G] in
theorem ne_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x ≠ 1 := by
  rintro rfl
  rw [orderOf_one] at hx
  exact absurd hx (by decide)

omit [Finite G] in
theorem zpow_eq_one_or_self_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) (k : ℤ) :
    x ^ k = 1 ∨ x ^ k = x := by
  rw [← zpow_mod_orderOf, hx]
  have : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases this with h0 | h1
  · left
    rw [h0]
    simp
  · right
    rw [h1]
    simp

theorem eq_of_mem_fusedSet (h : SolomonHyp G L K t u) (hf : Sol78Fusion u t) {t' : G}
    (ht' : t' ∈ fusedSet u t) : t' = t := by
  rcases hf t' ht' with h1 | h1
  · exact h1
  · exfalso
    have hc : IsConj t (u * t) := h1 ▸ ht'.1
    have := h.simpleL
    have hu2 : orderOf (⟨u, h.u_mem⟩ : L) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact h.u_order
    obtain ⟨⟨y, hyL⟩, hxne, hxcomm⟩ := exists_fused_commuting_involution h.nonabelianL hu2
    have hne : y * u * y⁻¹ ≠ u := fun e => hxne (Subtype.ext e)
    have hcomm : (y * u * y⁻¹) * u = u * (y * u * y⁻¹) := congrArg Subtype.val hxcomm
    have hu₃L : y * u * y⁻¹ ∈ L := L.mul_mem (L.mul_mem hyL h.u_mem) (L.inv_mem hyL)
    have hyt : y * t = t * y := mem_centralizer_iff.1 h.t_mem y hyL
    have hu₃t : (y * u * y⁻¹) * t = t * (y * u * y⁻¹) :=
      mem_centralizer_iff.1 h.t_mem _ hu₃L
    have hyt' : y * t * y⁻¹ = t := by rw [hyt]; group
    have hut : t * u = u * t := h.u_comm_t.symm
    have hconj : y * (u * t) * y⁻¹ = (y * u * y⁻¹) * t := by
      calc y * (u * t) * y⁻¹ = (y * u * y⁻¹) * (y * t * y⁻¹) := by group
        _ = (y * u * y⁻¹) * t := by rw [hyt']
    generalize hw : y * u * y⁻¹ = w at hne hcomm hu₃L hu₃t hconj
    have hmem : w * t ∈ fusedSet u t := by
      refine ⟨hc.trans (isConj_iff.2 ⟨y, hconj⟩), ?_, ?_⟩
      · calc w * t * u = w * (t * u) := mul_assoc w t u
          _ = w * (u * t) := by rw [hut]
          _ = (w * u) * t := (mul_assoc w u t).symm
          _ = (u * w) * t := by rw [hcomm]
          _ = u * (w * t) := mul_assoc u w t
      · calc w * t * t = (w * t) * t := rfl
          _ = (t * w) * t := by rw [hu₃t]
          _ = t * (w * t) := mul_assoc t w t
    rcases hf _ hmem with h3 | h3
    · have h4 : w = 1 := mul_eq_right.1 h3
      apply ne_one_of_orderOf_eq_two h.u_order
      have h5 : u = y⁻¹ * (y * u * y⁻¹) * y := by group
      rw [h5, hw, h4]
      group
    · exact hne (mul_right_cancel h3)

theorem solomon_closing_3_12_3 (hStd : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h : SolomonHyp G L K t u) (hf : Sol78Fusion u t) (hm : Sol78UMoves L u) : False := by
  have ht2 := h.t_order
  have := h.simple
  obtain ⟨g, hne, hcomm⟩ := exists_fused_commuting_involution h.nonabelian ht2
  set t₁ : G := g * t * g⁻¹ with ht₁
  have ht₁t₁ : t₁ * t₁ = 1 := by
    have htt := mul_self_eq_one_of_orderOf_eq_two ht2
    calc t₁ * t₁ = g * (t * t) * g⁻¹ := by rw [ht₁]; group
      _ = 1 := by rw [htt]; group
  have ht₁ne : t₁ ≠ 1 := by
    intro e
    apply ne_one_of_orderOf_eq_two ht2
    have : g * t * g⁻¹ = 1 := e
    simpa using this
  have ht₁C : t₁ ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 hcomm
  have hN : t₁ ∈ normalizer (L : Set G) := hStd.centralizer_le_normalizer h.t_mem ht2 ht₁C
  have hnC : t₁ ∉ centralizer (L : Set G) := by
    intro hc
    have hmem : t₁ ∈ centralizer (L : Set G) ⊓ centralizer ({t} : Set G) := ⟨hc, ht₁C⟩
    rw [hStd.centralizer_inf_centralizer_eq_zpowers hS h.t_mem ht2] at hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    rcases zpow_eq_one_or_self_of_orderOf_eq_two ht2 k with h1 | h1
    · exact ht₁ne (hk.symm.trans h1)
    · exact hne (hk.symm.trans h1)
  obtain ⟨x, hxL, hxcomm⟩ := hm t₁ hN ht₁t₁ hnC
  have hxt : x * t = t * x := mem_centralizer_iff.1 h.t_mem x hxL
  have hxit : x⁻¹ * t = t * x⁻¹ := mem_centralizer_iff.1 h.t_mem x⁻¹ (L.inv_mem hxL)
  have hmem : x⁻¹ * t₁ * x ∈ fusedSet u t := by
    refine ⟨isConj_iff.2 ⟨x⁻¹ * g, ?_⟩, ?_, ?_⟩
    · rw [ht₁]; group
    · calc x⁻¹ * t₁ * x * u = x⁻¹ * (t₁ * (x * u * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * u * x⁻¹) * t₁) * x := by rw [← hxcomm]
        _ = u * (x⁻¹ * t₁ * x) := by group
    · calc x⁻¹ * t₁ * x * t = x⁻¹ * t₁ * (x * t) := by rw [mul_assoc]
        _ = x⁻¹ * t₁ * (t * x) := by rw [hxt]
        _ = x⁻¹ * (t₁ * t) * x := by group
        _ = x⁻¹ * (t * t₁) * x := by rw [hcomm]
        _ = (x⁻¹ * t) * t₁ * x := by group
        _ = (t * x⁻¹) * t₁ * x := by rw [hxit]
        _ = t * (x⁻¹ * t₁ * x) := by group
  have h1 := eq_of_mem_fusedSet h hf hmem
  apply hne
  calc g * t * g⁻¹ = x * (x⁻¹ * t₁ * x) * x⁻¹ := by rw [ht₁]; group
    _ = x * t * x⁻¹ := by rw [h1]
    _ = t := by rw [hxt]; group

end CFSG.EvenSporadicStandard.Solomon78
