module

public import Mathlib.GroupTheory.IsSubnormal
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec10KS2a

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

private theorem sl23_commutator_order_four (x : SL23) (hx : x ^ 4 ≠ 1) :
    ∃ g : SL23, (x * g * x⁻¹ * g⁻¹) ^ 4 = 1 ∧
      (x * g * x⁻¹ * g⁻¹) * (x * g * x⁻¹ * g⁻¹) ≠ 1 :=
  (by decide : ∀ x : SL23, x ^ 4 ≠ 1 → ∃ g : SL23,
    (x * g * x⁻¹ * g⁻¹) ^ 4 = 1 ∧
      (x * g * x⁻¹ * g⁻¹) * (x * g * x⁻¹ * g⁻¹) ≠ 1) x hx

private theorem sl23_q8_eq_or_conj (c : SL23) (hc4 : c ^ 4 = 1) (hc2 : c * c ≠ 1) :
    ∀ q : SL23, q ^ 4 = 1 → q = 1 ∨ q = c * c ∨ ∃ g : SL23, q = g * c * g⁻¹ :=
  (by decide : ∀ c : SL23, c ^ 4 = 1 → c * c ≠ 1 → ∀ q : SL23, q ^ 4 = 1 →
    q = 1 ∨ q = c * c ∨ ∃ g : SL23, q = g * c * g⁻¹) c hc4 hc2

private theorem sl23_cover (x : SL23) (hx : x ^ 4 ≠ 1) (g : SL23) :
    ∃ q : SL23, q ^ 4 = 1 ∧ (g = q ∨ g = q * x ∨ g = q * x * x) :=
  (by decide : ∀ x : SL23, x ^ 4 ≠ 1 → ∀ g : SL23,
    ∃ q : SL23, q ^ 4 = 1 ∧ (g = q ∨ g = q * x ∨ g = q * x * x)) x hx g

theorem sl23_normal_dichotomy {N : Subgroup SL23} (hN : N.Normal) :
    N = ⊤ ∨ ∀ x ∈ N, x ^ 4 = 1 := by
  by_cases h : ∀ x ∈ N, x ^ 4 = 1
  · exact Or.inr h
  · left
    push Not at h
    obtain ⟨x, hxN, hx4⟩ := h
    obtain ⟨g₀, hc4, hc2⟩ := sl23_commutator_order_four x hx4
    have hcN : x * g₀ * x⁻¹ * g₀⁻¹ ∈ N := by
      have h1 : g₀ * x * g₀⁻¹ ∈ N := hN.conj_mem x hxN g₀
      have h2 : x * (g₀ * x * g₀⁻¹)⁻¹ ∈ N := N.mul_mem hxN (N.inv_mem h1)
      convert h2 using 1
      group
    rw [Subgroup.eq_top_iff']
    intro g
    obtain ⟨q, hq4, hgq⟩ := sl23_cover x hx4 g
    have hqN : q ∈ N := by
      rcases sl23_q8_eq_or_conj (x * g₀ * x⁻¹ * g₀⁻¹) hc4 hc2 q hq4 with h1 | h1 | ⟨g', h1⟩
      · rw [h1]; exact N.one_mem
      · rw [h1]; exact N.mul_mem hcN hcN
      · rw [h1]; exact hN.conj_mem _ hcN g'
    rcases hgq with h1 | h1 | h1
    · rw [h1]; exact hqN
    · rw [h1]; exact N.mul_mem hqN hxN
    · rw [h1]; exact N.mul_mem (N.mul_mem hqN hxN) hxN

theorem sl23_subnormal_dichotomy {N : Subgroup SL23} (hN : N.IsSubnormal) :
    N = ⊤ ∨ ∀ x ∈ N, x ^ 4 = 1 := by
  by_cases h : N = ⊤
  · exact Or.inl h
  · right
    obtain ⟨K, hKnorm, hNK, hKlt⟩ := hN.exists_normal_and_le_and_lt_top_of_ne h
    rcases sl23_normal_dichotomy hKnorm with hK | hK
    · exact absurd hK hKlt.ne
    · intro x hx; exact hK x (hNK hx)

theorem sec5_subnormal_dichotomy {G : Type} [Group G] {K H : Subgroup G} (e : ↥K ≃* SL23)
    (hHK : H ≤ K) (hH : (H.subgroupOf K).IsSubnormal) : H = K ∨ ∀ x ∈ H, x ^ 4 = 1 := by
  have hNsub : ((H.subgroupOf K).map e.toMonoidHom).IsSubnormal := hH.map e.surjective
  rcases sl23_subnormal_dichotomy hNsub with hN | hN
  · left
    have htop : (H.subgroupOf K).map e.toMonoidHom = (⊤ : Subgroup ↥K).map e.toMonoidHom := by
      rw [hN, Subgroup.map_top_of_surjective _ e.surjective]
    have hsub : H.subgroupOf K = ⊤ := Subgroup.map_injective e.injective htop
    exact le_antisymm hHK (Subgroup.subgroupOf_eq_top.mp hsub)
  · right
    intro x hx
    have hxK : x ∈ K := hHK hx
    have hxN : e ⟨x, hxK⟩ ∈ (H.subgroupOf K).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem _ (by rwa [Subgroup.mem_subgroupOf])
    have h4 : (e ⟨x, hxK⟩) ^ 4 = 1 := hN _ hxN
    have hthisK : (⟨x, hxK⟩ : ↥K) ^ 4 = 1 := by
      have h := congrArg e.symm h4
      simpa using h
    simpa using congrArg (fun y : ↥K => (y : G)) hthisK

theorem sl23_eq_top_of_odd {Y : Subgroup SL23} (h : ∀ x : SL23, Odd (orderOf x) → x ∈ Y) :
    Y = ⊤ := by
  have h3 : ∀ x : SL23, x ^ 3 = 1 → x ∈ Y := fun x hx =>
    h x ((show Odd 3 by decide).of_dvd_nat (orderOf_dvd_iff_pow_eq_one.mpr hx))
  obtain ⟨a, b, ha3, ha4, hb3, hab4, hab2⟩ :=
    (by decide : ∃ a b : SL23, a ^ 3 = 1 ∧ a ^ 4 ≠ 1 ∧ b ^ 3 = 1 ∧
      (a * b) ^ 4 = 1 ∧ (a * b) * (a * b) ≠ 1)
  have haY : a ∈ Y := h3 a ha3
  have habY : a * b ∈ Y := Y.mul_mem haY (h3 b hb3)
  have hq8 : ∀ q : SL23, q ^ 4 = 1 → q ∈ Y := by
    intro q hq4
    rcases sl23_q8_eq_or_conj (a * b) hab4 hab2 q hq4 with h1 | h1 | ⟨g, h1⟩
    · rw [h1]; exact Y.one_mem
    · rw [h1]; exact Y.mul_mem habY habY
    · rw [h1]
      have hga : g * a * g⁻¹ ∈ Y := h3 _ (by rw [conj_pow, ha3]; group)
      have hgb : g * b * g⁻¹ ∈ Y := h3 _ (by rw [conj_pow, hb3]; group)
      convert Y.mul_mem hga hgb using 1
      group
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨q, hq4, hgq⟩ := sl23_cover a ha4 g
  have hqY : q ∈ Y := hq8 q hq4
  rcases hgq with h1 | h1 | h1
  · rw [h1]; exact hqY
  · rw [h1]; exact Y.mul_mem hqY haY
  · rw [h1]; exact Y.mul_mem (Y.mul_mem hqY haY) haY

theorem sec5_le_of_odd {G : Type} [Group G] {P : Subgroup G} (e : ↥P ≃* SL23) {Y : Subgroup G}
    (h : ∀ x ∈ P, Odd (orderOf x) → x ∈ Y) : P ≤ Y := by
  have hY' : Y.comap (P.subtype.comp e.symm.toMonoidHom) = ⊤ := by
    apply sl23_eq_top_of_odd
    intro s hs
    rw [Subgroup.mem_comap]
    change ((e.symm s : ↥P) : G) ∈ Y
    exact h _ (e.symm s).2 (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact hs)
  intro x hx
  have hxmem : e ⟨x, hx⟩ ∈ Y.comap (P.subtype.comp e.symm.toMonoidHom) := by
    rw [hY']; exact Subgroup.mem_top _
  rw [Subgroup.mem_comap] at hxmem
  simpa using hxmem

end CFSG.OddStandard.SmallF3.Omega
