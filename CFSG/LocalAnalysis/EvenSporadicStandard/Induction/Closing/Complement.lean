module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Basic

public section

namespace CFSG.EvenSporadicStandard.Induction.Closing

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H] {L : Subgroup H}

omit [Finite H] in
theorem mem_normalizer_centralizer {g : H} (hg : g ∈ normalizer (L : Set H)) :
    g ∈ normalizer (centralizer (L : Set H) : Set H) := by
  refine mem_normalizer_iff.2 fun x => ⟨fun hx => conj_mem_centralizer hg hx, fun hx => ?_⟩
  have := conj_mem_centralizer (inv_mem hg) hx
  have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
  rwa [e] at this

theorem exists_K₀ (hS2 : ∀ P : Sylow 2 (centralizer (L : Set H)), Nat.card P = 2) {t : H}
    (ht : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) :
    ∃ K₀ : Subgroup H, K₀ ≤ centralizer (L : Set H) ∧ (∀ k ∈ K₀, Odd (orderOf k)) ∧ t ∉ K₀ ∧
      (∀ x ∈ centralizer (L : Set H), ∀ y ∈ centralizer (L : Set H),
        x * y ∈ K₀ ↔ (x ∈ K₀ ↔ y ∈ K₀)) ∧
      ∀ g ∈ normalizer (L : Set H), ∀ x ∈ K₀, g * x * g⁻¹ ∈ K₀ := by
  have hcompl := centralizer_isComplement' hS2 ht ht2
  have hidx : (CFSG.pPrimeCore 2 (centralizer (L : Set H))).index = 2 := by
    rw [hcompl.symm.index_eq_card, Nat.card_zpowers, Subgroup.orderOf_mk, ht2]
  have hodd : Odd (Nat.card (CFSG.pPrimeCore 2 (centralizer (L : Set H)))) :=
    Nat.coprime_two_left.1 CFSG.pPrimeCore_coprime_card
  set C : Subgroup H := centralizer (L : Set H) with hC
  set K₀ : Subgroup H := (CFSG.pPrimeCore 2 C).map C.subtype with hK₀
  have hmemK : ∀ x : H, ∀ hx : x ∈ C, x ∈ K₀ ↔ (⟨x, hx⟩ : ↥C) ∈ CFSG.pPrimeCore 2 C := by
    intro x hx
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact hk
    · intro hk
      exact ⟨⟨x, hx⟩, hk, rfl⟩
  have hK₀odd : ∀ k ∈ K₀, Odd (orderOf k) := by
    rintro _ ⟨k₀, hk₀, rfl⟩
    have h1 : orderOf k₀ ∣ Nat.card (CFSG.pPrimeCore 2 C) := by
      have := orderOf_dvd_natCard (⟨k₀, hk₀⟩ : ↥(CFSG.pPrimeCore 2 C))
      rwa [Subgroup.orderOf_mk] at this
    have h2 : orderOf (C.subtype k₀) = orderOf k₀ := by
      show orderOf ((k₀ : C) : H) = orderOf k₀
      exact Subgroup.orderOf_coe k₀
    rw [h2]
    exact hodd.of_dvd_nat h1
  refine ⟨K₀, map_subtype_le _, hK₀odd, ?_, ?_, ?_⟩
  · intro h
    have := hK₀odd t h
    rw [ht2] at this
    exact absurd this (by decide)
  · intro x hx y hy
    rw [hmemK x hx, hmemK y hy, hmemK (x * y) (C.mul_mem hx hy)]
    exact mul_mem_iff_of_index_two hidx (a := ⟨x, hx⟩) (b := ⟨y, hy⟩)
  · intro g hg x hx
    exact conj_mem_map_pPrimeCore (mem_normalizer_centralizer hg) hx


namespace ClosingSetup

variable {N : Subgroup H} {t u : H} (S : ClosingSetup H N L t u)
include S

theorem t_not_mem_sup {K₀ : Subgroup H} (hK₀C : K₀ ≤ centralizer (L : Set H))
    (hK₀odd : ∀ k ∈ K₀, Odd (orderOf k)) : t ∉ L ⊔ K₀ := by
  intro h
  obtain ⟨ℓ, hℓ, k, hk, htℓk⟩ := exists_mul_of_mem_sup_of_le_centralizer hK₀C h
  have hℓC : ℓ ∈ centralizer (L : Set H) := by
    have : ℓ = t * k⁻¹ := by rw [htℓk]; group
    rw [this]
    exact (centralizer (L : Set H)).mul_mem S.t_mem
      ((centralizer (L : Set H)).inv_mem (hK₀C hk))
  have hℓodd : Odd (orderOf ℓ) :=
    odd_orderOf_of_mem_center S.centre_odd hℓ (fun x hx => (mem_centralizer_iff.1 hℓC x hx))
  have hcomm : Commute ℓ k := mem_centralizer_iff.1 (hK₀C hk) ℓ hℓ
  have h1 : orderOf t ∣ (orderOf ℓ).lcm (orderOf k) := by
    rw [htℓk]
    exact hcomm.orderOf_mul_dvd_lcm
  have h2 : (orderOf ℓ).lcm (orderOf k) ∣ orderOf ℓ * orderOf k := Nat.lcm_dvd_mul _ _
  have h3 : 2 ∣ orderOf ℓ * orderOf k := by
    have := h1.trans h2
    rwa [S.t_order] at this
  exact (Nat.not_even_iff_odd.2 (hℓodd.mul (hK₀odd k hk))) (even_iff_two_dvd.2 h3)

end ClosingSetup

end CFSG.EvenSporadicStandard.Induction.Closing
