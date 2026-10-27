module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.General

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

theorem centralizer_eq_zpowers_of_hyp38 (hStd : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h : SolomonHyp G L K t u) : centralizer (L : Set G) = zpowers t := by
  have ht : t ∈ centralizer (L : Set G) := h.t_mem
  have ht2 := h.t_order
  set C : Subgroup G := centralizer (L : Set G) with hC
  have hN : normalizer (C : Set G) = normalizer (L : Set G) := hStd.standard.2.2.2.1
  have hHC : centralizer ({u} : Set G) ≤ normalizer (C : Set G) := hN ▸ h.hyp38_2
  have hbot := map_pPrimeCore_inf_eq_bot hHC (hStd.oddCore u h.u_order)
  have hCu : C ≤ centralizer ({u} : Set G) := fun c hc =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hc) u h.u_mem).symm
  have hO : CFSG.pPrimeCore 2 C = ⊥ := by
    refine (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 ?_
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ C := by
      obtain ⟨k, -, rfl⟩ := hx
      exact k.2
    have : x ∈ (CFSG.pPrimeCore 2 C).map C.subtype ⊓ centralizer ({u} : Set G) :=
      ⟨hx, hCu hxC⟩
    rw [hbot] at this
    exact this
  have hcompl := centralizer_isComplement' hS ht ht2
  rw [hO, Subgroup.isComplement'_bot_left] at hcompl
  apply le_antisymm
  · intro c hc
    have : (⟨c, hc⟩ : C) ∈ zpowers (⟨t, ht⟩ : C) := hcompl ▸ mem_top _
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 this
    exact mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩
  · exact zpowers_le.2 ht

theorem centralizer_u_le_centralizer_t (hStd : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h : SolomonHyp G L K t u) : centralizer ({u} : Set G) ≤ centralizer ({t} : Set G) := by
  intro x hx
  have hxN : x ∈ normalizer (L : Set G) := h.hyp38_2 hx
  have hxC : x * t * x⁻¹ ∈ centralizer (L : Set G) := by
    have hN : normalizer (centralizer (L : Set G) : Set G) = normalizer (L : Set G) :=
      hStd.standard.2.2.2.1
    have := (mem_normalizer_iff.1 (hN ▸ hxN : x ∈ normalizer (centralizer (L : Set G) : Set G)) t).1
      h.t_mem
    exact this
  rw [centralizer_eq_zpowers_of_hyp38 hStd hS h] at hxC
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hxC
  have ht2 := h.t_order
  have hne : x * t * x⁻¹ ≠ 1 := by
    intro e
    apply ne_one_of_orderOf_eq_two ht2
    have : x * t * x⁻¹ = 1 := e
    simpa using this
  rcases zpow_eq_one_or_self_of_orderOf_eq_two ht2 k with h1 | h1
  · exact absurd (hk.symm.trans h1) hne
  · apply mem_centralizer_singleton_iff.2
    have e : x * t * x⁻¹ = t := hk.symm.trans h1
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [e]

end CFSG.EvenSporadicStandard.Solomon78
