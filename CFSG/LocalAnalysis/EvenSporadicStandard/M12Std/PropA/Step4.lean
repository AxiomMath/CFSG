module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M12Std.Layer0

public section

namespace CFSG.EvenSporadicStandard.M12Std.PropA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

section Certified


theorem centralizer_le_of_le_normalizer (h : StdHyp G L) (hL : IsSporadic L .M12) {t x : G}
    (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) (hxL : x ∈ L) (hx2 : orderOf x = 2)
    (hN : centralizer ({x} : Set G) ≤ normalizer (L : Set G)) :
    centralizer ({x} : Set G) ≤ centralizer ({t} : Set G) := by
  set C := centralizer (L : Set G) with hC
  have hNC : centralizer ({x} : Set G) ≤ normalizer (C : Set G) := by
    obtain ⟨-, -, -, hN', -⟩ := h.standard
    rw [hN']
    exact hN
  have hCx : C ≤ centralizer ({x} : Set G) := fun c hc =>
    mem_centralizer_iff.2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]
      exact mem_centralizer_iff.1 hc x hxL
  have hbot := map_pPrimeCore_inf_eq_bot hNC (h.oddCore x hx2)
  have hcore : CFSG.pPrimeCore 2 C = ⊥ := by
    refine eq_bot_iff.2 fun k hk => ?_
    have hmem : (k : G) ∈ (CFSG.pPrimeCore 2 C).map C.subtype ⊓ centralizer ({x} : Set G) :=
      ⟨⟨k, hk, rfl⟩, hCx k.2⟩
    rw [hbot, mem_bot] at hmem
    exact (mem_bot).2 (Subtype.ext hmem)
  have htop : zpowers (⟨t, ht⟩ : C) = ⊤ := by
    have hc := centralizer_isComplement' (h.card_sylow_eq_two_m12 hL) ht ht2
    rw [hcore] at hc
    exact isComplement'_bot_left.1 hc
  intro c hc
  have hs : c * t * c⁻¹ ∈ C := (mem_normalizer_iff.1 (hNC hc) t).1 ht
  have hzs : (⟨c * t * c⁻¹, hs⟩ : C) ∈ zpowers (⟨t, ht⟩ : C) := by rw [htop]; exact mem_top _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hzs
  have hk' : t ^ k = c * t * c⁻¹ := by
    have := congrArg Subtype.val hk
    simpa using this
  have hst : c * t * c⁻¹ = t := by
    rw [← hk', ← zpow_mod_orderOf, ht2]
    have h01 : k % (2 : ℕ) = 0 ∨ k % (2 : ℕ) = 1 := by omega
    rcases h01 with h0 | h1
    · exfalso
      have : c * t * c⁻¹ = 1 := by rw [← hk', ← zpow_mod_orderOf, ht2, h0, zpow_zero]
      have : t = 1 := by
        have h' : c⁻¹ * (c * t * c⁻¹) * c = t := by group
        rw [this, mul_one, inv_mul_cancel] at h'
        exact h'.symm
      subst this
      simp at ht2
    · rw [h1, zpow_one]
  exact mem_centralizer_singleton_iff.2 (by
    calc c * t = c * t * c⁻¹ * c := by group
      _ = t * c := by rw [hst])

end Certified

end CFSG.EvenSporadicStandard.M12Std.PropA
