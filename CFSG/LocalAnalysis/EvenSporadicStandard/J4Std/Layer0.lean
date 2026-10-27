module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.Setup
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.SylowTwo
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Centralizer

public section

namespace CFSG.EvenSporadicStandard.J4Std

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem _root_.CFSG.EvenSporadicStandard.StdHyp.setting_of_isSq (h : StdHyp G L)
    (hI : HypothesisOne (L ⧸ center L))
    (hinn : ∀ α : MulAut (L ⧸ center L), ∃ q, α = MulAut.conj q) (hZ : center L = ⊥)
    (hsq : ∀ u ∈ L, u * u = 1 → ∃ c ∈ L, c * c = u) {z : G}
    (hz : z ∈ centralizer (L : Set G)) (hz2 : orderOf z = 2) : Setting L z := by
  have hS := h.card_sylow_eq_two_of_inner hI hinn
  obtain ⟨hC, hd, hcomm⟩ := h.centralizer_eq_prod_of_center_eq_bot hS hz hz2
    (h.centralizer_le_sup_centralizer_of_inner hz hz2 hinn) hZ
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hz2; exact absurd hz2 (by decide)
  have hzpow : ∀ b ∈ Subgroup.zpowers z, b = 1 ∨ b = z := by
    intro b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_mod_orderOf, hz2]
    rcases Int.emod_two_eq_zero_or_one k with h0 | h0
    · left; simp [h0]
    · right; simp [h0]
  exact
    { z_mul_self := hzz
      z_ne_one := hz1
      z_not_mem := fun hzL => hz1 (mem_bot.1 (hd.le_bot ⟨hzL, mem_zpowers z⟩))
      z_comm := fun l hl => (mem_centralizer_iff.1 hz l hl).symm
      centralizer_z := by
        intro g hg
        have hg' : g ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hg.symm
        rw [hC] at hg'
        obtain ⟨a, ha, b, hb, rfl⟩ :=
          CFSG.EvenSporadicStandard.exists_mul_of_mem_sup_of_le_centralizer hcomm hg'
        rcases hzpow b hb with rfl | rfl
        · exact ⟨a, ha, Or.inl (by simp)⟩
        · exact ⟨a, ha, Or.inr rfl⟩
      isSq := hsq }

end CFSG.EvenSporadicStandard.J4Std
