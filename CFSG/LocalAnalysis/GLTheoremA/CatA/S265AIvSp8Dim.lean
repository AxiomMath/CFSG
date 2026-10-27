module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.I2016SpFpfFix

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open Polynomial Module CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
open CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8 CFSG.LocalAnalysis.GLTheoremA.I2016Sp

theorem finrank_ker_eq_six_of_card {g : StatedSp 4 (ZMod 2)} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hcard : 1451520 ≤ Nat.card ↥(Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2))))) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (spEnd g - 1)) = 6 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s₀, hC⟩ := exists_class_spSupported hg3 hg1
  obtain ⟨s₁, hs₁, hs4⟩ := dimension_count hg3 hg1
  have blocks := sp8_blocks g (orderOf_eq_prime hg3 hg1)
  generalize primaryMultiplicity (spEnd g) q2 = m at hC hs4
  generalize spSupported g {(X - 1 : (ZMod 2)[X])} = A₀ at hC
  generalize spSupported g {q2} = A₁ at hC
  have hsum := hC.sum_eq
  have hone := hC.one_le
  have h1 : Nat.card ↥(Subgroup.centralizer ({g} : Set (StatedSp 4 (ZMod 2)))) ≤
      Nat.card ↥A₀ * Nat.card ↥A₁ := by
    rw [hC.centralizer_eq]
    exact card_sup_le hC.commute
  have hm : m = 1 := by
    rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4) with rfl | rfl | rfl | rfl
    · rfl
    · obtain rfl : s₀ = 2 := by omega
      rw [card_product_two hC] at h1
      omega
    · obtain rfl : s₀ = 1 := by omega
      rw [card_product_three hC] at h1
      omega
    · obtain rfl : s₀ = 0 := by omega
      have hA₀ : A₀ = ⊥ := (hC.fixed.resolve_right (by omega)).2
      obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e₁⟩⟩ := hC.unitary
      have hA₁ : Nat.card ↥A₁ = 77760 := by
        rw [Nat.card_congr e₁.toEquiv]
        exact card_unitary_four hE hsymm hsep hdim
      rw [hA₀, Subgroup.card_bot, hA₁] at h1
      omega
  subst hm
  have h3 : s₁ = 3 := by omega
  have h6 : Module.finrank (ZMod 2)
      ↥(primaryComponent (spEnd g) (X - 1 : (ZMod 2)[X])) = 6 := by
    rw [hs₁, h3]
  rwa [blocks.fixed_eq] at h6

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
