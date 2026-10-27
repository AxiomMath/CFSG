module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.EgawaDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.Setting

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G}

theorem localSetting_of_centralizer_eq
    (hz2 : orderOf z = 2)
    (hcen : zpowers z ≤ centralizer (L : Set G))
    (hC : centralizer ({z} : Set G) = L ⊔ zpowers z) (hd : Disjoint L (zpowers z))
    (hsp : IsSporadic L .M24) : LocalSetting G L z := by
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by decide)
  have hzL : z ∉ L := by
    intro hz
    have : z ∈ L ⊓ zpowers z := ⟨hz, mem_zpowers z⟩
    rw [disjoint_iff.1 hd] at this
    exact hz1 (mem_bot.1 this)
  have hcomm : ∀ l ∈ L, l * z = z * l := fun l hl =>
    mem_centralizer_iff.1 (hcen (mem_zpowers z)) l hl
  have hmem : ∀ q ∈ centralizer ({z} : Set G), ∃ l ∈ L, q = l ∨ q = l * z := by
    intro q hq
    rw [hC] at hq
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcen hq
    rcases eq_one_or_eq_of_mul_self hzz hb with rfl | rfl
    · exact ⟨a, ha, Or.inl (mul_one a)⟩
    · exact ⟨a, ha, Or.inr rfl⟩
  refine ⟨hz2, hcen, hC, hd, hsp, fun g hg => ?_⟩
  have hy1 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
    calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hy2 : orderOf (g * z * g⁻¹) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [pow_two]; exact hy1) ?_
    intro h
    apply hz1
    have : g * z * g⁻¹ = g * 1 * g⁻¹ := by rw [h]; group
    simpa using this
  obtain ⟨v, hvL, hvv⟩ := exists_mul_self_eq_of_mem hsp hg hy2
  set w : G := g⁻¹ * v * g with hw
  have hww : w * w = z := by
    calc w * w = g⁻¹ * (v * v) * g := by simp only [hw]; group
      _ = z := by rw [hvv]; group
  have hwc : w ∈ centralizer ({z} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc w * z = w * (w * w) := by rw [hww]
      _ = (w * w) * w := by group
      _ = z * w := by rw [hww]
  obtain ⟨l, hl, hwl | hwl⟩ := hmem w hwc
  · apply hzL
    rw [← hww, hwl]
    exact L.mul_mem hl hl
  · apply hzL
    have : z = l * l := by
      calc z = w * w := hww.symm
        _ = (l * z) * (l * z) := by rw [hwl]
        _ = l * l * (z * z) := by
          rw [mul_assoc, ← mul_assoc z l z, ← hcomm l hl]
          group
        _ = l * l := by rw [hzz, mul_one]
    rw [this]
    exact L.mul_mem hl hl

end CFSG.EvenSporadicStandard.M24Std
