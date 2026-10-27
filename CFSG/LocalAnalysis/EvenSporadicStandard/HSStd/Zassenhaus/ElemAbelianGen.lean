module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Common.Basic

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open

variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
theorem exists_card_sup_zpowers {F K : Subgroup M} (hF : IsElemAbelian 2 F) (hK : K < F) :
    ∃ x ∈ F, x ∉ K ∧ Nat.card ↥(K ⊔ zpowers x) = 2 * Nat.card K := by
  obtain ⟨x, hxF, hxK⟩ := IsConcreteLE.exists_of_lt hK
  have hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := by
    have := hF.1
    rwa [isMulCommutative_iff_of_setLike] at this
  have hx2 : x * x = 1 := by
    have := hF.2 x hxF
    rwa [pow_two] at this
  have hx1 : x ≠ 1 := fun h => hxK (h ▸ K.one_mem)
  have hord : orderOf x = 2 := orderOf_eq_prime (by rwa [pow_two]) hx1
  refine ⟨x, hxF, hxK, ?_⟩
  have hcent : zpowers x ≤ centralizer (K : Set M) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun k hk => hcomm k (hK.le hk) x hxF
  have hdisj : Disjoint K (zpowers x) := by
    rw [Subgroup.disjoint_def]
    intro y hyK hyx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hyx
    have hn : x ^ n = 1 ∨ x ^ n = x := by
      rw [← zpow_mod_orderOf, hord]
      rcases Int.emod_two_eq_zero_or_one n with h | h <;> simp [h]
    rcases hn with h | h
    · exact h
    · exact absurd (h ▸ hyK) hxK
  rw [← Nat.card_congr (mulEquivProdSup hcent hdisj).toEquiv, Nat.card_prod, Nat.card_zpowers,
    hord, mul_comm]

theorem exists_gen_card_sixteen {F : Subgroup M} (hF : IsElemAbelian 2 F) (hcard : Nat.card F = 16)
    {z : M} (hz : z ∈ F) (hz1 : z ≠ 1) :
    ∃ a ∈ F, ∃ b ∈ F, ∃ c ∈ F, a ∉ zpowers z ∧ b ∉ zpowers z ⊔ zpowers a ∧
      c ∉ zpowers z ⊔ zpowers a ⊔ zpowers b ∧
      F = zpowers z ⊔ zpowers a ⊔ zpowers b ⊔ zpowers c := by
  have hz2 : z * z = 1 := by
    have := hF.2 z hz
    rwa [pow_two] at this
  have hord : orderOf z = 2 := orderOf_eq_prime (by rwa [pow_two]) hz1
  have h1 : Nat.card (zpowers z) = 2 := by rw [Nat.card_zpowers, hord]
  have hle1 : zpowers z ≤ F := zpowers_le.2 hz
  have hlt : ∀ {K : Subgroup M}, K ≤ F → Nat.card K < 16 → K < F := by
    intro K hKF hK
    refine lt_of_le_of_ne hKF fun h => ?_
    rw [h, hcard] at hK
    exact lt_irrefl _ hK
  obtain ⟨a, haF, haK, h2⟩ := exists_card_sup_zpowers hF (hlt hle1 (by rw [h1]; norm_num))
  have hle2 : zpowers z ⊔ zpowers a ≤ F := sup_le hle1 (zpowers_le.2 haF)
  rw [h1] at h2
  obtain ⟨b, hbF, hbK, h3⟩ := exists_card_sup_zpowers hF (hlt hle2 (by rw [h2]; norm_num))
  have hle3 : zpowers z ⊔ zpowers a ⊔ zpowers b ≤ F := sup_le hle2 (zpowers_le.2 hbF)
  rw [h2] at h3
  obtain ⟨c, hcF, hcK, h4⟩ := exists_card_sup_zpowers hF (hlt hle3 (by rw [h3]; norm_num))
  have hle4 : zpowers z ⊔ zpowers a ⊔ zpowers b ⊔ zpowers c ≤ F := sup_le hle3 (zpowers_le.2 hcF)
  rw [h3] at h4
  refine ⟨a, haF, b, hbF, c, hcF, haK, hbK, hcK, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hle4 (by rw [h4, hcard])).symm

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
