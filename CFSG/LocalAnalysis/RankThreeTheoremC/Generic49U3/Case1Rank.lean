module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem three_le_pRank_of_not_le {p : ℕ} [Fact p.Prime] {S A U : Subgroup G}
    (hexp : ∀ s ∈ S, s ^ p = 1) (hUS : U ≤ S) (hUc : ∀ u ∈ U, ∀ s ∈ S, u * s = s * u)
    (hUcard : Nat.card U = p ^ 2) (hUA : U ≤ A) (hAS : A ≤ S) (hAU : ¬ A ≤ U) :
    3 ≤ CFSG.Open.pRank p A := by
  obtain ⟨a, haA, haU⟩ := IsConcreteLE.not_le_iff_exists.mp hAU
  have haS : a ∈ S := hAS haA
  have ha_p : a ^ p = 1 := hexp a haS
  have ha_ne : a ≠ 1 := fun h => haU (by rw [h]; exact U.one_mem)
  have hord : orderOf a = p := orderOf_eq_prime ha_p ha_ne
  have hzcard : Nat.card (zpowers a) = p ^ 1 := by rw [Nat.card_zpowers, hord, pow_one]
  have hzcard' : Nat.card (zpowers a) = p := by rw [hzcard, pow_one]
  have hdisj : Disjoint U (zpowers a) := by
    rw [disjoint_iff]
    have hdvd : Nat.card ↥(U ⊓ zpowers a) ∣ p := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : U ⊓ zpowers a ≤ zpowers a)
      rwa [hzcard'] at h
    rcases Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ hdvd with h1 | hp
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : U ⊓ zpowers a = zpowers a :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      have haU' : a ∈ U ⊓ zpowers a := by
        rw [heq]
        exact Subgroup.mem_zpowers a
      exact haU (Subgroup.mem_inf.mp haU').1
  have hzab : CFSG.Open.IsElemAbelian p (zpowers a) := by
    refine ⟨inferInstance, ?_⟩
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha_p, one_zpow]
  have hUab : CFSG.Open.IsElemAbelian p U :=
    ⟨isMulCommutative_iff.mpr (fun x y => Subtype.ext (hUc (x : G) x.2 (y : G) (hUS y.2))),
      fun x hx => hexp x (hUS hx)⟩
  have hcomm : ∀ u ∈ U, ∀ b ∈ zpowers a, u * b = b * u := fun u hu b hb =>
    hUc u hu b (Subgroup.zpowers_le.mpr haS hb)
  have key := add_le_pRank_of_commute hUab hzab hUcard hzcard hcomm hdisj hUA
    (Subgroup.zpowers_le.mpr haA)
  exact key

theorem three_le_pRank_of_mul {p : ℕ} [Fact p.Prime] {S A B U : Subgroup G}
    (hexp : ∀ s ∈ S, s ^ p = 1) (hUS : U ≤ S) (hUc : ∀ u ∈ U, ∀ s ∈ S, u * s = s * u)
    (hUcard : Nat.card U = p ^ 2) (hSU : ¬ S ≤ U)
    (hAS : A ≤ S) (hBS : B ≤ S) (hUA : U ≤ A) (hUB : U ≤ B)
    (hAB : ∀ s ∈ S, ∃ a ∈ A, ∃ b ∈ B, s = a * b) :
    3 ≤ CFSG.Open.pRank p A ∨ 3 ≤ CFSG.Open.pRank p B := by
  by_cases hA : A ≤ U
  · by_cases hB : B ≤ U
    · exfalso
      apply hSU
      intro s hs
      obtain ⟨x, hx, y, hy, rfl⟩ := hAB s hs
      exact U.mul_mem (hA hx) (hB hy)
    · exact Or.inr (three_le_pRank_of_not_le hexp hUS hUc hUcard hUB hBS hB)
  · exact Or.inl (three_le_pRank_of_not_le hexp hUS hUc hUcard hUA hAS hA)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
