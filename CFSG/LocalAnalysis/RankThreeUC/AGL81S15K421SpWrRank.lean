module

public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421SpWrProof

theorem three_le_pRank_regularWreathProduct {D Q : Type} [Group D] [Finite D] [Group Q] [Finite Q]
    (hD : 3 ∣ Nat.card D) (hQ : Nat.card Q = 3) :
    3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (D ≀ᵣ Q)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := D) 3 hD
  have hg3 : g ^ 3 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [hg] at this
  have hCcard : Nat.card (Subgroup.zpowers g) = 3 := by rw [Nat.card_zpowers, hg]
  have hCpow : ∀ c : Subgroup.zpowers g, c ^ 3 = 1 := by
    intro c
    apply Subtype.ext
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 c.2
    have : (c : D) ^ 3 = 1 := by
      rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
    simpa using this
  have hCcomm : ∀ c d : Subgroup.zpowers g, c * d = d * c := by
    rintro ⟨c, m, rfl⟩ ⟨d, n, rfl⟩
    apply Subtype.ext
    show g ^ m * g ^ n = g ^ n * g ^ m
    rw [← zpow_add, ← zpow_add, add_comm]
  let f : (Q → Subgroup.zpowers g) →* D ≀ᵣ Q :=
    { toFun := fun a => ⟨fun q => (a q : D), 1⟩
      map_one' := by ext <;> simp
      map_mul' := fun a b => by
        ext q
        · simp [RegularWreathProduct.mul_def]
        · simp [RegularWreathProduct.mul_def] }
  have hf : Function.Injective f := by
    intro a b hab
    funext q
    apply Subtype.ext
    exact congrFun (congrArg RegularWreathProduct.left hab) q
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (k := 3) (by norm_num)
    (fun a b => funext fun q => hCcomm (a q) (b q))
    (fun a => funext fun q => hCpow (a q)) ?_ f hf (H := ⊤) le_top
  rw [Nat.card_fun, hCcard, hQ]

theorem three_le_pRank_wreath_zmod {k : ℕ} (hk : 1 ≤ k) :
    3 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (Multiplicative (ZMod (3 ^ k)) ≀ᵣ Multiplicative (ZMod 3))) := by
  refine three_le_pRank_regularWreathProduct ?_ ?_
  · rw [Nat.card_eq_fintype_card]
    have : Fintype.card (Multiplicative (ZMod (3 ^ k))) = 3 ^ k := by simp
    rw [this]
    exact dvd_pow_self 3 (by omega)
  · rw [Nat.card_eq_fintype_card]
    simp

theorem three_le_pRank_of_mulEquiv_wreath_zmod {k : ℕ} (hk : 1 ≤ k) {X : Type} [Group X] [Finite X]
    {P : Subgroup X}
    (e : ↥P ≃* Multiplicative (ZMod (3 ^ k)) ≀ᵣ Multiplicative (ZMod 3)) :
    3 ≤ CFSG.Open.pRank 3 P := by
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup,
    CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact three_le_pRank_wreath_zmod hk

end K421SpWrProof

end CFSG.LocalAnalysis.RankThreeUC.S15
