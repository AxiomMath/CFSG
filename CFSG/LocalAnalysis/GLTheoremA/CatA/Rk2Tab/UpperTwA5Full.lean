module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UnitaryCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperTwA5

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint


theorem rk2_up_twa5_full (hG : CFSG.Open.GriessAllModelsStatement)
    (hSU3 : ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (f d : ℕ),
      Nat.card F = (2 ^ f) ^ 2 → 3 ≤ d → 3 ∣ 2 ^ f + 1 →
        ∀ (C : Subgroup (StatedSU d (2 ^ f) F)) [C.Normal],
          C ≤ Subgroup.center (StatedSU d (2 ^ f) F) →
            CFSG.Open.twoLocalPrimeRank 3 (StatedSU d (2 ^ f) F ⧸ C) ≤ d - 2)
    {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .twA ∧ lab.rank = 5) (hn : 2 ≤ lab.n)
    (hc : Subgroup.center K = ⊥) :
    CFSG.Open.evenRank K ≤ 4 := by
  refine rk2_up_twa5 hK ht hn hc hG ?_
  intro h9
  have h3 : 3 ∣ 2 ^ lab.n + 1 := (by norm_num : 3 ∣ 9).trans h9
  have h := rk2_split_up_twA (r := 3) hG hK ht.1 hn Nat.prime_three (by norm_num) h3 hSU3
  simpa [ht.2] using h

end CFSG.LocalAnalysis.GLTheoremA
