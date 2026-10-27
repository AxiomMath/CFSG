module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxPumpSporBasic
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.Monster.SteinbergMSporadicOddCoreFree
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup CFSG.Blueprint

theorem not_two_pow_dvd_of_le_monsterOrder {m : ℕ} (hm7 : 7 ≤ m)
    (hm : m.factorial / 2 ≤ Open.monsterOrder) : ¬ 2 ^ 41 ∣ m.factorial / 2 := by
  have hbig : Open.monsterOrder < (44 : ℕ).factorial / 2 := by
    unfold Open.monsterOrder
    decide
  have hm44 : m < 44 := by
    by_contra hc
    have h1 : (44 : ℕ).factorial / 2 ≤ m.factorial / 2 :=
      Nat.div_le_div_right (Nat.factorial_le (by omega))
    omega
  have key : ∀ k < 44, 7 ≤ k → ¬ 2 ^ 41 ∣ k.factorial / 2 := by decide
  exact key m hm44 hm7

theorem altPumpSpor_M :
    AltPumpSporClauseFor .M :=
  altPumpSporClauseFor_of_comps CatalogueU.sporadicOddCoreFree_M
    (fun G _ _ hs _ ⟨e⟩ t ht B hB => by
      obtain ⟨E⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
      have hG : Nat.card G = Open.monsterOrder := by
        rw [Nat.card_congr E.toEquiv, YGroups.Y443.natCard_Gmat_eq_monsterOrder]
      obtain ⟨h41, -⟩ := CatLeafProof.monsterLocalComponentsInput G hs ⟨e⟩ t ht B hB
      refine noOddAltBelow_of_card_quotient_center fun m _ hm7 hmN h => ?_
      rw [h] at h41
      exact not_two_pow_dvd_of_le_monsterOrder hm7 (hG ▸ hmN) h41)
    (fun G _ _ hs _ hG α _ hα => absurd (CatLeafProof.monsterInnerInput G hs hG α) hα)

end CFSG.ComponentClassification.SolMax
