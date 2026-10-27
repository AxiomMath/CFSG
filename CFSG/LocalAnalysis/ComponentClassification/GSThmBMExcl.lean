module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrLayerStandard
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofMonster
public import CFSG.YGroups.Y443.Tri.Finiteness

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial

theorem commutingBlockOvergroupExclusion_M :
    UnbalancedCorr.CommutingBlockOvergroupExclusion NativeSporadic.M := by
  intro G _ _ J hq heven hJ hΔ L hL hML hLH
  classical
  rintro ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hodd, hπKq, hcomm, hloc, -⟩ :=
    escaping_block_quotient_inherits_local_components hq heven hJ hΔ hL hML hLH
  obtain ⟨K₁, hK₁, K₂, hK₂, hne⟩ := hΔ
  have hS : IsSimpleGroup (↥L ⧸ center ↥L) :=
    ((AssemblyBPredicates.isQuasisimple_iff_native _).mp hL).2.1
  obtain ⟨eG⟩ := RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  have hcard : Nat.card (↥L ⧸ center ↥L) = Open.monsterOrder := by
    rw [Nat.card_congr eG.toEquiv, YGroups.Y443.natCard_Gmat_eq_monsterOrder]
  have hinv : ∀ K ∈ block J, ∃ t : L, (t : G) ∈ K ∧ orderOf t = 2 := by
    intro K hK
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := centerQuotientImage L K) 2
      (even_iff_two_dvd.1 (hπKq K hK).2)
    obtain ⟨t, htK, ht2, -⟩ := exists_involution_lift_of_odd_center hodd u.2
      (by rw [Subgroup.orderOf_coe, hu])
    exact ⟨t, htK, ht2⟩
  have h41 : ∀ Ka ∈ block J, ∀ Kb ∈ block J, Ka ≠ Kb →
      2 ^ 41 ∣ Nat.card (centerQuotientImage L Ka ⧸ center (centerQuotientImage L Ka)) := by
    intro Ka hKa Kb hKb hab
    obtain ⟨t, htK, ht2⟩ := hinv Kb hKb
    obtain ⟨hπt, hcompK⟩ := hloc Ka hKa Kb hKb hab t htK ht2
    have hB := (isComponentOf_iff_isComponent_subgroupOf hcompK.1).1 hcompK
    have h := (CatLeafProof.monsterLocalComponentsInput (↥L ⧸ center ↥L) hS ⟨e⟩ _ hπt _ hB).1
    let φ := Subgroup.subgroupOfEquivOfLe hcompK.1
    rwa [(Nat.card_congr (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).toEquiv)] at h
  have hmul := card_quotient_center_mul_dvd (hcomm K₁ hK₁ K₂ hK₂ hne).2
    (bot_le : (⊥ : Subgroup (L ⧸ center L)) ≤ center (L ⧸ center L))
  rw [Nat.card_congr QuotientGroup.quotientBot.toEquiv, hcard] at hmul
  have h82 := (Nat.mul_dvd_mul (h41 K₁ hK₁ K₂ hK₂ hne) (h41 K₂ hK₂ K₁ hK₁ hne.symm)).trans hmul
  norm_num [Open.monsterOrder] at h82

end CFSG.ComponentClassification.GSThmB
