module

public import CFSG.Open.GorensteinWalterLBalanceMilestoneDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.ComponentClassification.LBalance

open CFSG.Open

variable {G : Type*} [Group G]

theorem primeCore_eq_map (p : ℕ) (Y : Subgroup G) :
    lBalancePrimeCore p Y = (pPrimeCore p Y).map Y.subtype := by
  apply le_antisymm
  · apply sSup_le
    intro N hN
    have hcop : Nat.Coprime p (Nat.card (N.subgroupOf Y)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.1).toEquiv]
      exact hN.2.2
    have hle : N.subgroupOf Y ≤ pPrimeCore p Y := le_sSup ⟨hN.2.1, hcop⟩
    simpa only [Subgroup.map_subgroupOf_eq_of_le hN.1] using
      (Subgroup.map_mono (f := Y.subtype) hle)
  · rw [pPrimeCore, sSup_eq_iSup, Subgroup.map_iSup]
    apply iSup_le
    intro N
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro hN
    apply le_sSup
    refine ⟨Subgroup.map_subtype_le N, ?_, ?_⟩
    · change ((N.map Y.subtype).comap Y.subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective Y.subtype_injective]
      exact hN.1
    · simpa only [Subgroup.card_subtype] using hN.2

theorem primeCore_le (p : ℕ) (Y : Subgroup G) : lBalancePrimeCore p Y ≤ Y := by
  rw [primeCore_eq_map]
  exact Subgroup.map_subtype_le _

theorem primeCore_subgroupOf_eq (p : ℕ) (Y : Subgroup G) :
    (lBalancePrimeCore p Y).subgroupOf Y = pPrimeCore p Y := by
  rw [primeCore_eq_map]
  exact Subgroup.comap_map_eq_self_of_injective Y.subtype_injective _

instance primeCore_normal (p : ℕ) (Y : Subgroup G) :
    ((lBalancePrimeCore p Y).subgroupOf Y).Normal := by
  rw [primeCore_subgroupOf_eq]
  infer_instance

theorem primeCore_coprime (p : ℕ) [Fact p.Prime] [Finite G] (Y : Subgroup G) :
    Nat.Coprime p (Nat.card (lBalancePrimeCore p Y)) := by
  rw [primeCore_eq_map, Subgroup.card_subtype]
  exact pPrimeCore_coprime_card

theorem primeCore_top (p : ℕ) : lBalancePrimeCore p (⊤ : Subgroup G) = pPrimeCore p G := by
  rw [primeCore_eq_map]
  exact pPrimeCore_map_iso p Subgroup.topEquiv

theorem primeCore_quotient_corefree (p : ℕ) [Fact p.Prime] [Finite G] (Y : Subgroup G) :
    pPrimeCore p (Y ⧸ (lBalancePrimeCore p Y).subgroupOf Y) = ⊥ := by
  let e : (Y ⧸ (lBalancePrimeCore p Y).subgroupOf Y) ≃* (Y ⧸ pPrimeCore p Y) :=
    QuotientGroup.congr _ _ (MulEquiv.refl Y) (by
      change ((lBalancePrimeCore p Y).subgroupOf Y).map (MonoidHom.id Y) =
        pPrimeCore p Y
      rw [Subgroup.map_id, primeCore_subgroupOf_eq])
  have heq := pPrimeCore_map_iso p e
  rw [pPrimeCore_quotient_pPrimeCore_eq_bot] at heq
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp heq

theorem primeCore_normal_intersection (p : ℕ) [Fact p.Prime] [Finite G]
    (Y : Subgroup G) [Y.Normal] :
    lBalancePrimeCore p Y = Y ⊓ pPrimeCore p G := by
  rw [primeCore_eq_map]
  let : (pPrimeCore p Y).Characteristic := inferInstance
  have hle : (pPrimeCore p Y).map Y.subtype ≤ pPrimeCore p G := by
    apply le_sSup
    exact ⟨ConjAct.normal_of_characteristic_of_normal,
      by simpa only [Subgroup.card_subtype] using
        (pPrimeCore_coprime_card (p := p) (G := Y))⟩
  apply le_antisymm (le_inf (Subgroup.map_subtype_le _) hle)
  rw [inf_comm, ← Subgroup.subgroupOf_map_subtype]
  apply Subgroup.map_mono
  apply le_sSup
  refine ⟨Subgroup.Normal.comap inferInstance Y.subtype, ?_⟩
  have hcard : Nat.card ((pPrimeCore p G).subgroupOf Y) =
      Nat.card (pPrimeCore p G ⊓ Y : Subgroup G) := by
    rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_subtype]
  rw [hcard]
  exact (pPrimeCore_coprime_card (p := p) (G := G)).of_dvd_right
    (Subgroup.card_dvd_of_le inf_le_left)

end CFSG.ComponentClassification.LBalance
