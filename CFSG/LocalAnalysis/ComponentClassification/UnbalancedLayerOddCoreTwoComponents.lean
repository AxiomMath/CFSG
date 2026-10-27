module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreQuotient
public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalThompson

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG CFSG.LocalCores Subgroup

variable {H : Type*} [Group H] [Finite H]

theorem odd_fixed_core_normalizes_two_components {t : H} (ht : orderOf t = 2) {D : Subgroup H}
    (hDC : D ≤ centralizer ({t} : Set H))
    (hDn : (D.subgroupOf (centralizer ({t} : Set H))).Normal) (hDodd : Odd (Nat.card D)) :
    ∀ L : Subgroup H, IsPComponent 2 L → D ≤ normalizer (L : Set H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htt : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hRodd : Odd (Nat.card (pPrimeCore 2 H)) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  obtain ⟨hDbC, hDbn⟩ := map_normal_centralizer hRodd htt hDC hDn
  have htb := orderOf_mk_eq_two hRodd ht
  have hDbodd : Odd (Nat.card (D.map (QuotientGroup.mk' (pPrimeCore 2 H)))) :=
    hDodd.of_dvd_nat (Subgroup.card_map_dvd D _)
  have hObar : pPrimeCore 2 (H ⧸ pPrimeCore 2 H) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hDbP : ⁅D.map (QuotientGroup.mk' (pPrimeCore 2 H)), pCore 2 (H ⧸ pPrimeCore 2 H)⁆ = ⊥ := by
    have hT : IsPGroup 2 (zpowers (QuotientGroup.mk' (pPrimeCore 2 H) t)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, htb, pow_one])
    rw [← centralizer_zpowers_eq] at hDbC hDbn
    exact SmallLocal.normal_coprime_centralizer_centralizes_prime_core Nat.prime_two hT hDbC
      hDbn (Nat.coprime_two_left.mpr hDbodd)
  have hDbZ : ⁅D.map (QuotientGroup.mk' (pPrimeCore 2 H)),
      (center (layer (H ⧸ pPrimeCore 2 H))).map (layer (H ⧸ pPrimeCore 2 H)).subtype⁆ = ⊥ :=
    le_bot_iff.mp (hDbP ▸ commutator_mono le_rfl
      (center_layer_le_fittingSubgroup.trans (fittingSubgroup_le_pCore_two hObar)))
  have heven : ∀ K : Subgroup (H ⧸ pPrimeCore 2 H), IsComponent K →
      Even (Nat.card (K ⧸ center K)) := by
    intro K hK
    have : IsSimpleGroup (K ⧸ center K) := hK.1.2.1
    exact (SimpleEvenOrder.nonabelian_simple_even hK.1.2.2).1
  have hnorm :=
    odd_fixed_centralizer_normalizes_even_layer_components htb hDbC hDbn hDbodd hDbZ heven
  intro L hL d hd
  obtain ⟨K, hK, -, hLK, -⟩ := id hL
  apply mem_normalizer_of_map hL
  rw [hLK]
  exact hnorm K hK (mem_map_of_mem _ hd)

end CFSG.ComponentClassification.UnbalancedLayer
