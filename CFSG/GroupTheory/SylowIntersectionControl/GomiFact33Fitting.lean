module

public import CFSG.Adapters.WholeGroupLayer

public section

namespace CFSG.GroupTheory

private theorem fittingSubgroup_le_pPrimeCore_two_of_pCore_eq_bot {H : Type*} [Group H] [Finite H]
    (h2 : CFSG.pCore 2 H = ⊥) : CFSG.fittingSubgroup H ≤ CFSG.pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  refine le_sSup (s := {K : Subgroup H | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}) ⟨hN, ?_⟩
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨T, hT⟩ := hxp.exists_le_sylow
  have hmap := Sylow.map_le_pCore hN hnil 2 T
  rw [h2] at hmap
  have hx1 : x = 1 := Subtype.ext
    (Subgroup.mem_bot.mp (hmap (Subgroup.mem_map_of_mem _ (hT (Subgroup.mem_zpowers x)))))
  rw [hx1, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem layer_ne_bot_and_of_pPrimeCore_le_center {H : Type} [Group H] [Finite H]
    (h2 : CFSG.pCore 2 H = ⊥) (hO : CFSG.pPrimeCore 2 H ≤ Subgroup.center H)
    (heven : Even (Nat.card H)) :
    CFSG.layer H ≠ ⊥ ∧
      Subgroup.centralizer (CFSG.layer H : Set H) = CFSG.pPrimeCore 2 H ∧
      CFSG.pPrimeCore 2 H = Subgroup.center H := by
  have hZF : Subgroup.center H ≤ CFSG.fittingSubgroup H :=
    le_sSup ⟨inferInstance, inferInstance⟩
  have hFO := fittingSubgroup_le_pPrimeCore_two_of_pCore_eq_bot h2
  have hOZ : CFSG.pPrimeCore 2 H = Subgroup.center H := le_antisymm hO (hZF.trans hFO)
  have hCE : Subgroup.centralizer (CFSG.layer H : Set H) ≤ CFSG.pPrimeCore 2 H := by
    refine le_trans ?_ ((CFSG.Adapters.centralizer_generalizedFitting_le_fittingSubgroup H).trans
      hFO)
    rw [Subgroup.le_centralizer_iff, CFSG.generalizedFitting.eq_sup]
    refine sup_le ((hFO.trans hO).trans (Subgroup.center_le_centralizer _)) ?_
    exact Subgroup.le_centralizer_iff.mp le_rfl
  have hC : Subgroup.centralizer (CFSG.layer H : Set H) = CFSG.pPrimeCore 2 H :=
    le_antisymm hCE (hO.trans (Subgroup.center_le_centralizer _))
  refine ⟨fun hE => ?_, hC, hOZ⟩
  have htop : (⊤ : Subgroup H) ≤ CFSG.pPrimeCore 2 H := by
    rw [← hC, hE]
    exact fun x _ => Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [(Subgroup.mem_bot.mp hy), one_mul, mul_one]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card (⊤ : Subgroup H)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le htop) CFSG.pPrimeCore_coprime_card
  rw [Subgroup.card_top, Nat.Prime.coprime_iff_not_dvd Nat.prime_two] at hcop
  exact hcop (even_iff_two_dvd.mp heven)

end CFSG.GroupTheory
