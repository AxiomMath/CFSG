module

public import CFSG.Foundations.Basic
import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW

open Subgroup CFSG

private theorem pPrimeCore_normal_eq_bot {D : Type} [Group D] [Finite D]
    (hO : pPrimeCore 2 D = ⊥) (M : Subgroup D) [M.Normal] : pPrimeCore 2 ↥M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC : ((pPrimeCore 2 ↥M).map M.subtype).Normal := inferInstance
  have hcop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 ↥M).map M.subtype)) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact pPrimeCore_coprime_card
  have hle : (pPrimeCore 2 ↥M).map M.subtype ≤ pPrimeCore 2 D := le_sSup ⟨hC, hcop⟩
  rw [hO, le_bot_iff, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at hle
  exact le_bot_iff.mp hle

theorem hat_pLayer_equiv_layer {Y : Type} [Group Y] [Finite Y] :
    Nonempty (↥(pLayer Y 2) ⧸ pPrimeCore 2 ↥(pLayer Y 2) ≃* ↥(layer (Y ⧸ pPrimeCore 2 Y))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap : (pLayer Y 2).map (QuotientGroup.mk' (pPrimeCore 2 Y)) =
      layer (Y ⧸ pPrimeCore 2 Y) :=
    CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient
  have hmem : ∀ x : ↥(pLayer Y 2),
      QuotientGroup.mk' (pPrimeCore 2 Y) (x : Y) ∈ layer (Y ⧸ pPrimeCore 2 Y) := fun x => by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ x.2
  let f : ↥(pLayer Y 2) →* ↥(layer (Y ⧸ pPrimeCore 2 Y)) :=
    ((QuotientGroup.mk' (pPrimeCore 2 Y)).comp (pLayer Y 2).subtype).codRestrict _ hmem
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy' : y ∈ (pLayer Y 2).map (QuotientGroup.mk' (pPrimeCore 2 Y)) := by
      rw [hmap]
      exact hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy'
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have : (layer (Y ⧸ pPrimeCore 2 Y)).Characteristic := CFSG.LocalCores.layer_characteristic
  have hbotE : pPrimeCore 2 ↥(layer (Y ⧸ pPrimeCore 2 Y)) = ⊥ :=
    pPrimeCore_normal_eq_bot (CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 2) _
  have hker : f.ker = pPrimeCore 2 ↥(pLayer Y 2) := by
    apply le_antisymm
    · have hcop : Nat.Coprime 2 (Nat.card f.ker) := by
        have hle : f.ker.map (pLayer Y 2).subtype ≤ pPrimeCore 2 Y := by
          rintro _ ⟨x, hx, rfl⟩
          exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
        have h1 : Nat.card (f.ker.map (pLayer Y 2).subtype) ∣ Nat.card (pPrimeCore 2 Y) :=
          Subgroup.card_dvd_of_le hle
        rw [Subgroup.card_map_of_injective (pLayer Y 2).subtype_injective] at h1
        exact Nat.Coprime.of_dvd_right h1 pPrimeCore_coprime_card
      exact le_sSup ⟨inferInstance, hcop⟩
    · intro x hx
      have h1 : f x ∈ pPrimeCore 2 ↥(layer (Y ⧸ pPrimeCore 2 Y)) :=
        CFSG.map_pPrimeCore_le f hsurj ⟨x, hx, rfl⟩
      rw [hbotE] at h1
      exact h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hsurj)⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87.L29GW
