module

public import CFSG.Foundations.Basic
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG

open Subgroup

private theorem eq_bot_of_subgroupOf_eq_bot {B : Type*} [Group B] {K N : Subgroup B}
    (hKN : K ≤ N) (hK : K.subgroupOf N = ⊥) : K = ⊥ := by
  rw [← map_subgroupOf_eq_of_le hKN, hK, Subgroup.map_bot]

theorem pPrimeCore_eq_bot_of_normal_of_centralizer_le {B : Type*} [Group B] [Finite B]
    {p : ℕ} [Fact p.Prime] {N : Subgroup B} (hNn : N.Normal)
    (hcoreN : pPrimeCore p ↥N = ⊥) (hC : centralizer (N : Set B) ≤ N) :
    pPrimeCore p B = ⊥ := by
  refine (pPrimeCore_eq_bot_iff (p := p) (G := B)).2 fun D hD hcop => ?_
  have hDN : D ⊓ N = ⊥ := by
    have : D.Normal := hD
    have : N.Normal := hNn
    have hn : ((D ⊓ N).subgroupOf N).Normal := (inferInstance : (D ⊓ N).Normal).subgroupOf N
    have hc : Nat.Coprime p (Nat.card ((D ⊓ N).subgroupOf N)) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact hcop.coprime_dvd_right (card_dvd_of_le inf_le_left)
    exact eq_bot_of_subgroupOf_eq_bot inf_le_right
      ((pPrimeCore_eq_bot_iff.1 hcoreN) _ hn hc)
  have hDC : D ≤ centralizer (N : Set B) := by
    rw [← commutator_eq_bot_iff_le_centralizer, eq_bot_iff, ← hDN]
    exact commutator_le_inf D N
  rw [← inf_eq_left.2 (hDC.trans hC)]
  exact hDN

theorem isCharacteristicP_of_normal_of_centralizer_le {B : Type*} [Group B] [Finite B] {p : ℕ}
    [Fact p.Prime] {N : Subgroup B} (hNn : N.Normal) (hN : IsCharacteristicP p ↥N)
    (hC : centralizer (N : Set B) ≤ N) : IsCharacteristicP p B := by
  have hcoreN : pPrimeCore p ↥N = ⊥ := pPrimeCore_eq_bot_of_isCharacteristicP ↥N p hN
  have hcore : pPrimeCore p B = ⊥ :=
    pPrimeCore_eq_bot_of_normal_of_centralizer_le hNn hcoreN hC
  have hlayerN : layer ↥N = ⊥ := layer_eq_bot_of_isCharacteristicP ↥N p hN
  have hlayer : layer B = ⊥ := by
    refine LocalCores.layer_eq_bot_of_forall fun K hK => ?_
    have hKN : K ≤ N := by
      rcases LocalCores.component_normal_subgroup hK hNn with h | h
      · exact h
      · exact ((commutator_eq_bot_iff_le_centralizer).1 h).trans hC
    have hKs : K.subgroupOf N = ⊥ := by
      have h := LocalCores.component_le_layer (LocalCores.component_overgroup hK hKN)
      rwa [hlayerN, le_bot_iff] at h
    have hnt : Nontrivial ↥K := LocalCores.isQuasisimple_nontrivial hK.1
    exact ((nontrivial_iff_ne_bot K).1 hnt) (eq_bot_of_subgroupOf_eq_bot hKN hKs)
  exact isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot B p hcore hlayer

end CFSG
