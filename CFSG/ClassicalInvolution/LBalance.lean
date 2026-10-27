module

public import CFSG.LocalAnalysis.ComponentClassification.LocalBFailureTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayerTransport

public section

namespace CFSG.ClassicalInvolution

open scoped commutatorElement

@[expose] def L2PrimeBalance : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (A : Subgroup X), IsPGroup 2 A →
    (CFSG.pLayer (Subgroup.centralizer (A : Set X)) 2).map
        (Subgroup.centralizer (A : Set X)).subtype ≤ CFSG.pLayer X 2

variable {G : Type} [Group G] [Finite G]

theorem layer_le_of_centralizer_eq_bot (F : Subgroup G) [F.Normal]
    (hC : Subgroup.centralizer (F : Set G) = ⊥) : CFSG.layer G ≤ F := by
  refine sSup_le fun K hK => ?_
  rcases CFSG.LocalCores.component_normal_subgroup hK (inferInstance : F.Normal) with h | h
  · exact h
  · have hKC : K ≤ Subgroup.centralizer (F : Set G) := by
      intro k hk
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have : ⁅k, f⁆ = 1 := by
        have hmem := Subgroup.commutator_mem_commutator hk hf
        rw [h] at hmem
        exact hmem
      rw [commutatorElement_eq_one_iff_mul_comm] at this
      exact this.symm
    rw [hC] at hKC
    exact hKC.trans bot_le

theorem oddCore_eq_bot_of_centralizer_eq_bot (F : Subgroup G) [F.Normal] [IsSimpleGroup F]
    (hFeven : Even (Nat.card F)) (hC : Subgroup.centralizer (F : Set G) = ⊥) :
    CFSG.Open.componentClassificationOddCore G = ⊥ := by
  set O := CFSG.Open.componentClassificationOddCore G
  have hOodd : Odd (Nat.card O) := ComponentClassification.OddCore.odd_card G
  have hinf : O ⊓ F = ⊥ := by
    have hn : ((O ⊓ F).subgroupOf F).Normal := by
      have : (O ⊓ F).Normal := Subgroup.normal_inf_normal O F
      exact Subgroup.normal_subgroupOf
    rcases hn.eq_bot_or_eq_top with h | h
    · exact (Subgroup.subgroupOf_eq_bot.mp h).eq_bot_of_le inf_le_right
    · exfalso
      rw [Subgroup.subgroupOf_eq_top] at h
      have hFO : F ≤ O := h.trans inf_le_left
      have hdvd : Nat.card F ∣ Nat.card O := Subgroup.card_dvd_of_le hFO
      exact (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hOodd hdvd)) hFeven
  have hOC : O ≤ Subgroup.centralizer (F : Set G) := by
    intro o ho
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    have hmem : ⁅o, f⁆ ∈ O ⊓ F :=
      (Subgroup.commutator_le_inf O F) (Subgroup.commutator_mem_commutator ho hf)
    rw [hinf, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem.symm
  exact le_bot_iff.mp (hC ▸ hOC)

theorem twoComponent_le_of_l2PrimeBalance (h : L2PrimeBalance) (F : Subgroup G) [F.Normal]
    [IsSimpleGroup F] (hFeven : Even (Nat.card F)) (hC : Subgroup.centralizer (F : Set G) = ⊥)
    (A : Subgroup G) (hA : IsPGroup 2 A) (L : Subgroup (Subgroup.centralizer (A : Set G)))
    (hL : CFSG.IsPComponent 2 L) : L.map (Subgroup.centralizer (A : Set G)).subtype ≤ F := by
  have h1 : L.map (Subgroup.centralizer (A : Set G)).subtype ≤ CFSG.pLayer G 2 :=
    (Subgroup.map_mono (le_sSup hL)).trans (h G A hA)
  rw [ComponentClassification.LocalBFailure.pLayer_two_eq_twoLayer,
    ComponentClassification.TwoLayerTransport.eq_layer_of_corefree
      (oddCore_eq_bot_of_centralizer_eq_bot F hFeven hC),
    ← CFSG.layer_eq_componentClassification] at h1
  exact h1.trans (layer_le_of_centralizer_eq_bot F hC)

end CFSG.ClassicalInvolution
