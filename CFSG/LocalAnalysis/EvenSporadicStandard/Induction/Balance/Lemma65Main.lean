module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Adapt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Defs
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.Lemma65Even

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic

theorem exists_subgroup_of_subtype {G : Type} [Group G] (H : Subgroup G) (N' : Subgroup ↥H)
    [N'.Normal] (hi : N'.index = 2) (e : ↥H) (he : e ∉ N') :
    ∃ N₀ : Subgroup G, N₀ ≤ H ∧ (N₀.subgroupOf H).Normal ∧ N₀.relIndex H = 2 ∧ (e : G) ∉ N₀ := by
  have hsub : (N'.map H.subtype).subgroupOf H = N' :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective N'
  refine ⟨N'.map H.subtype, Subgroup.map_subtype_le N', ?_, ?_, ?_⟩
  · rw [hsub]
    infer_instance
  · rw [Subgroup.relIndex, hsub]
    exact hi
  · rintro ⟨x, hx, hxe⟩
    exact he (by rw [← Subtype.ext hxe]; exact hx)

theorem sol78Lemma65KP_of_inputs (hU : Sol78Lemma65Uniq) (hM23 : M23Facts)
    (hRec : M24Recognition) (hMult : M24Multiplier) : Sol78Lemma65KP := by
  intro G _ _ hK H E H₁ e hHtop hEH hEN hab hcard hcent he hord horb hC hH₁ hdisj hN hiso
  obtain ⟨φ⟩ := hiso
  have := hM23.1
  have hsimple : IsSimpleGroup (H₁ ⧸ E.subgroupOf H₁) := φ.isSimpleGroup
  have hcard₁ : Nat.card (H₁ ⧸ E.subgroupOf H₁) = 10200960 :=
    (Nat.card_congr φ.toEquiv).trans hM23.2
  have hS := setting65_of_subgroup hEH hH₁ hEN hN hab hcard hcent he hord horb hC hdisj hsimple
    hcard₁
  have hM24 : Nonempty (H ⧸ E.subgroupOf H ≃* Carrier .M24) :=
    hRec hK hHtop hEH hS.isSimpleGroup_quot hS.card_quot
  refine ⟨hM24, ?_, hU G H E H₁ e hEH hEN hab hcard hcent he hord horb hC hH₁ hdisj hN ⟨φ⟩ hM24⟩
  obtain ⟨N', hNn, hNi, heN⟩ := hS.exists_index_two (hMult _ hM24)
  exact exists_subgroup_of_subtype H N' hNi _ heN

end CFSG.EvenSporadicStandard.Induction.Balance
