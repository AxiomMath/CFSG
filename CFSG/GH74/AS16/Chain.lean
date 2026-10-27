module

public import CFSG.GH74.AS16.Pairs
public import CFSG.GH74.AS16.J1Id
public import CFSG.GH74.AS16.Standard

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG CFSG.Blueprint

@[expose] def LNormal {G : Type} [Group G] (z : G) (L : Subgroup G) : Prop :=
  (L.subgroupOf (centralizer ({z} : Set G))).Normal

structure Ch16Open : Prop where
  thm1624 : ∀ (G : Type) [Group G] [Finite G], Hyp G →
    ∀ (T : Sylow 2 G) (z : G) (L : Subgroup G), Pair T z L → LNormal z L
  lem1631 : ∀ (G : Type) [Group G] [Finite G], Hyp G →
    ∀ (T : Sylow 2 G) (z : G) (L : Subgroup G), Pair T z L → LNormal z L →
      ∀ g : G, ¬ GLS.IsCompIn (centralizer (L : Set G)) (conjugate L g)
  terminal : ∀ (G : Type) [Group G] [Finite G], Hyp G →
    ∀ (T : Sylow 2 G) (z : G) (L : Subgroup G), Pair T z L → LNormal z L →
      ∀ t ∈ centralizer (L : Set G), orderOf t = 2 →
        GLS.IsCompIn (centralizer ({t} : Set G)) L
  sect164 : ∀ (G : Type) [Group G] [Finite G], Hyp G →
    ∀ (T : Sylow 2 G) (z : G) (L : Subgroup G), Pair T z L → LNormal z L → IsStandardSubgroup L →
      ∃ K' : Subgroup G, InDelta0 (centralizer (L : Set G)) L K'
  prop1651 : ∀ (G : Type) [Group G] [Finite G], Hyp G →
    ∀ (T : Sylow 2 G) (z : G) (L : Subgroup G), Pair T z L → LNormal z L → IsStandardSubgroup L →
      ∀ K' : Subgroup G, InDelta0 (centralizer (L : Set G)) L K' → IsBenderComp L →
        JankoLocal z L
  elim : ∀ (G : Type) [Group G] [Finite G], Hyp G →
    ∀ (T : Sylow 2 G) (z : G) (L : Subgroup G), Pair T z L → LNormal z L → IsStandardSubgroup L →
      ∀ K' : Subgroup G, InDelta0 (centralizer (L : Set G)) L K' → ¬ IsBenderComp L → False

theorem Pair.isQuasisimple {G : Type} [Group G] {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : Pair T z L) : IsQuasisimple ↥L :=
  LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe h.isComp.1) h.isComp.2.1

theorem Pair.mem_centralizer {G : Type} [Group G] {T : Sylow 2 G} {z : G} {L : Subgroup G}
    (h : Pair T z L) : z ∈ centralizer (L : Set G) :=
  Subgroup.mem_centralizer_iff.mpr fun _ hl => mem_centralizer_singleton_iff.mp (h.isComp.1 hl)

@[expose] def EvenTypeStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    Assembly.KProper Catalog G → GLS.IsEvenType G → Assembly.evenRank G ≤ 2 →
      ¬ Assembly.Quasithin.quasithinEvenCharacteristic G → NativeSporadic.IsSporadic G .J1

theorem evenType_of_chain (c : Ch16Open) : EvenTypeStatement := by
  intro G _ _ hs hnonab hK hev he hnot
  have hH : Hyp G := ⟨hs, hnonab, hK, hev, he, hnot⟩
  obtain ⟨T, z, L, hp⟩ := exists_pair hH.e1 hH.notEvenChar
  have hN := c.thm1624 G hH T z L hp
  have hS : IsStandardSubgroup L :=
    isStandardSubgroup_of_terminal hp.isQuasisimple hp.orderOf_eq hp.mem_centralizer
      (c.terminal G hH T z L hp hN) (c.lem1631 G hH T z L hp hN)
  obtain ⟨K', hK'⟩ := c.sect164 G hH T z L hp hN hS
  by_cases hB : IsBenderComp L
  · exact isSporadic_J1_of_jankoLocal hs T hp.orderOf_eq hp.mem_sylow hp.central
      (c.prop1651 G hH T z L hp hN hS K' hK' hB)
  · exact (c.elim G hH T z L hp hN hS K' hK' hB).elim

end CFSG.GH74.AS16
