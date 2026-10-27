module

public import CFSG.CGT.PushingUpLit.EightOneFinalSetup
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.CGT.PushingUpLit

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp

namespace EightOneFinal

variable {G : Type} [Group G] [Finite G]

theorem isSylowOf_of_isSylowOf_inf {S S₀ K N : Subgroup G} (hS : IsSylowOf 2 S K) (hSN : S ≤ N)
    (hS₀ : IsSylowOf 2 S₀ (K ⊓ N)) : IsSylowOf 2 S₀ K := by
  have hS' : IsSylowOf 2 S (K ⊓ N) :=
    EightOneWindow.isSylowOf_of_le_of_le hS (le_inf hS.1 hSN) inf_le_left
  have hS₀card := (ABGLocalTools.isSylowOf_iff.mpr hS₀).card_eq
  have hS'card := (ABGLocalTools.isSylowOf_iff.mpr hS').card_eq
  have hScard := (ABGLocalTools.isSylowOf_iff.mpr hS).card_eq
  have hcard : Nat.card ↥S₀ = 2 ^ (Nat.card ↥K).factorization 2 := by
    rw [hS₀card, ← hS'card, hScard]
  exact ABGLocalTools.isSylowOf_iff.mp (ABGLocalTools.isSylowOf_of_card
    (hS₀.1.trans inf_le_left) hcard)

theorem exists_isSylowOf_normalized {C S₀ : Subgroup G} (hS₀ : IsPGroup 2 S₀)
    (hn : S₀ ≤ Subgroup.normalizer (C : Set G)) :
    ∃ P : Subgroup G, IsSylowOf 2 P C ∧ S₀ ≤ Subgroup.normalizer (P : Set G) := by
  have hCh : C ⊔ S₀ ≤ Subgroup.normalizer (C : Set G) := sup_le Subgroup.le_normalizer hn
  obtain ⟨T, hT, hST⟩ := Nine.exists_isSylowOf_ge hS₀ (le_sup_right : S₀ ≤ C ⊔ S₀)
  refine ⟨T ⊓ C, ABGLocalTools.isSylowOf_iff.mp
    (ABGLocalTools.IsSylowOf.inf_of_le_normalizer (ABGLocalTools.isSylowOf_iff.mpr hT)
      le_sup_left hCh), hST.trans fun t ht => ?_⟩
  have htC : t ∈ Subgroup.normalizer (C : Set G) := hCh (hT.1 ht)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.1 htC x,
    Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer ht) x]

theorem oTwoIn_le_of_isSylowOf {L P : Subgroup G} (hP : IsSylowOf 2 P (centralizerModCore L)) :
    oTwoIn L ≤ P :=
  Nine.le_of_isSylowOf_of_normal hP (ThreeFromEight.isPGroup_oTwoIn L)
    (EightOneWindow.oTwoIn_le_centralizerModCore L)
    ((EightOneWindow.centralizerModCore_le_normalizer L).trans
      (ThreeFromEight.normalizer_le_normalizer_oTwoIn L))

theorem le_normalizer_of_isSylowOf {L P : Subgroup G} (hP : IsSylowOf 2 P (centralizerModCore L)) :
    L ≤ Subgroup.normalizer (P : Set G) := by
  have hO : oTwoIn L ≤ P := oTwoIn_le_of_isSylowOf hP
  have key : ∀ l ∈ L, ∀ p ∈ P, l * p * l⁻¹ ∈ P := by
    intro l hl p hp
    have h1 : p * l * p⁻¹ * l⁻¹ ∈ oTwoIn L := (hP.1 hp).2 l hl
    have h2 : l * p * l⁻¹ * p⁻¹ ∈ P := by
      have e : l * p * l⁻¹ * p⁻¹ = (p * l * p⁻¹ * l⁻¹)⁻¹ := by group
      rw [e]
      exact hO (inv_mem h1)
    have e : l * p * l⁻¹ = (l * p * l⁻¹ * p⁻¹) * p := by group
    rw [e]
    exact mul_mem h2 hp
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key l hl x, fun h => ?_⟩
  have := key l⁻¹ (inv_mem hl) _ h
  simpa [mul_assoc] using this

theorem exists_sylow_data {X N L D : Subgroup G} (hN : IsCharacteristicP 2 ↥N)
    (hX : InClassX ↥X) (hL : BlockAbove X N L) (hD2 : IsPGroup 2 D) (hDN : D ≤ N)
    (hDC : D ≤ centralizerModCore X) :
    ∃ S₀ P : Subgroup G, IsSylowOf 2 S₀ (Subgroup.normalizer (X : Set G) ⊓ N) ∧ D ≤ S₀ ∧
      IsSylowOf 2 P (centralizerModCore L) ∧ S₀ ≤ Subgroup.normalizer (P : Set G) ∧ P ≠ ⊥ ∧
      L ≤ Subgroup.normalizer (P : Set G) := by
  have hDK : D ≤ Subgroup.normalizer (X : Set G) ⊓ N :=
    le_inf (hDC.trans (EightOneWindow.centralizerModCore_le_normalizer X)) hDN
  obtain ⟨S₀, hS₀, hDS₀⟩ := Nine.exists_isSylowOf_ge hD2 hDK
  have hS₀L : S₀ ≤ Subgroup.normalizer (L : Set G) := fun g hg => by
    obtain ⟨hgX, hgN⟩ := Subgroup.mem_inf.1 (hS₀.1 hg)
    exact hL.mem_normalizer hN hX hgN hgX
  obtain ⟨P, hP, hSP⟩ := exists_isSylowOf_normalized hS₀.2.1
    (hS₀L.trans (EightOneWindow.normalizer_le_normalizer_centralizerModCore L))
  refine ⟨S₀, P, hS₀, hDS₀, hP, hSP, fun hP0 => ?_, le_normalizer_of_isSylowOf hP⟩
  have h1 := oTwoIn_le_of_isSylowOf hP
  rw [hP0, le_bot_iff] at h1
  exact ThreeFromEight.oTwoIn_ne_bot_of_isShortGroup hL.inClassX.1 h1

end EightOneFinal

end CFSG.CGT.PushingUpLit
