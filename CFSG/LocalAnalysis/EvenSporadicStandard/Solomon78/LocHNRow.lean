module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.HNCenter
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.AutModelTransfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.G6Words

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.EvenSporadicStandard.TwoHS CFSG.Blueprint.NativeSporadic

@[expose] def HNOvergroupFact : Prop :=
  ∀ (Y : Type) [Group Y], IsSporadic Y .HN → ∀ (u : Y) (K : Subgroup Y), orderOf u = 2 →
    (∀ k ∈ K, k * u = u * k) → Nat.card K = 88704000 →
      ∀ X : Subgroup Y, K ≤ X → X ≤ centralizer ({u} : Set Y) ∨ X = ⊤

@[expose] def HNPair (G : Type) [Group G] (L K : Subgroup G) (u : G) : Prop :=
  u ∈ L ∧ orderOf u = 2 ∧ K ≤ L ∧ (∀ k ∈ K, k * u = u * k) ∧ Nat.card K = 88704000

theorem hn_overgroups_of_fact (hfact : HNOvergroupFact) {G : Type} [Group G] {L K : Subgroup G}
    {u : G} (hL : IsSporadic L .HN) (hu : u ∈ L) (hu2 : orderOf u = 2) (hKL : K ≤ L)
    (hKu : ∀ k ∈ K, k * u = u * k) (hcard : Nat.card K = 88704000) :
    ∀ X : Subgroup G, K ≤ X → X ≤ L → X ≤ L ⊓ centralizer ({u} : Set G) ∨ X = L := by
  intro X hKX hXL
  have h := hfact (↥L) hL ⟨u, hu⟩ (K.subgroupOf L) (by rw [Subgroup.orderOf_mk]; exact hu2)
    (fun k hk => Subtype.ext (hKu k (mem_subgroupOf.1 hk)))
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv]; exact hcard)
    (X.subgroupOf L) (fun x hx => mem_subgroupOf.2 (hKX (mem_subgroupOf.1 hx)))
  rcases h with h | h
  · left
    intro x hx
    refine ⟨hXL hx, mem_centralizer_singleton_iff.2 ?_⟩
    have := mem_centralizer_singleton_iff.1 (h (mem_subgroupOf.2 hx : (⟨x, hXL hx⟩ : ↥L) ∈ _))
    exact congrArg Subtype.val this
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hXL h

theorem hn_isSimpleGroup_of_isSporadic {X : Type} [Group X]
    (h : IsSporadic X .HN) : IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  have e' : X ≃* CFSG.Blueprint.NativeSporadic.HN := e
  exact @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.HN.isSimpleGroup_HN e'

theorem hn_exists_not_commute {X : Type} [Group X]
    (h : IsSporadic X .HN) : ∃ a b : X, a * b ≠ b * a := by
  have hs := hn_isSimpleGroup_of_isSporadic h
  by_contra hc
  push Not at hc
  let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
  have hp := IsSimpleGroup.prime_card (α := X)
  obtain ⟨e⟩ := h
  have e' : X ≃* CFSG.Blueprint.NativeSporadic.HN := e
  have hcX : Nat.card X = 273030912000000 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.HN.card_HN
  rw [hcX] at hp
  norm_num at hp

theorem hn_outTwo_of_isSporadic
    {Y : Type} [Group Y] (h : IsSporadic Y .HN) : OutTwo Y := by
  obtain ⟨e⟩ := hn_equiv_P h
  exact @OutTwo.of_mulEquiv ↥hnP Y _ _ e.symm (hn_autRowData centerInvolutions_jh).outTwo

end CFSG.EvenSporadicStandard.Solomon78
