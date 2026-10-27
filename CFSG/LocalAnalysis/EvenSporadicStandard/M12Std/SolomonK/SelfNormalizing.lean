module

public import CFSG.GroupTheory.BurnsideNormalComplement
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.M12Std.SolomonK

open Subgroup

theorem eq_of_normalizer_le {K : Type} [Group K] [Finite K]
    (hO : ∀ N : Subgroup K, N.Normal → Odd (Nat.card N) → N = ⊥)
    {C E : Subgroup K} (hC : C.Normal) (hEC : E ≤ C) (hE2 : IsPGroup 2 E)
    (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hN : ∀ g ∈ C, g ∈ normalizer (E : Set K) → g ∈ E) : C = E := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let E' : Subgroup C := E.subgroupOf C
  have hE'2 : IsPGroup 2 E' := hE2.comap_subtype (K := C)
  obtain ⟨T, hE'T⟩ := hE'2.exists_le_sylow
  have hTE' : E' = T := by
    by_contra hne
    let H : Subgroup (T : Subgroup C) := E'.subgroupOf (T : Subgroup C)
    have hHlt : H < ⊤ := by
      have hHne : H ≠ ⊤ := fun hHtop =>
        hne (le_antisymm hE'T (Subgroup.subgroupOf_eq_top.mp hHtop))
      exact lt_of_le_of_ne le_top hHne
    haveI : Group.IsNilpotent (T : Subgroup C) := T.isPGroup'.isNilpotent
    have hHnorm : H < normalizer H :=
      Group.normalizerCondition_of_isNilpotent (G := (T : Subgroup C)) H hHlt
    obtain ⟨hle, hne'⟩ := lt_iff_le_and_ne.mp hHnorm
    have hnotle : ¬ normalizer H ≤ H := fun hHle => hne' (le_antisymm hle hHle)
    obtain ⟨t, ht_norm, ht_not⟩ := SetLike.not_le_iff_exists.mp hnotle
    have ht_norm' : (t : C) ∈ normalizer (E' : Set C) := by
      have : t ∈ (normalizer E').subgroupOf (T : Subgroup C) := by
        rw [Subgroup.subgroupOf_normalizer_eq hE'T]
        exact ht_norm
      exact Subgroup.mem_subgroupOf.mp this
    have ht_normK : (t : K) ∈ normalizer (E : Set K) := by
      have : (t : C) ∈ (normalizer (E : Set K)).subgroupOf C := by
        rw [Subgroup.subgroupOf_normalizer_eq hEC]
        exact ht_norm'
      exact Subgroup.mem_subgroupOf.mp this
    have htE : (t : K) ∈ E := hN (t : K) (t : C).2 ht_normK
    have htE' : (t : C) ∈ E' := by
      rw [Subgroup.mem_subgroupOf]
      exact htE
    exact ht_not (by rw [Subgroup.mem_subgroupOf]; exact htE')
  have hNT : normalizer (T : Set C) ≤ centralizer (T : Set C) := by
    have hTset : (T : Set C) = (E' : Set C) :=
      congrArg (fun s : Subgroup C => (s : Set C)) hTE'.symm
    rw [hTset]
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcE' : c ∈ E' := by
      have hcK : (c : K) ∈ normalizer (E : Set K) := by
        have : c ∈ (normalizer (E : Set K)).subgroupOf C := by
          rw [Subgroup.subgroupOf_normalizer_eq hEC]
          exact hc
        exact Subgroup.mem_subgroupOf.mp this
      have := hN (c : K) c.2 hcK
      rw [Subgroup.mem_subgroupOf]
      exact this
    exact Subtype.ext (hEab (x : K) (Subgroup.mem_subgroupOf.mp hx)
      (c : K) (Subgroup.mem_subgroupOf.mp hcE'))
  obtain ⟨M, hMnorm, hModd, -, -, hMchar, -, hMsup, -, -, -⟩ :=
    CFSG.GroupTheory.burnside_normal_complement (p := 2) T hNT
  haveI : C.Normal := hC
  haveI : M.Characteristic := hMchar
  have hMK_normal : (M.map C.subtype).Normal := inferInstance
  have hMK_odd : Odd (Nat.card (M.map C.subtype)) := by
    rw [Subgroup.card_subtype C M]
    exact Nat.not_even_iff_odd.mp (by rwa [← even_iff_two_dvd] at hModd)
  have hMK_bot : M.map C.subtype = ⊥ := hO (M.map C.subtype) hMK_normal hMK_odd
  have hMbot : M = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective M C.subtype_injective).mp hMK_bot
  have hTtop : (T : Subgroup C) = ⊤ := by
    have := hMsup
    rw [hMbot, bot_sup_eq] at this
    exact this
  have hE'top : E' = ⊤ := by rw [hTE', hTtop]
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp hE'top) hEC

end CFSG.EvenSporadicStandard.M12Std.SolomonK
