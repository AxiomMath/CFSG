module

public import Mathlib.Data.Set.Card
public import Mathlib.Data.Nat.Prime.Defs

import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Sym.Sym2.Init
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.GroupTheory

theorem disjoint_sdiff_one_of_ne_of_card_prime {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {F F' : Subgroup G} (hF : Nat.card F = p) (hF' : Nat.card F' = p)
    (hne : F ≠ F') : Disjoint ((F : Set G) \ {1}) ((F' : Set G) \ {1}) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [Set.mem_diff, Set.mem_singleton_iff] at hx hx'
  obtain ⟨hxF, hx1⟩ := hx
  obtain ⟨hxF', -⟩ := hx'
  have hgen : ∀ {K : Subgroup G}, Nat.card K = p → x ∈ K → Subgroup.zpowers x = K := by
    intro K hK hxK
    have hle : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.mpr hxK
    have hdvd : orderOf x ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hxK
    rw [hK] at hdvd
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exfalso
      exact hx1 (orderOf_eq_one_iff.mp h1)
    · exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, h1, hK])
  exact hne ((hgen hF hxF).symm.trans (hgen hF' hxF'))

theorem ncard_subgroups_card_prime_mul_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (A : Subgroup G) :
    {F : Subgroup G | F ≤ A ∧ Nat.card F = p}.ncard * (p - 1) ≤ Nat.card A - 1 := by
  classical
  let : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G))
      (fun H K h => Subgroup.ext (Set.ext_iff.mp h))
  set S : Set (Subgroup G) := {F | F ≤ A ∧ Nat.card F = p} with hS
  have hmem : ∀ {F : Subgroup G}, F ∈ S ↔ F ≤ A ∧ Nat.card F = p := by
    intro F
    rw [hS, Set.mem_setOf_eq]
  let f : Subgroup G → Set G := fun F => (F : Set G) \ {1}
  have hcardf : ∀ F ∈ S, (f F).ncard = p - 1 := by
    intro F hF
    have hFp : Nat.card F = p := (hmem.mp hF).2
    have hcoe : (F : Set G).ncard = Nat.card F :=
      (Nat.card_coe_set_eq (F : Set G)).symm
    change ((F : Set G) \ {1}).ncard = p - 1
    rw [Set.ncard_diff_singleton_of_mem F.one_mem, hcoe, hFp]
  have hdisj : S.PairwiseDisjoint f := by
    intro F hF F' hF' hne
    exact disjoint_sdiff_one_of_ne_of_card_prime hp (hmem.mp hF).2 (hmem.mp hF').2 hne
  have hfin : ∀ F ∈ S, (f F).Finite := fun F _ => Set.toFinite _
  have hcount := Set.Finite.ncard_biUnion (Set.toFinite S) hfin hdisj
  have hsum : (∑ᶠ F ∈ S, (f F).ncard) = S.ncard * (p - 1) := by
    calc (∑ᶠ F ∈ S, (f F).ncard) = ∑ᶠ F ∈ S, (p - 1) :=
          finsum_mem_congr rfl fun F hF => hcardf F hF
      _ = S.ncard * (p - 1) := by
          rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite S), Finset.sum_const,
            smul_eq_mul, ← Set.ncard_eq_toFinset_card S (Set.toFinite S)]
  have hsub : (⋃ F ∈ S, f F) ⊆ (A : Set G) \ {1} := by
    intro x hx
    obtain ⟨F, hF, hxF⟩ := Set.mem_iUnion₂.mp hx
    simp only [f, Set.mem_diff, Set.mem_singleton_iff] at hxF
    exact ⟨(hmem.mp hF).1 hxF.1, hxF.2⟩
  have hAle : (⋃ F ∈ S, f F).ncard ≤ ((A : Set G) \ {1}).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have hA : ((A : Set G) \ {1}).ncard = Nat.card A - 1 := by
    have hcoe : (A : Set G).ncard = Nat.card A :=
      (Nat.card_coe_set_eq (A : Set G)).symm
    rw [Set.ncard_diff_singleton_of_mem A.one_mem, hcoe]
  rw [hcount, hsum, hA] at hAle
  simpa only [hS] using hAle

end CFSG.GroupTheory

end
