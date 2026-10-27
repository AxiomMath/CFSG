module

public import Mathlib.GroupTheory.SpecificGroups.ZGroup
import CFSG.FeitThompson.Local.FreeComplementNoFrobeniusSubgroup
import CFSG.FeitThompson.Local.OddNoncyclicNormalPlane
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
import CFSG.FeitThompson.OddOrder.FullExponentSubgroupCyclicSylow
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import CFSG.FeitThompson.Foundations.CentralSeriesDerivedLength

open Pointwise

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {L : Type*} [Group L] {p : ℕ}

theorem isCyclic_of_isPGroup_of_free_complement [Finite L] (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) [Group.IsSolvable H]
    (hfree : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hp : p.Prime) {P : Subgroup E} (hPp : IsPGroup p P) : IsCyclic P := by
  have := Fact.mk hp
  by_contra hnc
  have hHnt : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).2 hH
  have hcop : Nat.Coprime (Nat.card H) (Nat.card E) :=
    coprime_card_of_fixedPointFree (φ := (MulAut.conjNormal (H := H)).comp E.subtype)
      (fun u hu => fixedPointFree_conjNormal_of_inf_centralizer_eq_bot
        (hfree (u : L) u.2 (by simpa using hu)))
  have hPnt : Nontrivial P := by
    rcases subsingleton_or_nontrivial (P : Type _) with h | h
    · exact absurd isCyclic_of_subsingleton hnc
    · exact h
  obtain ⟨n, hn⟩ := hPp.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact absurd (Nat.card_eq_one_iff_unique.mp hn).1 (not_subsingleton _)
  have hpE : p ∣ Nat.card E :=
    (hn ▸ dvd_pow_self p hn0).trans (Subgroup.card_subgroup_dvd_card P)
  have hpH : ¬ p ∣ Nat.card H := fun h => hp.one_lt.ne' (Nat.eq_one_of_dvd_one
    (hcop ▸ Nat.dvd_gcd h hpE))
  have hpodd : Odd p :=
    Odd.of_dvd_nat (Odd.of_dvd_nat hodd (Subgroup.card_subgroup_dvd_card E)) hpE
  have hnc' : ¬ IsCyclic ((⊤ : Subgroup P)) := fun h =>
    hnc (isCyclic_of_surjective (⊤ : Subgroup P).subtype fun x => ⟨⟨x, trivial⟩, rfl⟩)
  obtain ⟨A, -, -, ⟨eA⟩⟩ :=
    exists_normal_le_mulEquiv_zmod_prod_of_not_isCyclic_of_isPGroup hp hpodd hPp ⊤ hnc'
  let ρ : A →* MulAut H :=
    (MulAut.conjNormal (H := H)).comp (E.subtype.comp (P.subtype.comp A.subtype))
  have key := iSup_autFixedSubgroup_eq_top_of_mulEquiv eA hp ρ hpH
  have hbot : ∀ a : A, a ≠ 1 → autFixedSubgroup (ρ a) = ⊥ := by
    intro a ha
    have ha' : (((a : P) : E) : L) ≠ 1 := by simpa using ha
    have hff := fixedPointFree_conjNormal_of_inf_centralizer_eq_bot
      (H := H) (hfree _ (((a : P) : E)).2 ha')
    exact (Subgroup.eq_bot_iff_forall _).2 fun v hv => hff v (mem_autFixedSubgroup.mp hv)
  have hle : (⨆ (a : A) (_ : a ≠ 1), autFixedSubgroup (ρ a)) ≤ ⊥ :=
    iSup₂_le fun a ha => (hbot a ha).le
  rw [key] at hle
  obtain ⟨v, hv⟩ := exists_ne (1 : H)
  exact hv (hle (Subgroup.mem_top v))

theorem isCyclic_sylow_of_free_complement [Finite L] (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) [Group.IsSolvable H]
    (hfree : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥)
    (hp : p.Prime) (P : Subgroup E) (hP : Nat.card P = p ^ (Nat.card E).factorization p) :
    IsCyclic P :=
  isCyclic_of_isPGroup_of_free_complement hodd hH hfree hp (IsPGroup.of_card hP)

theorem isZGroup_of_free_complement [Finite L] (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) [Group.IsSolvable H]
    (hfree : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) : IsZGroup E :=
  (isZGroup_iff E).2 fun _q hq P =>
    haveI := Fact.mk hq
    isCyclic_sylow_of_free_complement hodd hH hfree hq _ P.card_eq_multiplicity

theorem exponent_eq_natCard_of_free_complement [Finite L] (hodd : Odd (Nat.card L))
    {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) [Group.IsSolvable H]
    (hfree : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    Monoid.exponent E = Nat.card E :=
  exponent_eq_natCard_of_isCyclic_of_natCard_eq_pow_factorization
    fun _q hq P hP => isCyclic_sylow_of_free_complement hodd hH hfree hq P hP

theorem isCyclic_sylow_and_exponent_eq_of_frobenius_decomposition [Finite L]
    (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (_hE : E ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hdisj : H ⊓ E = ⊥)
    (hnil : Group.IsNilpotent H)
    (hfree : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    (∀ q : ℕ, q.Prime → ∀ P : Subgroup E,
        Nat.card P = q ^ (Nat.card E).factorization q → IsCyclic P) ∧
      Monoid.exponent E = Nat.card E ∧
      Monoid.exponent E = Nat.card (Set.range fun g : L => g • (H : Set L)) := by
  have _ : Group.IsSolvable H := by have := hnil; infer_instance
  have hHE : H.IsComplement' E :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hdisj) hmul
  refine ⟨fun q hq P hP => isCyclic_sylow_of_free_complement hodd hH hfree hq P hP,
    exponent_eq_natCard_of_free_complement hodd hH hfree, ?_⟩
  rw [exponent_eq_natCard_of_free_complement hodd hH hfree, natCard_range_leftCoset,
    hHE.symm.index_eq_card]

theorem isCyclic_sylow_and_exponent_eq_of_frobenius_decomposition_of_series [Finite L]
    (hodd : Odd (Nat.card L)) {H E : Subgroup L} [H.Normal] (hH : H ≠ ⊥) (_hE : E ≠ ⊥)
    (hmul : (H : Set L) * (E : Set L) = Set.univ) (hdisj : H ⊓ E = ⊥)
    (hnil : ∃ (t : ℕ) (S : ℕ → Subgroup H), S 0 = ⊥ ∧ S t = ⊤ ∧ (∀ i < t, S i ≤ S (i + 1)) ∧
      (∀ i, (S i).Normal) ∧ ∀ i, 1 ≤ i → i ≤ t → ⁅(⊤ : Subgroup H), S i⁆ ≤ S (i - 1))
    (hfree : ∀ u ∈ E, u ≠ 1 → H ⊓ Subgroup.centralizer {u} = ⊥) :
    IsZGroup E ∧ Monoid.exponent E = Nat.card E ∧
      Monoid.exponent E = Nat.card (Set.range fun g : L => g • (H : Set L)) := by
  have _ : Group.IsSolvable H := isSolvable_of_exists_normal_series_commutator_le hnil
  have hHE : H.IsComplement' E :=
    Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 hdisj) hmul
  refine ⟨isZGroup_of_free_complement hodd hH hfree,
    exponent_eq_natCard_of_free_complement hodd hH hfree, ?_⟩
  rw [exponent_eq_natCard_of_free_complement hodd hH hfree, natCard_range_leftCoset,
    hHE.symm.index_eq_card]

end CFSG.FeitThompson

end
