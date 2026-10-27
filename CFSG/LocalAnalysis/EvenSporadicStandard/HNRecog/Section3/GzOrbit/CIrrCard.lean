module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Interface

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog
open scoped commutatorElement

private lemma card_centralizer_extraspecial_sub {H : Type*} [Group H] [Finite H]
    (hcent : Nat.card (Subgroup.center H) = 2)
    (hcomm : _root_.commutator H ≤ Subgroup.center H)
    (hcard : Nat.card H = 2 ^ 9) {a : H} (ha_not_cent : a ∉ Subgroup.center H) :
    Nat.card (Subgroup.centralizer ({a} : Set H)) = 2 ^ 8 := by
  obtain ⟨w, hw, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center H)).mp hcent
  have hw1 : (w : H) ≠ 1 := fun h => hw (Subtype.ext h)
  have hcenter : ∀ c : H, c ∈ Subgroup.center H → c ≠ 1 → c = (w : H) := fun c hc hc1 =>
    Subtype.ext_iff.mp (huniq ⟨c, hc⟩ (by simpa using hc1))
  have hcomm_u : ∀ c : H, c * a * c⁻¹ = a ∨ c * a * c⁻¹ = (w : H) * a := by
    intro c
    have hc : ⁅c, a⁆ ∈ Subgroup.center H :=
      hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top c) (Subgroup.mem_top a))
    have key : c * a * c⁻¹ = ⁅c, a⁆ * a := by
      rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul]
    rcases eq_or_ne ⁅c, a⁆ 1 with h1 | h1
    · left; rw [key, h1, one_mul]
    · right; rw [key, hcenter _ hc h1]
  have hnc : ∃ c : H, c * a * c⁻¹ ≠ a := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    refine ha_not_cent ?_
    rw [Subgroup.mem_center_iff]
    intro x
    rw [← commutatorElement_eq_one_iff_mul_comm]
    have h := hcon x
    rw [← MulAut.conj_apply, conj_eq_commutatorElement_mul] at h
    calc ⁅x, a⁆ = ⁅x, a⁆ * a * a⁻¹ := by group
      _ = a * a⁻¹ := by rw [h]
      _ = 1 := by group
  have hne : a ≠ (w : H) * a := by
    intro h
    have h1 : (w : H) = 1 := by
      have h' := congrArg (fun t => t * a⁻¹) h
      simpa [mul_assoc] using h'.symm
    exact hw1 h1
  have hclass : conjugatesOf a = {a, (w : H) * a} := by
    ext b
    constructor
    · intro hb
      obtain ⟨c, hc⟩ := isConj_iff.mp hb
      rcases hcomm_u c with h | h
      · left; exact hc.symm.trans h
      · right; exact hc.symm.trans h
    · intro hb
      rcases hb with rfl | rfl
      · exact mem_conjugatesOf_self
      · obtain ⟨c, hc⟩ := hnc
        rcases hcomm_u c with h | h
        · exact absurd h hc
        · exact isConj_iff.mpr ⟨c, h⟩
  have hindex : (Subgroup.centralizer ({a} : Set H)).index = 2 := by
    rw [Subgroup.index_centralizer_eq_ncard, hclass, Set.ncard_pair hne]
  have hmain := Subgroup.card_mul_index (Subgroup.centralizer ({a} : Set H))
  rw [hindex, hcard] at hmain
  omega

theorem card_inf_centralizer_of_isPlusExtraspecial {C : Type} [Group C] {Q : Subgroup C}
    (hQ : IsPlusExtraspecial 4 Q) {q : C} (hqQ : q ∈ Q) (hq : q ∉ centerOf Q) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({q} : Set C)) = 2 ^ 8 := by
  have hExt : CFSG.IsExtraspecial 2 ↥Q := hQ.1
  have hcent : Nat.card (Subgroup.center ↥Q) = 2 := hExt.center_order_p
  have hcard : Nat.card ↥Q = 2 ^ 9 := by
    have hc := hQ.2.1
    norm_num at hc ⊢
    exact hc
  haveI : Finite ↥Q := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hcomm : _root_.commutator ↥Q ≤ Subgroup.center ↥Q := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    haveI := hExt.quotient_elementary_abelian
    infer_instance
  have ha_not_cent : (⟨q, hqQ⟩ : ↥Q) ∉ Subgroup.center ↥Q := by
    intro hmem
    refine hq ?_
    rw [centerOf, Subgroup.mem_inf]
    refine ⟨hqQ, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := Subgroup.mem_center_iff.mp hmem ⟨y, hy⟩
    simpa using congrArg (fun t : ↥Q => (t : C)) h
  have hcent_card := card_centralizer_extraspecial_sub hcent hcomm hcard ha_not_cent
  have hmap : Q ⊓ Subgroup.centralizer ({q} : Set C) =
      (Subgroup.centralizer ({(⟨q, hqQ⟩ : ↥Q)} : Set ↥Q)).map Q.subtype := by
    ext g
    constructor
    · intro hg
      refine Subgroup.mem_map_of_mem (f := Q.subtype)
        (K := Subgroup.centralizer ({(⟨q, hqQ⟩ : ↥Q)} : Set ↥Q))
        (x := ⟨g, hg.1⟩) ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hg.2
    · intro hg
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
      have hgval : (y : C) = g := hyg
      exact ⟨by rw [← hgval]; exact y.2, by
        rw [← hgval]
        have hy' := congrArg (fun t : ↥Q => (t : C))
          (Subgroup.mem_centralizer_singleton_iff.mp hy)
        exact Subgroup.mem_centralizer_singleton_iff.mpr hy'⟩
  rw [hmap, ← Nat.card_congr (Subgroup.equivMapOfInjective
    (Subgroup.centralizer ({(⟨q, hqQ⟩ : ↥Q)} : Set ↥Q))
    Q.subtype Subtype.coe_injective).toEquiv]
  exact hcent_card

end CFSG.EvenSporadicStandard.HNRecog.Section3
