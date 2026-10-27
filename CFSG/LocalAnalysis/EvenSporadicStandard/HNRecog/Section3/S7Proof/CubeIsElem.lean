module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.A8.CubeEnum

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem s7_isElemTwo_closure_three {G : Type} [Group G] {p q r : G} (hp : p ^ 2 = 1)
    (hq : q ^ 2 = 1) (hr : r ^ 2 = 1) (hpq : p * q = q * p) (hpr : p * r = r * p)
    (hqr : q * r = r * q) (hp1 : p ≠ 1) (hq1 : q ≠ 1) (hne : p ≠ q)
    (hr' : r ∉ Subgroup.closure ({p, q} : Set G)) :
    IsElemTwo 3 (Subgroup.closure ({p, q, r} : Set G)) := by
  let E := Subgroup.closure ({p, q, r} : Set G)
  let D := Subgroup.closure ({p, q} : Set G)
  have hDE : D ≤ E := by
    refine Subgroup.closure_mono ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    tauto
  have hrE : r ∈ E := Subgroup.subset_closure (by simp)
  have hrD : r ∉ D := hr'
  have hDltE : D < E := by
    refine lt_of_le_of_ne hDE ?_
    intro hEq
    rw [← hEq] at hrE
    exact hrD hrE
  have hpair : ({p, q, r} : Set G).Pairwise Commute := by
    rintro a ha b hb hab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact absurd rfl hab
    · exact hpq
    · exact hpr
    · exact hpq.symm
    · exact absurd rfl hab
    · exact hqr
    · exact hpr.symm
    · exact hqr.symm
    · exact absurd rfl hab
  haveI : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
  have hsq : ∀ e ∈ E, e ^ 2 = 1 := by
    intro e he
    rcases eq_of_mem_closure_three hp hq hr hpq hpr hqr he with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp
    · exact hp
    · exact hq
    · rw [Commute.mul_pow (show Commute p q from hpq) 2, hp, hq, mul_one]
    · exact hr
    · rw [Commute.mul_pow (show Commute p r from hpr) 2, hp, hr, mul_one]
    · rw [Commute.mul_pow (show Commute q r from hqr) 2, hq, hr, mul_one]
    · rw [Commute.mul_pow (show Commute (p * q) r from
          (show Commute p r from hpr).mul_left (show Commute q r from hqr)) 2,
        Commute.mul_pow (show Commute p q from hpq) 2, hp, hq, hr]
      simp
  have hDcard : Nat.card ↥D = 4 := card_closure_pair hp hq hpq hp1 hq1 hne
  haveI : Finite ↥D := Nat.finite_of_card_ne_zero (by rw [hDcard]; norm_num)
  let f : ↥D × Bool → ↥E := fun x =>
    match x.2 with
    | false => ⟨(x.1 : G), hDE x.1.2⟩
    | true => ⟨(x.1 : G) * r, E.mul_mem (hDE x.1.2) hrE⟩
  have hf : Function.Surjective f := by
    rintro ⟨e, he⟩
    rcases eq_of_mem_closure_three hp hq hr hpq hpr hqr he with
      h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact ⟨(⟨1, D.one_mem⟩, false), Subtype.ext (by simp [f, h1])⟩
    · exact ⟨(⟨p, Subgroup.subset_closure (by simp)⟩, false),
        Subtype.ext (by simp [f, h1])⟩
    · exact ⟨(⟨q, Subgroup.subset_closure (by simp)⟩, false),
        Subtype.ext (by simp [f, h1])⟩
    · exact ⟨(⟨p * q, D.mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))⟩, false),
        Subtype.ext (by simp [f, h1])⟩
    · exact ⟨(⟨1, D.one_mem⟩, true), Subtype.ext (by simp [f, h1])⟩
    · exact ⟨(⟨p, Subgroup.subset_closure (by simp)⟩, true),
        Subtype.ext (by simp [f, h1])⟩
    · exact ⟨(⟨q, Subgroup.subset_closure (by simp)⟩, true),
        Subtype.ext (by simp [f, h1])⟩
    · exact ⟨(⟨p * q, D.mul_mem (Subgroup.subset_closure (by simp))
          (Subgroup.subset_closure (by simp))⟩, true),
        Subtype.ext (by simp [f, h1])⟩
  haveI : Finite ↥E := Finite.of_surjective f hf
  have hcard_le : Nat.card ↥E ≤ Nat.card (↥D × Bool) :=
    Nat.card_le_card_of_surjective f hf
  have hcard_le' : Nat.card ↥E ≤ 8 := by
    refine hcard_le.trans ?_
    simp [Nat.card_prod, hDcard, Nat.card_eq_fintype_card, Fintype.card_bool]
  have hdvd : Nat.card ↥D ∣ Nat.card ↥E := Subgroup.card_dvd_of_le hDE
  have hlt : Nat.card ↥D < Nat.card ↥E := Subgroup.card_lt_of_lt hDltE
  rw [hDcard] at hdvd hlt
  obtain ⟨k, hk⟩ := hdvd
  rw [hk] at hlt hcard_le'
  have hk2 : k = 2 := by omega
  change IsElemTwo 3 E
  refine ⟨⟨inferInstance, hsq⟩, ?_⟩
  rw [hk, hk2]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
