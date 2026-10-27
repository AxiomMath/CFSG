module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.Qz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion2.O2Bound

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog Subgroup
open scoped commutatorElement

private lemma eq_of_mem_center_of_card_two {Q : Type*} [Group Q]
    (hcard : Nat.card (Subgroup.center Q) = 2) {u v : Q}
    (hu : u ∈ Subgroup.center Q) (hv : v ∈ Subgroup.center Q) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    u = v := by
  obtain ⟨m, hm, huniq⟩ := (Nat.card_eq_two_iff' (1 : Subgroup.center Q)).mp hcard
  exact Subtype.ext_iff.mp ((huniq ⟨u, hu⟩ (by simpa using hu1)).trans
    (huniq ⟨v, hv⟩ (by simpa using hv1)).symm)

private lemma card_centralizer_extraspecial {H : Type*} [Group H] [Finite H]
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

theorem a_not_mem_Qz {G : Type} [Group G] {a u : G} (ha : a ^ 2 = 1) (hu : u ^ 2 = 1) (ha1 : a ≠ 1)
    (hu1 : u ≠ 1) (hau : a ≠ u) (hcomm : a * u = u * a)
    (hC : IsExtraspecialPlusByA5WrTwo ↥(Gx u)) (hX : IsShapeTwoTwoTimesTwoFourA5 ↥(Gxy a u)) :
    a ∉ Qz u := by
  intro haQ
  obtain ⟨Q, hQ, hQW, hQz⟩ := exists_Qz_eq hC
  haveI : Q.Normal := hQ
  have hExtQ : CFSG.IsExtraspecial 2 ↥Q := hQW.plus.1
  have hQcard : Nat.card Q = 2 ^ 9 := by
    have hc := hQW.plus.2.1
    norm_num at hc ⊢
    exact hc
  have hQz_le : Qz u ≤ Gx u := by
    rw [hQz]
    exact Subgroup.map_subtype_le (H := Gx u) Q
  have huwmem : u ∈ Gx u := self_mem_Gx u
  have huC_cent : (⟨u, huwmem⟩ : ↥(Gx u)) ∈ Subgroup.centralizer (Q : Set ↥(Gx u)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q _
    apply Subtype.ext
    exact (mem_Gx.mp q.2).symm
  have huQmem : (⟨u, huwmem⟩ : ↥(Gx u)) ∈ Q := hQW.centralizer_le huC_cent
  have huQz : u ∈ Qz u := by
    rw [hQz]
    exact Subgroup.mem_map_of_mem (Gx u).subtype huQmem
  have hExtQz : CFSG.IsExtraspecial 2 ↥(Qz u) := by
    rw [hQz]
    exact TwoHSData.isExtraspecial_of_mulEquiv
      (Subgroup.equivMapOfInjective Q (Gx u).subtype Subtype.coe_injective) hExtQ
  have hQzcard : Nat.card ↥(Qz u) = 2 ^ 9 := by
    rw [hQz, ← Nat.card_congr (Subgroup.equivMapOfInjective Q (Gx u).subtype
      Subtype.coe_injective).toEquiv]
    exact hQcard
  haveI : Finite ↥(Qz u) := Nat.finite_of_card_ne_zero (by rw [hQzcard]; norm_num)
  have hcent_card : Nat.card (Subgroup.center ↥(Qz u)) = 2 := hExtQz.center_order_p
  have hu_center : (⟨u, huQz⟩ : ↥(Qz u)) ∈ Subgroup.center ↥(Qz u) := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact (mem_Gx.mp (hQz_le x.2)).symm
  have hu_ne_one : (⟨u, huQz⟩ : ↥(Qz u)) ≠ 1 := by
    intro h
    exact hu1 (by simpa using congrArg (fun t : ↥(Qz u) => (t : G)) h)
  have ha_ne_one : (⟨a, haQ⟩ : ↥(Qz u)) ≠ 1 := by
    intro h
    exact ha1 (by simpa using congrArg (fun t : ↥(Qz u) => (t : G)) h)
  have ha_not_cent : (⟨a, haQ⟩ : ↥(Qz u)) ∉ Subgroup.center ↥(Qz u) := by
    intro hmem
    have heq : (⟨a, haQ⟩ : ↥(Qz u)) = ⟨u, huQz⟩ :=
      eq_of_mem_center_of_card_two hcent_card hmem hu_center ha_ne_one hu_ne_one
    exact hau (by simpa using congrArg (fun t : ↥(Qz u) => (t : G)) heq)
  have hcommQz : _root_.commutator ↥(Qz u) ≤ Subgroup.center ↥(Qz u) := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    haveI := hExtQz.quotient_elementary_abelian
    infer_instance
  have hcent_card' := card_centralizer_extraspecial hcent_card hcommQz hQzcard ha_not_cent
  have hLmap : Qz u ⊓ Gx a =
      (Subgroup.centralizer ({(⟨a, haQ⟩ : ↥(Qz u))} : Set ↥(Qz u))).map
        (Qz u).subtype := by
    ext g
    constructor
    · intro hg
      refine Subgroup.mem_map_of_mem (f := (Qz u).subtype)
        (K := Subgroup.centralizer ({(⟨a, haQ⟩ : ↥(Qz u))} : Set ↥(Qz u)))
        (x := ⟨g, hg.1⟩) ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact (mem_Gx.mp hg.2).symm
    · intro hg
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
      have hgval : (y : G) = g := hyg
      exact ⟨by rw [← hgval]; exact y.2, by
        rw [← hgval]
        have hy' := congrArg (fun t : ↥(Qz u) => (t : G))
          (Subgroup.mem_centralizer_singleton_iff.mp hy)
        exact mem_Gx.mpr hy'.symm⟩
  have hLcard : Nat.card ↥(Qz u ⊓ Gx a) = 2 ^ 8 := by
    rw [hLmap, ← Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({(⟨a, haQ⟩ : ↥(Qz u))} : Set ↥(Qz u)))
      (Qz u).subtype Subtype.coe_injective).toEquiv]
    exact hcent_card'
  have hR_le : Qz u ⊓ Gx a ≤ Gxy a u := by
    calc Qz u ⊓ Gx a ≤ Gx u ⊓ Gx a := inf_le_inf hQz_le le_rfl
      _ = Gx a ⊓ Gx u := inf_comm _ _
      _ = Gxy a u := (Gxy_eq_inf a u).symm
  have hconjQz : ∀ g ∈ Gxy a u, ∀ r ∈ Qz u, g * r * g⁻¹ ∈ Qz u := by
    intro g hg r hr
    have hgu : g ∈ Gx u := (mem_Gxy.mp hg).2
    rw [hQz] at hr ⊢
    obtain ⟨r', hr', hr'r⟩ := Subgroup.mem_map.mp hr
    refine Subgroup.mem_map.mpr
      ⟨(⟨g, hgu⟩ : ↥(Gx u)) * r' * (⟨g, hgu⟩ : ↥(Gx u))⁻¹, ?_, ?_⟩
    · exact (inferInstance : Q.Normal).conj_mem r' hr' ⟨g, hgu⟩
    · simpa [hr'r]
  have hnorm : ∀ g ∈ Gxy a u, ∀ p ∈ Qz u ⊓ Gx a, g * p * g⁻¹ ∈ Qz u ⊓ Gx a := by
    intro g hg p hp
    refine ⟨hconjQz g hg p hp.1, ?_⟩
    exact (Gx a).mul_mem ((Gx a).mul_mem (mem_Gxy.mp hg).1 hp.2)
      ((Gx a).inv_mem (mem_Gxy.mp hg).1)
  have hQz_pg : IsPGroup 2 (Qz u) := hExtQz.isPGroup
  have hRpg : IsPGroup 2 ↥(Qz u ⊓ Gx a) := hQz_pg.to_le inf_le_left
  have hbound := card_le_of_normal_isPGroup (X := Gxy a u) hX (Qz u ⊓ Gx a) hR_le hnorm hRpg
  rw [hLcard] at hbound
  norm_num at hbound

end CFSG.EvenSporadicStandard.HNRecog.Section3
