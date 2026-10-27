module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Local
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.GammaCount

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G] {a z : G}

theorem orb2A_rep {b : G} (h : IsConj a b) (x : G) : orb2A b x = orb2A a x := by
  ext c
  simp only [orb2A, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h.trans h1, h.trans h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h.symm.trans h1, h.symm.trans h2⟩

theorem orb3A_rep {b : G} (h : IsConj a b) (x : G) : orb3A b x = orb3A a x := by
  ext c
  have hx : orb2A b x = orb2A a x := orb2A_rep h x
  have hc : orb2A b c = orb2A a c := orb2A_rep h c
  simp only [orb3A, Set.mem_setOf_eq, hx, hc]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h.trans h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h.symm.trans h1, h2, h3⟩

theorem oddSet_rep {b : G} (h : IsConj a b) (x : G) : oddSet b x = oddSet a x := by
  ext c
  simp only [oddSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, t, ht, htm⟩
    exact ⟨h.trans h1, h2, h3, t, h.trans ht, htm⟩
  · rintro ⟨h1, h2, h3, t, ht, htm⟩
    exact ⟨h.symm.trans h1, h2, h3, t, h.symm.trans ht, htm⟩

theorem orb5A_rep {b : G} (h : IsConj a b) (x : G) : orb5A b x = orb5A a x := by
  have hx : oddSet b x = oddSet a x := oddSet_rep h x
  ext c
  simp only [orb5A, Set.mem_setOf_eq, hx]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t ht htm => h3 t (h.symm.trans ht) htm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t ht htm => h3 t (h.trans ht) htm⟩

theorem orb5E_rep {b : G} (h : IsConj a b) (x : G) : orb5E b x = orb5E a x := by
  have hx : oddSet b x = oddSet a x := oddSet_rep h x
  ext c
  simp only [orb5E, Set.mem_setOf_eq, hx]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t ht htm => h3 t (h.symm.trans ht) htm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t ht htm => h3 t (h.trans ht) htm⟩

theorem tableVII_partition_at (hL : F5Local G a z) {b : G} (hb : IsConj a b) :
    IsOrbitPartition (Gx b) (oddSet a b) ![orb3A a b, orb5A a b, orb5E a b] := by
  have h := (hL.tableVII b z hb (IsConj.refl z)).partition
  rw [oddSet_rep hb b, orb3A_rep hb b, orb5A_rep hb b, orb5E_rep hb b] at h
  exact h

theorem card_Gxy_orb5E_at (hL : F5Local G a z) {b : G} (hb : IsConj a b) {y : G}
    (hy : y ∈ orb5E a b) : Nat.card ↥(Gxy b y) = 500 := by
  have hy' : y ∈ orb5E b b := by
    rwa [← orb5E_rep hb b] at hy
  exact card_eq_of_isShapeFiveCubeByTwoTwo ((hL.five b z hb (IsConj.refl z)).five_E y hy')

theorem card_of_isNonsplitDoubleCoverOfS5 {Y : Type} [Group Y] [Finite Y]
    (h : IsNonsplitDoubleCoverOfS5 Y) : Nat.card Y = 240 := by
  obtain ⟨Z, _, hZcard, ⟨e⟩, -⟩ := h
  have hq : Nat.card (Y ⧸ Z) = 120 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup Z, hZcard, hq]

theorem mem_orb5A_of_exists_order_three (hL : F5Local G a z) {b y : G} (hb : IsConj a b)
    (hy : y ∈ oddSet a b) (h5 : orderOf (b * y) = 5) (hs : ∃ s ∈ Gxy b y, orderOf s = 3) :
    y ∈ orb5A a b := by
  obtain ⟨i, hi⟩ := (tableVII_partition_at hL hb).cover y hy
  fin_cases i
  · exfalso
    simp only [orb3A, Set.mem_setOf_eq] at hi
    exact absurd hi.2.1 (by rw [h5]; norm_num)
  · exact hi
  · exfalso
    obtain ⟨s, hsG, hs3⟩ := hs
    have hcard := card_Gxy_orb5E_at hL hb hi
    have hdvd := Subgroup.orderOf_dvd_natCard (Gxy b y) hsG
    rw [hcard, hs3] at hdvd
    norm_num at hdvd

theorem mem_orb5E_of_card_lt (hL : F5Local G a z) [Finite G] {b y : G} (hb : IsConj a b)
    (hy : y ∈ oddSet a b) (h5 : orderOf (b * y) = 5) {t : G} (ht : IsConj a t)
    (htm : t ∈ Gxy b y) (hlt : Nat.card ↥(Gxyz b t y) < 240) : y ∈ orb5E a b := by
  obtain ⟨i, hi⟩ := (tableVII_partition_at hL hb).cover y hy
  fin_cases i
  · exfalso
    simp only [orb3A, Set.mem_setOf_eq] at hi
    exact absurd hi.2.1 (by rw [h5]; norm_num)
  · exfalso
    simp only [orb5A, Set.mem_setOf_eq] at hi
    have hshape : IsNonsplitDoubleCoverOfS5 ↥(Gxyz b t y) := hi.2.2 t ht htm
    have hcard : Nat.card ↥(Gxyz b t y) = 240 := card_of_isNonsplitDoubleCoverOfS5 hshape
    omega
  · exact hi

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
