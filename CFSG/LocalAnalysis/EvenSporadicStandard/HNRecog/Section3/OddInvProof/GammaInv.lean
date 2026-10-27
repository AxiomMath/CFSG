module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LocalGz
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private theorem isConj_iff_of_isConj {G : Type} [Group G] {a x : G} (hx : IsConj a x)
    (b : G) : IsConj x b ↔ IsConj a b :=
  ⟨fun h => hx.trans h, fun h => hx.symm.trans h⟩

private theorem orb2A_eq_of_isConj {G : Type} [Group G] {a x : G} (hx : IsConj a x) (y : G) :
    orb2A x y = orb2A a y := by
  ext b
  simp only [orb2A, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(isConj_iff_of_isConj hx b).mp h1, (isConj_iff_of_isConj hx (y * b)).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isConj_iff_of_isConj hx b).mpr h1, (isConj_iff_of_isConj hx (y * b)).mpr h2⟩

private theorem orb2B_eq_of_isConj {G : Type} [Group G] {a z x : G} (hx : IsConj a x) (y : G) :
    orb2B x z y = orb2B a z y := by
  ext b
  simp only [orb2B, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(isConj_iff_of_isConj hx b).mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isConj_iff_of_isConj hx b).mpr h1, h2⟩

private theorem orb4A_eq_of_isConj {G : Type} [Group G] {a z x : G} (hx : IsConj a x) (y : G) :
    orb4A x z y = orb4A a z y := by
  ext c
  simp only [orb4A, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(isConj_iff_of_isConj hx c).mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isConj_iff_of_isConj hx c).mpr h1, h2⟩

private theorem orb4B_eq_of_isConj {G : Type} [Group G] {a x : G} (hx : IsConj a x) (y : G) :
    orb4B x y = orb4B a y := by
  ext c
  simp only [orb4B, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(isConj_iff_of_isConj hx c).mp h1,
      (isConj_iff_of_isConj hx ((y * c) ^ 2)).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(isConj_iff_of_isConj hx c).mpr h1,
      (isConj_iff_of_isConj hx ((y * c) ^ 2)).mpr h2⟩

private theorem orb6A_eq_of_isConj {G : Type} [Group G] {a x : G} (hx : IsConj a x) (y : G) :
    orb6A x y = orb6A a y := by
  ext c
  simp only [orb6A, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(isConj_iff_of_isConj hx c).mp h1, h2,
      (isConj_iff_of_isConj hx ((y * c) ^ 3)).mp h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(isConj_iff_of_isConj hx c).mpr h1, h2,
      (isConj_iff_of_isConj hx ((y * c) ^ 3)).mpr h3⟩

private theorem orb3A_eq_of_isConj {G : Type} [Group G] {a x : G} (hx : IsConj a x) :
    orb3A x x = orb3A a x := by
  ext c
  simp only [orb3A, Set.mem_setOf_eq]
  rw [orb2A_eq_of_isConj hx x, orb2A_eq_of_isConj hx c]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(isConj_iff_of_isConj hx c).mp h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨(isConj_iff_of_isConj hx c).mpr h1, h2, h3⟩

private theorem oddSet_eq_of_isConj {G : Type} [Group G] {a x : G} (hx : IsConj a x) :
    oddSet x x = oddSet a x := by
  ext c
  simp only [oddSet, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2, h3, t, h4, h5⟩
    exact ⟨(isConj_iff_of_isConj hx c).mp h1, h2, h3, t,
      (isConj_iff_of_isConj hx t).mp h4, h5⟩
  · rintro ⟨h1, h2, h3, t, h4, h5⟩
    exact ⟨(isConj_iff_of_isConj hx c).mpr h1, h2, h3, t,
      (isConj_iff_of_isConj hx t).mpr h4, h5⟩

private theorem orb5A_eq_of_isConj {G : Type} [Group G] {a x : G} (hx : IsConj a x) :
    orb5A x x = orb5A a x := by
  ext c
  simp only [orb5A, Set.mem_setOf_eq, oddSet_eq_of_isConj hx]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t ht htc => h3 t ((isConj_iff_of_isConj hx t).mpr ht) htc⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t ht htc => h3 t ((isConj_iff_of_isConj hx t).mp ht) htc⟩

private theorem orb5E_eq_of_isConj {G : Type} [Group G] {a x : G} (hx : IsConj a x) :
    orb5E x x = orb5E a x := by
  ext c
  simp only [orb5E, Set.mem_setOf_eq, oddSet_eq_of_isConj hx]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t ht htc => h3 t ((isConj_iff_of_isConj hx t).mpr ht) htc⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, fun t ht htc => h3 t ((isConj_iff_of_isConj hx t).mp ht) htc⟩

private theorem mem_gammaSet_of_mem_orb2A {G : Type} [Group G] {a z x y : G}
    (h : y ∈ orb2A a x) : y ∈ gammaSet a z x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  tauto

private theorem mem_gammaSet_of_mem_orb2B {G : Type} [Group G] {a z x y : G}
    (h : y ∈ orb2B a z x) : y ∈ gammaSet a z x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  tauto

private theorem mem_gammaSet_of_mem_orb3A {G : Type} [Group G] {a z x y : G}
    (h : y ∈ orb3A a x) : y ∈ gammaSet a z x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  tauto

private theorem mem_gammaSet_of_mem_orb4A {G : Type} [Group G] {a z x y : G}
    (h : y ∈ orb4A a z x) : y ∈ gammaSet a z x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  tauto

private theorem mem_gammaSet_of_mem_orb4B {G : Type} [Group G] {a z x y : G}
    (h : y ∈ orb4B a x) : y ∈ gammaSet a z x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  tauto

private theorem mem_gammaSet_of_mem_orb5A {G : Type} [Group G] {a z x y : G}
    (h : y ∈ orb5A a x) : y ∈ gammaSet a z x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  tauto

private theorem mem_gammaSet_of_mem_orb5E {G : Type} [Group G] {a z x y : G}
    (h : y ∈ orb5E a x) : y ∈ gammaSet a z x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  tauto

private theorem mem_gammaSet_of_mem_orb6A {G : Type} [Group G] {a z x y : G}
    (h : y ∈ orb6A a x) : y ∈ gammaSet a z x := by
  simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
  tauto

theorem oddInv_gamma_of_inv {G : Type} [Group G] {a z : G} (hCls : GzClassFacts a z)
    (hT5 : Vert TableVFacts a z) (hT7 : Vert TableVIIFacts a z)
    (hodd : ∀ w x y : G, IsConj z w → IsConj a x → IsConj a y → x ∈ Gx w → y ∈ Gx w →
      Odd (orderOf (x * y)) → ∃ t : G, IsConj a t ∧ t ∈ Gxyz x w y)
    {x y : G} (hx : IsConj a x) (hy : IsConj a y) (ht : ∃ t : G, orderOf t = 2 ∧ t ∈ Gxy x y) :
    y ∈ gammaSet a z x := by
  have hxy : IsConj x y := hx.symm.trans hy
  by_cases hyx : y = x
  · rw [hyx]
    simp only [gammaSet, Set.mem_union, Set.mem_singleton_iff, or_assoc]
    exact Or.inl trivial
  · by_cases heven : Even (orderOf (x * y))
    ·
      have hybase : y ∈ tab5Base x := ⟨hxy, heven⟩
      obtain ⟨i, hi⟩ := (hT5 x z hx (IsConj.refl z)).partition.cover y hybase
      fin_cases i
      · simp only [tab5Set] at hi
        rw [orb2A_eq_of_isConj hx x] at hi
        exact mem_gammaSet_of_mem_orb2A hi
      · simp only [tab5Set] at hi
        rw [orb2B_eq_of_isConj hx x] at hi
        exact mem_gammaSet_of_mem_orb2B hi
      · simp only [tab5Set] at hi
        rw [orb4A_eq_of_isConj hx x] at hi
        exact mem_gammaSet_of_mem_orb4A hi
      · simp only [tab5Set] at hi
        rw [orb4B_eq_of_isConj hx x] at hi
        exact mem_gammaSet_of_mem_orb4B hi
      · simp only [tab5Set] at hi
        rw [orb6A_eq_of_isConj hx x] at hi
        exact mem_gammaSet_of_mem_orb6A hi
    ·
      have hoddxy : Odd (orderOf (x * y)) := Nat.not_even_iff_odd.mp heven
      have key : (∃ s : G, IsConj a s ∧ s ∈ Gxy x y) → y ∈ gammaSet a z x := by
        rintro ⟨s, hsA, hsxy⟩
        have hys : y ∈ oddSet x x := ⟨hxy, hyx, hoddxy, s, hx.symm.trans hsA, hsxy⟩
        obtain ⟨i, hi⟩ := (hT7 x z hx (IsConj.refl z)).partition.cover y hys
        fin_cases i
        · have hi' : y ∈ orb3A x x := by simpa using hi
          rw [orb3A_eq_of_isConj hx] at hi'
          exact mem_gammaSet_of_mem_orb3A hi'
        · have hi' : y ∈ orb5A x x := by simpa using hi
          rw [orb5A_eq_of_isConj hx] at hi'
          exact mem_gammaSet_of_mem_orb5A hi'
        · have hi' : y ∈ orb5E x x := by simpa using hi
          rw [orb5E_eq_of_isConj hx] at hi'
          exact mem_gammaSet_of_mem_orb5E hi'
      obtain ⟨t, ht2, htxy⟩ := ht
      rcases hCls.inv_two t ht2 with htA | htB
      · exact key ⟨t, htA, htxy⟩
      · have hxGt : x ∈ Gx t := mem_Gx.mpr ((mem_Gx.mp (mem_Gxy.mp htxy).1).symm)
        have hyGt : y ∈ Gx t := mem_Gx.mpr ((mem_Gx.mp (mem_Gxy.mp htxy).2).symm)
        obtain ⟨t', ht'A, ht'xyz⟩ := hodd t x y htB hx hy hxGt hyGt hoddxy
        rw [mem_Gxyz] at ht'xyz
        exact key ⟨t', ht'A, mem_Gxy.2 ⟨ht'xyz.1, ht'xyz.2.2⟩⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3