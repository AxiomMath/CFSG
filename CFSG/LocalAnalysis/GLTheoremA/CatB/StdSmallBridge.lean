module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
public import CFSG.LocalAnalysis.GLTheoremA.S12.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

theorem isU42_of_catalogIs {S : Type} [Group S] (h : catalogIs S S9.isU4two) :
    CFSG.Assembly.LargeEvenIsU42 S := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CatB.lieIndex_isU4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  obtain ⟨-, K, i1, i2, hK, ⟨e'⟩⟩ := hm.statedClassicalModel (by decide)
  exact ⟨K, i1, i2, by rw [hK]; norm_num, ⟨e'⟩⟩

theorem nontrivial_pSimple_of_smallType {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hs : SmallType 3 K) : Nontrivial (PSimple 3 K) := by
  rcases hs with hu | ha
  · obtain ⟨i, hi, ⟨e⟩⟩ := hu
    have h42 : CFSG.Assembly.LargeEvenIsU42 (PSimple 3 K) :=
      isU42_of_catalogIs (S := PSimple 3 K) ⟨i, hi, ⟨e⟩⟩
    have hc : Nat.card (PSimple 3 K) = 25920 := CFSG.StandardType.IOneOrthEnd.card_of_isU42 h42
    haveI : Finite (PSimple 3 K) := inferInstance
    exact Finite.one_lt_card_iff_nontrivial.1 (by rw [hc]; norm_num)
  · obtain ⟨i, hi, ⟨e⟩⟩ := ha
    cases i with
    | cyclic q hq => simp [S10.isA6] at hi
    | alternating n hn =>
      simp only [S10.isA6] at hi
      subst hi
      exact e.toEquiv.nontrivial
    | sporadic s => simp [S10.isA6] at hi
    | lie k => simp [S10.isA6] at hi

theorem toSimple_bijective_of_center_bot {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : Subgroup.center ↥K = ⊥)
    (hnt : Nontrivial (PSimple 3 K)) : Function.Bijective (CatB.toSimple 3 K) := by
  refine ⟨?_, CatB.toSimple_surjective 3 K⟩
  have hne : GLAPPrimeCore 3 ↥K ≠ ⊤ := by
    intro htop
    haveI : Subsingleton (PQuot 3 K) := by
      show Subsingleton (↥K ⧸ GLAPPrimeCore 3 ↥K)
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    haveI : Subsingleton (PSimple 3 K) :=
      Function.Surjective.subsingleton (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 K)))
    exact not_subsingleton _ ‹_›
  have hO : GLAPPrimeCore 3 ↥K ≤ Subgroup.center ↥K :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hne
  rw [hZ] at hO
  rw [injective_iff_map_eq_one]
  intro k hk
  have hmem : (QuotientGroup.mk k : PQuot 3 K) ∈ Subgroup.center (PQuot 3 K) := by
    have := (QuotientGroup.eq_one_iff (N := Subgroup.center (PQuot 3 K)) (QuotientGroup.mk k : PQuot 3 K)).1 hk
    exact this
  have hc : k ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro k'
    have h1 := Subgroup.mem_center_iff.1 hmem (QuotientGroup.mk k')
    have h2 : (QuotientGroup.mk (k' * k) : PQuot 3 K) = QuotientGroup.mk (k * k') := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]; exact h1
    have h3 := QuotientGroup.eq.1 h2
    have h4 : (k' * k)⁻¹ * (k * k') ∈ (⊥ : Subgroup ↥K) := hO h3
    rw [Subgroup.mem_bot] at h4
    exact inv_inj.1 (mul_eq_one_iff_eq_inv.1 h4)
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem glaSmall_of_center_bot {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple ↥K) (hZ : Subgroup.center ↥K = ⊥) (hs : SmallType 3 K) :
    GLASmall K := by
  have hnt := nontrivial_pSimple_of_smallType hs
  have e : ↥K ≃* PSimple 3 K :=
    MulEquiv.ofBijective (CatB.toSimple 3 K) (toSimple_bijective_of_center_bot hq hZ hnt)
  rcases hs with hu | ha
  · left
    exact isU42_of_catalogIs ((catalogIs_congr e).2 hu)
  · right
    obtain ⟨i, hi, ⟨f⟩⟩ := (catalogIs_congr e).2 ha
    cases i with
    | cyclic q hq => simp [S10.isA6] at hi
    | alternating n hn =>
      simp only [S10.isA6] at hi
      subst hi
      exact ⟨f⟩
    | sporadic s => simp [S10.isA6] at hi
    | lie k => simp [S10.isA6] at hi

end CFSG.LocalAnalysis.GLTheoremA
