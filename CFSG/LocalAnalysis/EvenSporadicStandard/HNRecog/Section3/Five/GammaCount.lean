module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Orbits
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GraphLocal
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion1.NotConj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Counting
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Five.Generic.Inverted

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G]

private lemma mul_self_eq_one_of_orderOf_eq_two {x : G} (hx : orderOf x = 2) : x * x = 1 := by
  have h := pow_orderOf_eq_one x
  rw [hx] at h
  simpa [pow_two] using h

private lemma card_Gx_eq_of_isF5Type (hI : TwoHSInterface) [Finite G] {a z : G} (h : IsF5Type a z) :
    Nat.card ↥(Gx a) = 177408000 := by
  have hh := card_centralizer_a_of_isF5Type hI h
  norm_num at hh
  exact hh

theorem IsOrbitPartition.card_eq_sum [Finite G] {ι : Type} [Fintype ι] {K : Subgroup G} {S : Set G}
    {P : ι → Set G} (h : IsOrbitPartition K S P) : Nat.card ↥S = ∑ i, Nat.card ↥(P i) := by
  classical
  have hS : S = ⋃ i, P i := by
    ext c
    constructor
    · intro hc
      exact Set.mem_iUnion.mpr (h.cover c hc)
    · intro hc
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hc
      exact h.subset i hi
  have hdisj : Pairwise fun i j => Disjoint (P i) (P j) := fun i j hij => h.disjoint i j hij
  have hfin : ∀ i, (P i).Finite := fun i => Set.toFinite (P i)
  change S.ncard = ∑ i, (P i).ncard
  rw [hS, Set.ncard_iUnion_of_finite hfin hdisj, finsum_eq_sum_of_fintype]

theorem IsOrbitPartition.card_mul_eq {ι : Type} {K : Subgroup G} [Finite K] {S : Set G}
    {P : ι → Set G} {n : ι → ℕ} (h : IsOrbitPartition K S P) (hn : StabCard K P n) (i : ι) :
    Nat.card ↥(P i) * n i = Nat.card ↥K := by
  obtain ⟨c, hc⟩ := (h.orbit i).nonempty
  rw [← hn i c hc]
  exact IsConjOrbit.card_mul_card_stab (h.orbit i) hc

theorem card_isConj_eq_of_gamma (hI : TwoHSInterface) (hU : U35Facts) [Finite G] {a z : G}
    (h : IsF5Type a z) (hGam : GammaFacts a z) (hT5 : TableVFacts a z) (hT7 : TableVIIFacts a z) :
    Nat.card {c : G // IsConj a c} = 1184184 + Nat.card ↥(orb5E a a) := by
  classical
  let A : Set G := {c : G | IsConj a c}
  have ha2 : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two h.orderOf_a
  have hGxcard : Nat.card ↥(Gx a) = 177408000 := card_Gx_eq_of_isF5Type hI h
  have hnotmem1 : a ∉ tab5Base a := by
    intro hmem
    have heven : Even (orderOf (a * a)) := hmem.2
    rw [ha2, orderOf_one] at heven
    exact Nat.not_even_one heven
  have hnotmem2 : a ∉ oddSet a a := fun hmem => hmem.2.1 rfl
  have hdisj : Disjoint (tab5Base a) (oddSet a a) := by
    rw [Set.disjoint_left]
    intro c hc1 hc2
    exact (Nat.not_even_iff_odd.mpr hc2.2.2.1) hc1.2
  have hdisj1 : Disjoint ({a} : Set G) (tab5Base a) := by
    rw [Set.disjoint_left]
    intro c hc1 hc2
    rw [Set.mem_singleton_iff] at hc1
    exact hnotmem1 (hc1 ▸ hc2)
  have hdisj2 : Disjoint ({a} ∪ tab5Base a) (oddSet a a) := by
    rw [Set.disjoint_left]
    intro c hc1 hc2
    rw [Set.mem_union, Set.mem_singleton_iff] at hc1
    rcases hc1 with rfl | hc1
    · exact hnotmem2 hc2
    · exact (Set.disjoint_left.mp hdisj hc1) hc2
  have hA : A = {a} ∪ tab5Base a ∪ oddSet a a := by
    apply Set.Subset.antisymm
    · intro c hc
      have hgam : c ∈ gammaSet a z a := hGam.eq_gamma a c (IsConj.refl a) hc
      simp only [gammaSet, Set.mem_union, or_assoc] at hgam
      rcases hgam with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8
      · exact Or.inl (Or.inl h0)
      · exact Or.inl (Or.inr (hT5.partition.subset 0 h1))
      · exact Or.inl (Or.inr (hT5.partition.subset 1 h2))
      · exact Or.inr (hT7.partition.subset 0 h3)
      · exact Or.inl (Or.inr (hT5.partition.subset 2 h4))
      · exact Or.inl (Or.inr (hT5.partition.subset 3 h5))
      · exact Or.inr (hT7.partition.subset 1 h6)
      · exact Or.inr (hT7.partition.subset 2 h7)
      · exact Or.inl (Or.inr (hT5.partition.subset 4 h8))
    · intro c hc
      rcases hc with (hc | hc) | hc
      · rw [Set.mem_singleton_iff] at hc
        rw [hc]
        exact IsConj.refl a
      · exact hc.1
      · exact hc.1
  have hlen0 : Nat.card ↥(tab5Set a z (0 : Fin 5)) = 2200 := by
    obtain ⟨c, hc⟩ := (hT5.partition.orbit 0).nonempty
    have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 80640 := by
      simpa using hT5.card_stab 0 c hc
    have hh := IsConjOrbit.card_mul_card_stab (hT5.partition.orbit 0) hc
    rw [hstab, hGxcard] at hh
    omega
  have hlen1 : Nat.card ↥(tab5Set a z (1 : Fin 5)) = 5775 := by
    obtain ⟨c, hc⟩ := (hT5.partition.orbit 1).nonempty
    have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 30720 := by
      simpa using hT5.card_stab 1 c hc
    have hh := IsConjOrbit.card_mul_card_stab (hT5.partition.orbit 1) hc
    rw [hstab, hGxcard] at hh
    omega
  have hlen2 : Nat.card ↥(tab5Set a z (2 : Fin 5)) = 277200 := by
    obtain ⟨c, hc⟩ := (hT5.partition.orbit 2).nonempty
    have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 640 := by
      simpa using hT5.card_stab 2 c hc
    have hh := IsConjOrbit.card_mul_card_stab (hT5.partition.orbit 2) hc
    rw [hstab, hGxcard] at hh
    omega
  have hlen3 : Nat.card ↥(tab5Set a z (3 : Fin 5)) = 123200 := by
    obtain ⟨c, hc⟩ := (hT5.partition.orbit 3).nonempty
    have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 1440 := by
      simpa using hT5.card_stab 3 c hc
    have hh := IsConjOrbit.card_mul_card_stab (hT5.partition.orbit 3) hc
    rw [hstab, hGxcard] at hh
    omega
  have hlen4 : Nat.card ↥(tab5Set a z (4 : Fin 5)) = 739200 := by
    obtain ⟨c, hc⟩ := (hT5.partition.orbit 4).nonempty
    have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 240 := by
      simpa using hT5.card_stab 4 c hc
    have hh := IsConjOrbit.card_mul_card_stab (hT5.partition.orbit 4) hc
    rw [hstab, hGxcard] at hh
    omega
  have hlen3A : Nat.card ↥(![orb3A a a, orb5A a a, orb5E a a] (0 : Fin 3)) = 35200 := by
    obtain ⟨c, hc⟩ := (hT7.partition.orbit 0).nonempty
    have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 5040 := hT7.card_3A c hc
    have hh := IsConjOrbit.card_mul_card_stab (hT7.partition.orbit 0) hc
    rw [hstab, hGxcard] at hh
    omega
  have hlen5A : Nat.card ↥(![orb3A a a, orb5A a a, orb5E a a] (1 : Fin 3)) = 1408 := by
    obtain ⟨c, hc⟩ := (hT7.partition.orbit 1).nonempty
    have hshape : IsShapeU35 ↥(Gxy a c) := hT7.shape_5A c hc
    have hstab : Nat.card ↥(Gx a ⊓ Gx c) = 126000 := by
      rw [← Gxy_eq_inf]
      exact hU.card_eq _ hshape
    have hh := IsConjOrbit.card_mul_card_stab (hT7.partition.orbit 1) hc
    rw [hstab, hGxcard] at hh
    omega
  have hsum5 : (∑ i : Fin 5, Nat.card ↥(tab5Set a z i)) = 1147575 := by
    rw [Fin.sum_univ_five, hlen0, hlen1, hlen2, hlen3, hlen4]
  have hsum3 : (∑ i : Fin 3, Nat.card ↥(![orb3A a a, orb5A a a, orb5E a a] i)) =
      35200 + 1408 + Nat.card ↥(orb5E a a) := by
    rw [Fin.sum_univ_three, hlen3A, hlen5A]
    rfl
  have hcardA : Nat.card ↥A = 1 + Nat.card ↥(tab5Base a) + Nat.card ↥(oddSet a a) := by
    change A.ncard = 1 + (tab5Base a).ncard + (oddSet a a).ncard
    rw [hA, Set.ncard_union_eq hdisj2, Set.ncard_union_eq hdisj1, Set.ncard_singleton]
  have hcardT5 : Nat.card ↥(tab5Base a) = ∑ i : Fin 5, Nat.card ↥(tab5Set a z i) :=
    IsOrbitPartition.card_eq_sum hT5.partition
  have hcardT7 : Nat.card ↥(oddSet a a) =
      ∑ i : Fin 3, Nat.card ↥(![orb3A a a, orb5A a a, orb5E a a] i) :=
    IsOrbitPartition.card_eq_sum hT7.partition
  have hmain : Nat.card ↥A = 1184184 + Nat.card ↥(orb5E a a) := by
    rw [hcardA, hcardT5, hsum5, hcardT7, hsum3]
    omega
  exact hmain

theorem card_eq_mul_of_gamma (hI : TwoHSInterface) (hU : U35Facts) [Finite G] {a z : G}
    (h : IsF5Type a z) (hGam : GammaFacts a z) (hT5 : TableVFacts a z) (hT7 : TableVIIFacts a z) :
    Nat.card G = 177408000 * (1184184 + Nat.card ↥(orb5E a a)) := by
  have hGxcard : Nat.card ↥(Gx a) = 177408000 := card_Gx_eq_of_isF5Type hI h
  have hclass := card_isConj_mul_card_centralizer (G := G) a
  have hcard := card_isConj_eq_of_gamma hI hU h hGam hT5 hT7
  rw [hcard, hGxcard] at hclass
  rw [← hclass]
  ring

theorem card_orb5E_mul_card_Gxy (hI : TwoHSInterface) [Finite G] {a z : G} (h : IsF5Type a z)
    (hT7 : TableVIIFacts a z) {x : G} (hx : x ∈ orb5E a a) :
    Nat.card ↥(orb5E a a) * Nat.card ↥(Gxy a x) = 177408000 := by
  have hGxcard : Nat.card ↥(Gx a) = 177408000 := card_Gx_eq_of_isF5Type hI h
  have hh := IsConjOrbit.card_mul_card_stab (hT7.partition.orbit 2) hx
  rw [hGxcard] at hh
  rw [Gxy_eq_inf]
  exact hh

theorem five_pow_four_dvd_card (hU : U35Facts) [Finite G] {a z : G} (h : IsF5Type a z)
    (hT7 : TableVIIFacts a z) : 5 ^ 4 ∣ Nat.card G := by
  obtain ⟨y, hy⟩ := (hT7.partition.orbit 1).nonempty
  have hay : y ∈ orb5A a a := hy
  have hconj : IsConj a y := hay.1.1
  have horder : orderOf (a * y) = 5 := hay.2.1
  have hshape : IsShapeU35 ↥(Gxy a y) := hT7.shape_5A y hay
  have hGxycard : Nat.card ↥(Gxy a y) = 126000 := hU.card_eq _ hshape
  have ha2 : a * a = 1 := mul_self_eq_one_of_orderOf_eq_two h.orderOf_a
  have hyorder : orderOf y = 2 := by
    obtain ⟨c, hc⟩ := hconj
    rw [← SemiconjBy.orderOf_eq (c : G) hc, h.orderOf_a]
  have hy2 : y * y = 1 := mul_self_eq_one_of_orderOf_eq_two hyorder
  have ha_inv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hy_inv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hinv : a * (a * y) * a = (a * y)⁻¹ := by
    rw [mul_inv_rev, ha_inv, hy_inv]
    calc a * (a * y) * a = (a * a) * (y * a) := by group
      _ = 1 * (y * a) := by rw [ha2]
      _ = y * a := by rw [one_mul]
  have hρodd : Odd (orderOf (a * y)) := by rw [horder]; norm_num
  have haL : ∀ l ∈ Gxy a y, l * a = a * l := fun l hl => (mem_Gx.mp (mem_Gxy.mp hl).1).symm
  have hρcomm : ∀ l ∈ Gxy a y, l * (a * y) = (a * y) * l := by
    intro l hl
    have hla : l * a = a * l := (mem_Gx.mp (mem_Gxy.mp hl).1).symm
    have hly : l * y = y * l := (mem_Gx.mp (mem_Gxy.mp hl).2).symm
    calc l * (a * y) = (l * a) * y := by rw [mul_assoc]
      _ = (a * l) * y := by rw [hla]
      _ = a * (l * y) := by rw [mul_assoc]
      _ = a * (y * l) := by rw [hly]
      _ = (a * y) * l := by rw [mul_assoc]
  have hcard_sup := card_sup_zpowers_of_inverted (L := Gxy a y) (a := a) (ρ := a * y)
      ha2 hinv hρodd hρcomm haL
  rw [hGxycard, horder] at hcard_sup
  have hdvd : Nat.card ↥(Gxy a y ⊔ Subgroup.zpowers (a * y)) ∣ Nat.card G :=
    Subgroup.card_subgroup_dvd_card _
  rw [hcard_sup] at hdvd
  exact dvd_trans (by norm_num : 5 ^ 4 ∣ 126000 * 5) hdvd

theorem card_Gxy_eq_of_orb5E (hI : TwoHSInterface) (hU : U35Facts) [Finite G] {a z : G}
    (h : IsF5Type a z) (hGam : GammaFacts a z) (hT5 : TableVFacts a z) (hT7 : TableVIIFacts a z)
    {x : G} (hx : x ∈ orb5E a a) (hdvd : Nat.card ↥(Gxy a x) ∣ 2500)
    (h20 : 20 ∣ Nat.card ↥(Gxy a x)) (hle : Nat.card ↥(Gxy a x) ≤ 500) :
    Nat.card ↥(Gxy a x) = 500 := by
  set s := Nat.card ↥(Gxy a x) with hs
  set n := Nat.card ↥(orb5E a a) with hn
  have heq1 : n * s = 177408000 := by
    rw [hs, hn]
    exact card_orb5E_mul_card_Gxy hI h hT7 hx
  have heq2 : Nat.card G = 177408000 * (1184184 + n) := by
    rw [hn]
    exact card_eq_mul_of_gamma hI hU h hGam hT5 hT7
  have h54 : 5 ^ 4 ∣ Nat.card G := five_pow_four_dvd_card hU h hT7
  obtain ⟨k, hk⟩ := h20
  have hk_le : k ≤ 25 := by omega
  have hk_dvd : k ∣ 125 := by
    rw [hk, show (2500 : ℕ) = 20 * 125 by norm_num] at hdvd
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 20)).mp hdvd
  have hk5 : k ∣ 5 ^ 3 := by
    rw [show (5 : ℕ) ^ 3 = 125 by norm_num]
    exact hk_dvd
  obtain ⟨i, _hi, hik⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hk5
  rw [hik] at hk hk_le
  interval_cases i
  · norm_num at hk
    rw [hk] at heq1
    exfalso
    have hn' : n = 8870400 := by omega
    rw [hn'] at heq2
    rw [heq2] at h54
    exact absurd h54 (by decide)
  · norm_num at hk
    rw [hk] at heq1
    exfalso
    have hn' : n = 1774080 := by omega
    rw [hn'] at heq2
    rw [heq2] at h54
    exact absurd h54 (by decide)
  · norm_num at hk
    omega
  · exact absurd hk_le (by norm_num)

theorem card_eq_of_isShapeFiveCubeByTwoTwo {X : Type*} [Group X] (h : IsShapeFiveCubeByTwoTwo X) :
    Nat.card X = 500 := by
  obtain ⟨N, hN, _hp, hNcard, ⟨e⟩⟩ := h
  haveI := hN
  have hquot : Nat.card (X ⧸ N) = 4 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Elem2 2) = 4
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    norm_num
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hquot, hNcard]
  norm_num

end CFSG.EvenSporadicStandard.HNRecog.Section3
