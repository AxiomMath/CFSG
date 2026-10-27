module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.PerpProof.PerpBasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fusion3.Conj
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.SuborbitFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Vert

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z p : G}

private theorem lines_orderOf_mul_two {u t : G} (hu : orderOf u = 2) (ht : orderOf t = 2)
    (hcomm : u * t = t * u) (hne : u * t ≠ 1) : orderOf (u * t) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ hne
  have hu2 : u ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hu]
  have ht2 : t ^ 2 = 1 := by rw [← pow_orderOf_eq_one, ht]
  calc (u * t) ^ 2 = u ^ 2 * t ^ 2 := (show Commute u t from hcomm).mul_pow 2
    _ = 1 := by rw [hu2, ht2, one_mul]

theorem lines_mul_isConj_or (h : IsF5Type a z) (hT5 : TableVFacts p z) (hp : IsConj a p)
    {t : G} (ht : IsConj a t) (hpt : orderOf (p * t) = 2) :
    IsConj a (p * t) ∨ IsConj z (p * t) := by
  have ht5 : t ∈ tab5Base p := ⟨hp.symm.trans ht, by rw [hpt]; norm_num⟩
  obtain ⟨i, hi⟩ := hT5.partition.cover t ht5
  have hsq : (p * t) ^ 2 = 1 := by simpa [hpt] using pow_orderOf_eq_one (p * t)
  fin_cases i
  · have hc : t ∈ orb2A p p := hi
    exact Or.inl (hp.trans hc.2)
  · have hc : t ∈ orb2B p z p := hi
    exact Or.inr hc.2
  · have hc : t ∈ orb4A p z p := hi
    exfalso
    have hz1 : z = 1 := by
      have h : IsConj z (1 : G) := by simpa [hsq] using hc.2
      exact isConj_one_right.mp (IsConj.symm h)
    have hzord := h.orderOf_z
    rw [hz1, orderOf_one] at hzord
    norm_num at hzord
  · have hc : t ∈ orb4B p p := hi
    exfalso
    have hp1 : p = 1 := by
      have h : IsConj p (1 : G) := by simpa [hsq] using hc.2
      exact isConj_one_right.mp (IsConj.symm h)
    have hpord : orderOf p = 2 := perp_orderOf_of_isConj_a h hp
    rw [hp1, orderOf_one] at hpord
    norm_num at hpord
  · have hc : t ∈ orb6A p p := hi
    have h6 : orderOf (p * t) = 6 := hc.2.1
    omega

theorem lines_not_twoA_of_five (h : IsF5Type a z) (hT4 : TableIVFacts a z) {x t : G}
    (hx : IsConj a x) (hord : orderOf (a * x) = 5) (ht : t ∈ orb2A a a ∩ orb2A a x) : False := by
  have hta : IsConj a t := ht.1.1
  have hxtA : IsConj a (x * t) := ht.2.2
  have hx2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hx
  have ht2 : orderOf t = 2 := perp_orderOf_of_isConj_a h hta
  have haa : a * a = 1 := by
    have h' : a ^ 2 = 1 := by rw [← pow_orderOf_eq_one, h.orderOf_a]
    simpa [pow_two] using h'
  have hxx : x * x = 1 := by
    have h' : x ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hx2]
    simpa [pow_two] using h'
  have htt : t * t = 1 := by
    have h' : t ^ 2 = 1 := by rw [← pow_orderOf_eq_one, ht2]
    simpa [pow_two] using h'
  have hx_pow : x ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hx2]
  have ht_pow : t ^ 2 = 1 := by rw [← pow_orderOf_eq_one, ht2]
  have hxt_pow : (x * t) ^ 2 = 1 := by
    have h' : orderOf (x * t) = 2 := perp_orderOf_of_isConj_a h hxtA
    simpa [h'] using pow_orderOf_eq_one (x * t)
  have hcomm : x * t = t * x := comm_of_sq_mul hx_pow ht_pow hxt_pow
  have hatx : IsConj a (t * x) := by rw [hcomm] at hxtA; exact hxtA
  have hxa : x ≠ a := by
    intro h_eq
    rw [h_eq] at hord
    rw [haa, orderOf_one] at hord
    norm_num at hord
  have hxat : x ≠ a * t := by
    intro h_eq
    rw [h_eq] at hord
    have haat : a * (a * t) = t := by
      calc a * (a * t) = (a * a) * t := (mul_assoc a a t).symm
        _ = 1 * t := by rw [haa]
        _ = t := one_mul t
    rw [haat, ht2] at hord
    norm_num at hord
  have hxS : x ∈ sBase a t := ⟨hx, hatx, hxa, hxat⟩
  obtain ⟨i, hi⟩ := (hT4.partition t ht.1).cover x hxS
  fin_cases i
  · have hc : x ∈ sBase a t ∧ IsConj a (a * x) := hi
    have h2 : orderOf (a * x) = 2 := perp_orderOf_of_isConj_a h hc.2
    omega
  · have hc : x ∈ sBase a t ∧ IsConj z (a * x) := hi
    have h2 : orderOf (a * x) = 2 := perp_orderOf_of_isConj_z h hc.2
    omega
  · obtain ⟨h2, -⟩ := perp_orderOf_row_two h hta hi
    omega
  · obtain ⟨h2, -⟩ := perp_orderOf_row_three h hi
    omega
  · have h2 := perp_orderOf_row_four hi
    omega
  · obtain ⟨h2, -⟩ := perp_orderOf_row_five h hta hi
    omega

theorem lines_five_A (hU : U35Facts) (h : IsF5Type a z) (hnc : ¬ IsConj a z)
    (hPar : ParityFacts a z) (hT4 : TableIVFacts a z) (hT5 : Vert TableVFacts a z)
    (hT7 : TableVIIFacts a z) {x : G} (hx : x ∈ orb5A a a) :
    IsConjOrbit (Gxy a x) {t | t ∈ Gxy a x ∧ orderOf t = 2} ∧
      {t | t ∈ Gxy a x ∧ orderOf t = 2} = orb2B a z a ∩ orb2B a z x := by
  have hx' : x ∈ oddSet a a ∧ orderOf (a * x) = 5 ∧
      (∀ t : G, IsConj a t → t ∈ Gxy a x →
        IsNonsplitDoubleCoverOfS5 ↥(Gxyz a t x)) := hx
  obtain ⟨hxodd, hxord, _hxrest⟩ := hx'
  have hxA : IsConj a x := hxodd.1
  obtain ⟨t₀, ht₀A, ht₀G⟩ := hxodd.2.2.2
  have ht₀ord : orderOf t₀ = 2 := perp_orderOf_of_isConj_a h ht₀A
  have ha2 : a ^ 2 = 1 := by rw [← pow_orderOf_eq_one, h.orderOf_a]
  have hxx2 : orderOf x = 2 := perp_orderOf_of_isConj_a h hxA
  have hx2 : x ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hxx2]
  have hX : IsShapeU35 ↥(Gxy a x) := hT7.shape_5A x hx
  have hax_ne : a * x ≠ x * a := by
    intro hcomm
    have hsq : (a * x) ^ 2 = 1 := by
      calc (a * x) ^ 2 = a ^ 2 * x ^ 2 := (show Commute a x from hcomm).mul_pow 2
        _ = 1 := by rw [ha2, hx2, one_mul]
    have hdvd : orderOf (a * x) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hsq
    rw [hxord] at hdvd
    norm_num at hdvd
  have hsq_of : ∀ c (hcK : c ∈ Gxy a x), orderOf c = 2 →
      (⟨c, hcK⟩ : ↥(Gxy a x)) ^ 2 = 1 := by
    intro c hcK hc2
    have h' : c ^ 2 = 1 := by rw [← pow_orderOf_eq_one, hc2]
    apply Subtype.ext
    simpa using h'
  have hne_of : ∀ c (hcK : c ∈ Gxy a x), orderOf c = 2 →
      (⟨c, hcK⟩ : ↥(Gxy a x)) ≠ 1 := by
    intro c hcK hc2 h1
    have hc1 : c = 1 := by simpa using congrArg Subtype.val h1
    rw [hc1, orderOf_one] at hc2
    norm_num at hc2
  have hconj_X : ∀ c (hcK : c ∈ Gxy a x), orderOf c = 2 →
      IsConj (⟨c, hcK⟩ : ↥(Gxy a x)) (⟨t₀, ht₀G⟩ : ↥(Gxy a x)) := by
    intro c hcK hc2
    exact hU.one_class ↥(Gxy a x) hX ⟨c, hcK⟩ ⟨t₀, ht₀G⟩ (hsq_of c hcK hc2)
      (hsq_of t₀ ht₀G ht₀ord) (hne_of c hcK hc2) (hne_of t₀ ht₀G ht₀ord)
  have hconj_G : ∀ c (hcK : c ∈ Gxy a x), orderOf c = 2 → IsConj c t₀ := by
    intro c hcK hc2
    have h := MonoidHom.map_isConj (Subgroup.subtype (Gxy a x)) (hconj_X c hcK hc2)
    simpa using h
  have hAt_of : ∀ c (hcK : c ∈ Gxy a x), orderOf c = 2 → IsConj a c := by
    intro c hcK hc2
    exact ht₀A.trans (IsConj.symm (hconj_G c hcK hc2))
  have hne_a : ∀ t (htK : t ∈ Gxy a x), a * t ≠ 1 := by
    intro t htK h
    have ht_eq_a : t = a := by
      have h1 := congrArg (fun y => a * y) h
      simp only [mul_one] at h1
      rw [← mul_assoc, show a * a = 1 by simpa [pow_two] using ha2, one_mul] at h1
      exact h1
    have ha_mem : a ∈ Gxy a x := ht_eq_a ▸ htK
    exact hax_ne (mem_Gx.mp (mem_Gxy.mp ha_mem).2).symm
  have hne_x : ∀ t (htK : t ∈ Gxy a x), x * t ≠ 1 := by
    intro t htK h
    have ht_eq_x : t = x := by
      have h1 := congrArg (fun y => x * y) h
      simp only [mul_one] at h1
      rw [← mul_assoc, show x * x = 1 by simpa [pow_two] using hx2, one_mul] at h1
      exact h1
    have hx_mem : x ∈ Gxy a x := ht_eq_x ▸ htK
    exact hax_ne (mem_Gx.mp (mem_Gxy.mp hx_mem).1)
  refine ⟨⟨?_, ⟨t₀, ht₀G, ht₀ord⟩, ?_⟩, ?_⟩
  · intro k hk c hc
    obtain ⟨hcK, hc2⟩ := hc
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hcK) (Subgroup.inv_mem _ hk), ?_⟩
    have h := MulEquiv.orderOf_eq (MulAut.conj k) c
    rw [MulAut.conj_apply] at h
    rw [h, hc2]
  · intro c hc c' hc'
    obtain ⟨hcK, hc2⟩ := hc
    obtain ⟨hc'K, hc'2⟩ := hc'
    have hic : IsConj (⟨c, hcK⟩ : ↥(Gxy a x)) (⟨c', hc'K⟩ : ↥(Gxy a x)) :=
      hU.one_class ↥(Gxy a x) hX ⟨c, hcK⟩ ⟨c', hc'K⟩ (hsq_of c hcK hc2)
        (hsq_of c' hc'K hc'2) (hne_of c hcK hc2) (hne_of c' hc'K hc'2)
    obtain ⟨k, hk⟩ := isConj_iff.mp hic
    exact ⟨(k : G), k.2, by simpa using congrArg Subtype.val hk⟩
  · ext t
    constructor
    · intro ht
      obtain ⟨htK, ht2⟩ := ht
      have hAt : IsConj a t := hAt_of t htK ht2
      have hcomm_at : a * t = t * a := mem_Gx.mp (mem_Gxy.mp htK).1
      have hcomm_xt : x * t = t * x := mem_Gx.mp (mem_Gxy.mp htK).2
      have hpt2a : orderOf (a * t) = 2 :=
        lines_orderOf_mul_two h.orderOf_a ht2 hcomm_at (hne_a t htK)
      have hpt2x : orderOf (x * t) = 2 :=
        lines_orderOf_mul_two hxx2 ht2 hcomm_xt (hne_x t htK)
      have hconj_at_xt : IsConj (a * t) (x * t) := by
        by_contra hh
        have hev := hPar.even_of_not_conj x t hxA ht2 htK hh
        rw [hxord] at hev
        obtain ⟨k, hk⟩ := hev
        omega
      have haxt_B : IsConj z (a * t) := by
        rcases lines_mul_isConj_or h (hT5 a z (IsConj.refl a) (IsConj.refl z))
          (IsConj.refl a) hAt hpt2a with hh | hh
        · exfalso
          exact lines_not_twoA_of_five h hT4 hxA hxord
            ⟨⟨hAt, hh⟩, ⟨hAt, hh.trans hconj_at_xt⟩⟩
        · exact hh
      have hxt_B : IsConj z (x * t) := by
        rcases lines_mul_isConj_or h (hT5 x z hxA (IsConj.refl z))
          hxA hAt hpt2x with hh | hh
        · exfalso
          exact lines_not_twoA_of_five h hT4 hxA hxord
            ⟨⟨hAt, hh.trans hconj_at_xt.symm⟩, ⟨hAt, hh⟩⟩
        · exact hh
      exact ⟨⟨hAt, haxt_B⟩, ⟨hAt, hxt_B⟩⟩
    · intro ht
      obtain ⟨ht1, ht2⟩ := ht
      have hAt : IsConj a t := ht1.1
      have haxt : IsConj z (a * t) := ht1.2
      have hxt : IsConj z (x * t) := ht2.2
      have htord : orderOf t = 2 := perp_orderOf_of_isConj_a h hAt
      have ht_pow : t ^ 2 = 1 := by rw [← pow_orderOf_eq_one, htord]
      have haxt_ord : orderOf (a * t) = 2 := perp_orderOf_of_isConj_z h haxt
      have hxt_ord : orderOf (x * t) = 2 := perp_orderOf_of_isConj_z h hxt
      have haxt_pow : (a * t) ^ 2 = 1 := by
        simpa [haxt_ord] using pow_orderOf_eq_one (a * t)
      have hxt_pow : (x * t) ^ 2 = 1 := by
        simpa [hxt_ord] using pow_orderOf_eq_one (x * t)
      have hcomm_at : a * t = t * a := comm_of_sq_mul ha2 ht_pow haxt_pow
      have hcomm_xt : x * t = t * x := comm_of_sq_mul hx2 ht_pow hxt_pow
      exact ⟨mem_Gxy.mpr ⟨mem_Gx.mpr hcomm_at, mem_Gx.mpr hcomm_xt⟩, htord⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
