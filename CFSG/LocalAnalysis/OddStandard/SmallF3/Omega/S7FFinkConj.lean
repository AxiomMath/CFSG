module

public import CFSG.LocalAnalysis.ComponentInitial.GroupComponents
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (mem_conj_iff
  eq_of_orderOf_eq_two_of_isCyclic)

variable {G : Type} [Group G]

theorem s7f_not_mem_of_mem_conj [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) {g u : G}
    (hg : g ∉ normalizer (L : Set G))
    (hu : u ∈ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom) (hu2 : orderOf u = 2) :
    u ∉ centralizer (L : Set G) := by
  intro huC
  obtain ⟨-, -, hodd, hNC, -⟩ := hL
  have hgC : g ∉ normalizer (centralizer (L : Set G) : Set G) := by rwa [hNC]
  have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨huC, hu⟩)
  rw [hu2] at hdvd
  exact (Nat.not_even_iff_odd.mpr (hodd g hgC)) (even_iff_two_dvd.mpr hdvd)

theorem s7f_conj_eq_of_involutions [Finite G] {C : Subgroup G}
    (hcyc : ∀ P : Sylow 2 ↥C, IsCyclic (P : Subgroup ↥C)) {w t : G} (hw : w ∈ C)
    (hw2 : orderOf w = 2) (ht : t ∈ C) (ht2 : orderOf t = 2) :
    ∃ d ∈ C, d * w * d⁻¹ = t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htp : IsPGroup 2 (zpowers (⟨t, ht⟩ : ↥C)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, ht2, pow_one])
  obtain ⟨P, hP⟩ := htp.exists_le_sylow
  have hwp : IsPGroup 2 (zpowers w) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw2, pow_one])
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_conj_mem_sylow
    ((zpowers_le (G := G)).mpr hw) hwp P
  have hcw : c⁻¹ * ⟨w, hw⟩ * c ∈ (P : Subgroup ↥C) := hc ⟨w, hw⟩ (mem_zpowers w)
  have htP : (⟨t, ht⟩ : ↥C) ∈ (P : Subgroup ↥C) := hP (mem_zpowers _)
  have hord : orderOf (c⁻¹ * ⟨w, hw⟩ * c) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj c⁻¹) (⟨w, hw⟩ : ↥C)
    rw [MulAut.conj_apply, inv_inv] at h
    rw [h, Subgroup.orderOf_mk, hw2]
  have heq := eq_of_orderOf_eq_two_of_isCyclic (hcyc P) hcw htP hord
    (by rw [Subgroup.orderOf_mk, ht2])
  refine ⟨(c : G)⁻¹, inv_mem c.2, ?_⟩
  have h := congrArg Subtype.val heq
  simpa [mul_assoc] using h

theorem s7f_exists_conj_commute [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hcyc : ∀ P : Sylow 2 ↥(centralizer (L : Set G)),
      IsCyclic (P : Subgroup ↥(centralizer (L : Set G))))
    {t x : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hxC : x ∈ centralizer (L : Set G)) (hxp : IsPGroup 2 (zpowers x)) {g' : G}
    (hg' : g' ∉ normalizer (L : Set G)) {R T : Subgroup G} (hRC : R ≤ centralizer (L : Set G))
    (hRcard : Nat.card R = 2 ^ (Nat.card (centralizer (L : Set G))).factorization 2)
    (hTg : T ≤ (centralizer (L : Set G)).map (MulAut.conj g').toMonoidHom)
    (hT2 : 2 ∣ Nat.card T) (hRT : R ≤ centralizer (T : Set G)) :
    ∃ h : G, h⁻¹ * t * h ≠ t ∧ x * (h⁻¹ * t * h) = (h⁻¹ * t * h) * x := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR'card : Nat.card (R.subgroupOf (centralizer (L : Set G))) =
      2 ^ (Nat.card (centralizer (L : Set G))).factorization 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC).toEquiv).trans hRcard
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.ComponentInitial.exists_conj_mem_sylow
    ((zpowers_le (G := G)).mpr hxC) hxp (Sylow.ofCard _ hR'card)
  have hxR : (c : G)⁻¹ * x * c ∈ R := by
    have h : c⁻¹ * ⟨x, hxC⟩ * c ∈ R.subgroupOf (centralizer (L : Set G)) :=
      hc ⟨x, hxC⟩ (mem_zpowers x)
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 hT2
  have hu2 : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe, hu]
  have huC : (u : G) ∈ (centralizer (L : Set G)).map (MulAut.conj g').toMonoidHom := hTg u.2
  have hwC : g'⁻¹ * (u : G) * g' ∈ centralizer (L : Set G) := mem_conj_iff.mp huC
  have hw2 : orderOf (g'⁻¹ * (u : G) * g') = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g'⁻¹) (u : G)
    rwa [MulAut.conj_apply, inv_inv, hu2] at h
  obtain ⟨d, -, hd⟩ := s7f_conj_eq_of_involutions hcyc hwC hw2 htC ht
  have hconj : ((c : G) * g' * d⁻¹) * t * ((c : G) * g' * d⁻¹)⁻¹ = (c : G) * u * (c : G)⁻¹ := by
    rw [← hd]
    group
  refine ⟨((c : G) * g' * d⁻¹)⁻¹, ?_, ?_⟩
  · rw [inv_inv, hconj]
    intro heq
    apply s7f_not_mem_of_mem_conj hL hg' huC hu2
    have hu' : (u : G) = (c : G)⁻¹ * t * c := by
      rw [← heq]
      group
    rw [hu']
    exact mul_mem (mul_mem (inv_mem c.2) htC) c.2
  · rw [inv_inv, hconj]
    have hcomm := mem_centralizer_iff.mp (hRT hxR) u u.2
    calc x * ((c : G) * u * (c : G)⁻¹) = (c : G) * ((c : G)⁻¹ * x * c * u) * (c : G)⁻¹ := by
          group
      _ = (c : G) * (u * ((c : G)⁻¹ * x * c)) * (c : G)⁻¹ := by rw [← hcomm]
      _ = ((c : G) * u * (c : G)⁻¹) * x := by group

end CFSG.OddStandard.SmallF3.Omega
