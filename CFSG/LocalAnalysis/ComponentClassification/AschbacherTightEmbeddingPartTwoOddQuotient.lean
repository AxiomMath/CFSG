module

import CFSG.LocalAnalysis.ComponentClassification.TightEmbeddingMap
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingPartTwoData
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionOddQuotientLifting

public section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.ShultStronglyClosedTI

variable {G K : Type*} [Group G] [Finite G] [Group K] [Finite K]

omit [Finite G] [Finite K] in
theorem right_conjugate_map (f : G →* K) (Q : Subgroup G) (g : G) :
    (rightConjugate Q g).map f = rightConjugate (Q.map f) (f g) := by
  unfold rightConjugate
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  change f (g⁻¹ * x * (g⁻¹)⁻¹) = (f g)⁻¹ * f x * ((f g)⁻¹)⁻¹
  simp only [map_mul, map_inv]

omit [Finite K] in
theorem involution_mem_Q_of_odd_kernel_image (f : G →* K)
    (hkerodd : Odd (Nat.card f.ker)) (Q : Subgroup G)
    (hker : f.ker ≤ Subgroup.normalizer (Q : Set G))
    (x : G) (hx : orderOf x = 2) (himage : f x ∈ Q.map f) : x ∈ Q := by
  have hxI : IsInvolution x :=
    ⟨(orderOf_eq_prime_iff.mp hx).2, (orderOf_eq_prime_iff.mp hx).1⟩
  obtain ⟨t, htQ, ht, hft⟩ := involution_lift_in_subgroup_of_odd_kernel f hkerodd Q
    (involution_image_of_odd_kernel f hkerodd hxI) himage
  obtain ⟨n, hnker, hn⟩ := involutions_kernel_conjugate f hkerodd hxI ht hft.symm
  have hnH := hker hnker
  have hxconjQ : n⁻¹ * x * (n⁻¹)⁻¹ ∈ Q := by
    have hxright : rightConjugateElem x n ∈ Q := by
      rw [hn]
      exact htQ
    simpa only [rightConjugateElem, inv_inv] using hxright
  have hxQ := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hnH) x).mpr
    hxconjQ
  exact hxQ

omit [Finite K] in
theorem odd_kernel_normalizer_map (f : G →* K) (hf : Function.Surjective f)
    (hkerodd : Odd (Nat.card f.ker)) (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hker : f.ker ≤ Subgroup.normalizer (Q : Set G)) :
    (Subgroup.normalizer (Q : Set G)).map f =
      Subgroup.normalizer (Q.map f : Set K) := by
  apply le_antisymm (Subgroup.le_normalizer_map f)
  intro k hk
  obtain ⟨g, rfl⟩ := hf k
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Q) 2
    (even_iff_two_dvd.mp htight.1)
  have hzG : orderOf (z : G) = 2 := (Subgroup.orderOf_coe z).trans hz
  have himage : f (g⁻¹ * (z : G) * g) ∈ Q.map f := by
    have hzimage := Subgroup.mem_map_of_mem f z.property
    have hmem := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer _).inv_mem hk) (f (z : G))).mp hzimage
    simpa only [inv_inv, map_mul, map_inv] using hmem
  have hconjorder : orderOf (g⁻¹ * (z : G) * g) = 2 := by
    simpa only [MulAut.conj_apply, inv_inv] using
      ((MulAut.conj g⁻¹).orderOf_eq (z : G)).trans hzG
  have hconjQ := involution_mem_Q_of_odd_kernel_image f hkerodd Q hker
    (g⁻¹ * (z : G) * g) hconjorder himage
  exact Subgroup.mem_map_of_mem f
    ((involution_conjugate_mem_Q_iff Q hodd z z.property hzG g).mp hconjQ)

omit [Finite K] in
theorem odd_kernel_normalizer_preimage (f : G →* K) (hf : Function.Surjective f)
    (hkerodd : Odd (Nat.card f.ker)) (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hker : f.ker ≤ Subgroup.normalizer (Q : Set G)) :
    (Subgroup.normalizer (Q.map f : Set K)).comap f =
      Subgroup.normalizer (Q : Set G) := by
  rw [← odd_kernel_normalizer_map f hf hkerodd Q htight hodd hker,
    Subgroup.comap_map_eq_self hker]

theorem odd_normalizer_overlaps_image (f : G →* K) (hf : Function.Surjective f)
    (hkerodd : Odd (Nat.card f.ker)) (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hker : f.ker ≤ Subgroup.normalizer (Q : Set G)) :
    OddNormalizerOverlaps (Q.map f) := by
  intro k hk
  obtain ⟨g, rfl⟩ := hf k
  have hg : g ∉ Subgroup.normalizer (Q : Set G) := by
    intro hg
    apply hk
    rw [← odd_kernel_normalizer_map f hf hkerodd Q htight hodd hker]
    exact Subgroup.mem_map_of_mem f hg
  apply Nat.not_even_iff_odd.mp
  intro heven
  let I := rightConjugate (Q.map f) (f g) ⊓ Subgroup.normalizer (Q.map f : Set K)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := I) 2
    (even_iff_two_dvd.mp heven)
  have hyorder : orderOf (y : K) = 2 := (Subgroup.orderOf_coe y).trans hy
  have hyI : IsInvolution (y : K) :=
    ⟨(orderOf_eq_prime_iff.mp hyorder).2, (orderOf_eq_prime_iff.mp hyorder).1⟩
  have hyimage : (y : K) ∈ (rightConjugate Q g).map f := by
    rw [right_conjugate_map]
    exact y.property.1
  obtain ⟨x, hxright, hx, hfx⟩ := involution_lift_in_subgroup_of_odd_kernel f hkerodd
    (rightConjugate Q g) hyI hyimage
  have hxH : x ∈ Subgroup.normalizer (Q : Set G) := by
    have hxpre : x ∈ (Subgroup.normalizer (Q.map f : Set K)).comap f := by
      change f x ∈ Subgroup.normalizer (Q.map f : Set K)
      rw [hfx]
      exact y.property.2
    rwa [odd_kernel_normalizer_preimage f hf hkerodd Q htight hodd hker] at hxpre
  have hxorder : orderOf x = 2 := orderOf_eq_prime hx.sq_eq_one hx.ne_one
  exact (hodd g hg).not_two_dvd_nat
    (hxorder ▸ Subgroup.orderOf_dvd_natCard
      (rightConjugate Q g ⊓ Subgroup.normalizer (Q : Set G)) ⟨hxright, hxH⟩)

omit [Finite K] in
theorem tightly_embedded_image_of_odd_kernel (f : G →* K) (hf : Function.Surjective f)
    (hkerodd : Odd (Nat.card f.ker)) (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (_hodd : OddNormalizerOverlaps Q)
    (_hker : f.ker ≤ Subgroup.normalizer (Q : Set G)) :
    TightlyEmbedded (Q.map f) :=
  RankTwoBender.tightlyEmbedded_map_of_odd_ker f hf hkerodd htight

omit [Finite K] in
theorem normality_iff_odd_kernel_image (f : G →* K) (hf : Function.Surjective f)
    (hkerodd : Odd (Nat.card f.ker)) (Q : Subgroup G)
    (htight : TightlyEmbedded Q) (hodd : OddNormalizerOverlaps Q)
    (hker : f.ker ≤ Subgroup.normalizer (Q : Set G)) :
    Q.Normal ↔ (Q.map f).Normal := by
  constructor
  · intro hnormal
    exact hnormal.map f hf
  · intro hnormal
    have htop : Subgroup.normalizer (Q.map f : Set K) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hnormal
    have hpre := odd_kernel_normalizer_preimage f hf hkerodd Q htight hodd hker
    rw [htop, Subgroup.comap_top] at hpre
    exact Subgroup.normalizer_eq_top_iff.mp hpre.symm

end CFSG.ComponentClassification.AschbacherTightEmbedding
