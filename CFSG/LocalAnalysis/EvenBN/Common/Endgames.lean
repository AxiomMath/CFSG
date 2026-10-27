module

public import CFSG.LocalAnalysis.SteinbergBNFirstTransferData
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

variable {G : Type*} [Group G]

theorem eq_of_mul_self_eq_one_of_isCyclic {Q : Type*} [Group Q] [Finite Q] [IsCyclic Q] {u v : Q}
    (hu : u ≠ 1) (hv : v ≠ 1) (hu2 : u * u = 1) (hv2 : v * v = 1) : u = v := by
  classical
  have := Fintype.ofFinite Q
  by_contra huv
  have hle := IsCyclic.card_pow_eq_one_le (α := Q) (n := 2) two_pos
  have hsub : ({1, u, v} : Finset Q) ⊆ Finset.univ.filter (fun a => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq]
      exact hu2
    · rw [sq]
      exact hv2
  have h3 : ({1, u, v} : Finset Q).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair huv]
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hu, Ne.symm hv⟩
  have h4 := Finset.card_le_card hsub
  omega

theorem firstTransferData_of_forall_conj_mem {S N : Subgroup G} {x : G}
    (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (hNS : N ≤ S) [hN : (N.subgroupOf S).Normal]
    (hab : IsMulCommutative (S ⧸ N.subgroupOf S)) (hx : x ∈ S) (hxN : x ∉ N)
    (hx2 : orderOf x = 2) (hfus : ∀ g : G, g⁻¹ * x * g ∈ S → x⁻¹ * (g⁻¹ * x * g) ∈ N) :
    FirstTransferData S N x := by
  refine ⟨hS, hNS, hN, hab, hx, hxN, hx2, fun g hg => ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  have h := N.inv_mem (hfus g hg)
  rw [mul_inv_rev, inv_inv] at h
  exact h

theorem firstTransferData_of_isCyclic [Finite G] {S N : Subgroup G} {x : G}
    (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (hNS : N ≤ S) [(N.subgroupOf S).Normal]
    (hcyc : IsCyclic (S ⧸ N.subgroupOf S)) (hx : x ∈ S) (hxN : x ∉ N) (hx2 : orderOf x = 2)
    (hfus : ∀ g : G, g⁻¹ * x * g ∉ N) : FirstTransferData S N x := by
  have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
  refine firstTransferData_of_forall_conj_mem hS hNS inferInstance hx hxN hx2 fun g hg => ?_
  set u : S ⧸ N.subgroupOf S := QuotientGroup.mk ⟨g⁻¹ * x * g, hg⟩ with hu
  set v : S ⧸ N.subgroupOf S := QuotientGroup.mk ⟨x, hx⟩ with hv
  have hu1 : u ≠ 1 := by
    rw [hu, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hfus g
  have hv1 : v ≠ 1 := by
    rw [hv, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hxN
  have hu2 : u * u = 1 := by
    rw [hu, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have e : ((⟨g⁻¹ * x * g, hg⟩ * ⟨g⁻¹ * x * g, hg⟩ : S) : G) = 1 := by
      change g⁻¹ * x * g * (g⁻¹ * x * g) = 1
      calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
        _ = 1 := by rw [hxx]; group
    rw [e]
    exact N.one_mem
  have hv2 : v * v = 1 := by
    rw [hv, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
    change x * x ∈ N
    rw [hxx]
    exact N.one_mem
  have huv := eq_of_mul_self_eq_one_of_isCyclic hu1 hv1 hu2 hv2
  rw [hu, hv, QuotientGroup.eq, mem_subgroupOf] at huv
  have h := N.inv_mem huv
  simpa [mul_assoc] using h

theorem firstTransferData_of_relIndex_eq_two [Finite G] {S N : Subgroup G} {x : G}
    (hS : ∃ P : Sylow 2 G, (P : Subgroup G) = S) (hNS : N ≤ S) (hidx : N.relIndex S = 2)
    (hx : x ∈ S) (hxN : x ∉ N) (hx2 : orderOf x = 2) (hfus : ∀ g : G, g⁻¹ * x * g ∉ N) :
    FirstTransferData S N x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx' : (N.subgroupOf S).index = 2 := hidx
  have : (N.subgroupOf S).Normal := normal_of_index_eq_two hidx'
  have hcyc : IsCyclic (S ⧸ N.subgroupOf S) := isCyclic_of_prime_card (p := 2) hidx'
  exact firstTransferData_of_isCyclic hS hNS hcyc hx hxN hx2 hfus

theorem exists_sylow_eq_of_isSylowOf_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime]
    {B H : Subgroup G} (hB : IsSylowOf p B H) (hN : normalizer (B : Set G) ≤ H) :
    ∃ P : Sylow p G, (P : Subgroup G) = B := by
  obtain ⟨-, hBp, hdvd⟩ := isSylowOf_iff.mp hB
  have hindex : ¬ p ∣ B.index := by
    intro hpi
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hBp
    have hG : p ^ (n + 1) ∣ Nat.card G := by
      rw [← card_mul_index B, hn, pow_succ]
      exact Nat.mul_dvd_mul_left _ hpi
    have h1 := Sylow.prime_dvd_card_quotient_normalizer hG hn
    have h2 : p ∣ B.relIndex (normalizer (B : Set G)) := h1
    apply hdvd
    rw [← relIndex_mul_relIndex B (normalizer (B : Set G)) H le_normalizer hN]
    exact h2.mul_right _
  exact ⟨hBp.toSylow hindex, IsPGroup.toSylow_coe hBp hindex⟩

theorem normalizer_le_normalizer_closure_involutions (B : Subgroup G) (t : G) :
    normalizer (B : Set G) ≤
      normalizer (closure {x | x ∈ B ∧ orderOf x = 2 ∧ ∀ g : G, g⁻¹ * t * g ≠ x} : Set G) := by
  refine le_normalizer_closure_iff.mpr fun n hn x ⟨hxB, hx2, hxt⟩ =>
    subset_closure ⟨?_, ?_, fun g hg => ?_⟩
  · exact (mem_normalizer_iff.mp hn x).mp hxB
  · have h := MulEquiv.orderOf_eq (MulAut.conj n) x
    rw [MulAut.conj_apply] at h
    rw [h, hx2]
  · apply hxt (g * n)
    calc (g * n)⁻¹ * t * (g * n) = n⁻¹ * (g⁻¹ * t * g) * n := by group
      _ = x := by rw [hg]; group

theorem closure_involutions_eq [Finite G] {B P : Subgroup G} {t : G} (hPB : P ≤ B)
    [(P.subgroupOf B).Normal] (hcyc : IsCyclic (B ⧸ P.subgroupOf B)) (htB : t ∈ B)
    (htP : t ∉ P) (ht : orderOf t = 2) (hfus : ∀ g : G, g⁻¹ * t * g ∉ P)
    (hcoset : ∀ y ∈ P, orderOf (t * y) = 2 → ∃ m ∈ P, t * y = m⁻¹ * t * m)
    (hgen : P ≤ closure {x | x ∈ P ∧ orderOf x = 2}) :
    closure {x | x ∈ B ∧ orderOf x = 2 ∧ ∀ g : G, g⁻¹ * t * g ≠ x} = P := by
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  apply le_antisymm
  · rw [closure_le]
    rintro x ⟨hxB, hx2, hxt⟩
    by_contra hxP
    have hxx : x * x = 1 := by rw [← sq, ← hx2, pow_orderOf_eq_one]
    set u : B ⧸ P.subgroupOf B := QuotientGroup.mk ⟨x, hxB⟩ with hu
    set v : B ⧸ P.subgroupOf B := QuotientGroup.mk ⟨t, htB⟩ with hv
    have hu1 : u ≠ 1 := by
      rw [hu, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hxP
    have hv1 : v ≠ 1 := by
      rw [hv, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact htP
    have hu2 : u * u = 1 := by
      rw [hu, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
      change x * x ∈ P
      rw [hxx]
      exact P.one_mem
    have hv2 : v * v = 1 := by
      rw [hv, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, mem_subgroupOf]
      change t * t ∈ P
      rw [htt]
      exact P.one_mem
    have hvu := eq_of_mul_self_eq_one_of_isCyclic hv1 hu1 hv2 hu2
    rw [hv, hu, QuotientGroup.eq, mem_subgroupOf] at hvu
    have hy : t⁻¹ * x ∈ P := hvu
    have hxy : t * (t⁻¹ * x) = x := by group
    obtain ⟨m, -, hm⟩ := hcoset _ hy (by rw [hxy, hx2])
    rw [hxy] at hm
    exact hxt m hm.symm
  · refine hgen.trans (closure_mono ?_)
    rintro x ⟨hxP, hx2⟩
    exact ⟨hPB hxP, hx2, fun g hg => hfus g (hg ▸ hxP)⟩

theorem sylow_and_firstTransferData_of_isCyclic [Finite G] {B P : Subgroup G} {t : G}
    (hB : IsSylowOf 2 B (normalizer (P : Set G))) (hPB : P ≤ B) [(P.subgroupOf B).Normal]
    (hcyc : IsCyclic (B ⧸ P.subgroupOf B)) (htB : t ∈ B) (htP : t ∉ P) (ht : orderOf t = 2)
    (hfus : ∀ g : G, g⁻¹ * t * g ∉ P)
    (hcoset : ∀ y ∈ P, orderOf (t * y) = 2 → ∃ m ∈ P, t * y = m⁻¹ * t * m)
    (hgen : P ≤ closure {x | x ∈ P ∧ orderOf x = 2}) :
    (∃ T : Sylow 2 G, (T : Subgroup G) = B) ∧ FirstTransferData B P t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer (B : Set G) ≤ normalizer (P : Set G) := by
    have h := normalizer_le_normalizer_closure_involutions B t
    rwa [closure_involutions_eq hPB hcyc htB htP ht hfus hcoset hgen] at h
  have hS := exists_sylow_eq_of_isSylowOf_of_normalizer_le hB hN
  exact ⟨hS, firstTransferData_of_isCyclic hS hPB hcyc htB htP ht hfus⟩

theorem sylow_and_firstTransferData_of_relIndex_eq_two [Finite G] {B B₀ H : Subgroup G} {t : G}
    (hB : IsSylowOf 2 B H) (hN : normalizer (B : Set G) ≤ H) (hB₀ : B₀ ≤ B)
    (hidx : B₀.relIndex B = 2) (htB : t ∈ B) (htB₀ : t ∉ B₀) (ht : orderOf t = 2)
    (hfus : ∀ g : G, g⁻¹ * t * g ∉ B₀) :
    (∃ T : Sylow 2 G, (T : Subgroup G) = B) ∧ FirstTransferData B B₀ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := exists_sylow_eq_of_isSylowOf_of_normalizer_le hB hN
  exact ⟨hS, firstTransferData_of_relIndex_eq_two hS hB₀ hidx htB htB₀ ht hfus⟩

end CFSG.LocalAnalysis.EvenBN.Common
