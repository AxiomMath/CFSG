module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Int.Star
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.KC.B433Alt

open scoped Classical

variable {G : Type*} [Group G]

theorem card_dc_le [Fintype G] (H S : Subgroup G) (x : G) (hconj : ∀ s ∈ S, x * s * x⁻¹ ∈ H) :
    (Finset.univ.filter fun g => ∃ a ∈ H, ∃ b ∈ H, g = a * x * b).card ≤
      Nat.card H * S.relIndex H := by
  let f : H × (H ⧸ S.subgroupOf H) → G := fun p => (p.1 : G) * x * ((Quotient.out p.2 : H) : G)⁻¹
  have hsurj : Set.SurjOn f (Finset.univ : Finset (H × (H ⧸ S.subgroupOf H)))
      (Finset.univ.filter fun g => ∃ a ∈ H, ∃ b ∈ H, g = a * x * b) := by
    intro g hg
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hg
    obtain ⟨a, ha, b, hb, rfl⟩ := hg
    obtain ⟨s, hs⟩ := QuotientGroup.mk_out_eq_mul (S.subgroupOf H) (⟨b⁻¹, H.inv_mem hb⟩ : H)
    have hsS : ((s : H) : G) ∈ S := s.2
    refine ⟨(⟨a * (x * ((s : H) : G) * x⁻¹), H.mul_mem ha (hconj _ hsS)⟩,
      ((⟨b⁻¹, H.inv_mem hb⟩ : H) : H ⧸ S.subgroupOf H)), by simp, ?_⟩
    change a * (x * ((s : H) : G) * x⁻¹) * x *
      ((Quotient.out (((⟨b⁻¹, H.inv_mem hb⟩ : H) : H ⧸ S.subgroupOf H)) : H) : G)⁻¹ = a * x * b
    have hs' : ((Quotient.out (((⟨b⁻¹, H.inv_mem hb⟩ : H) : H ⧸ S.subgroupOf H)) : H) : G) =
        b⁻¹ * ((s : H) : G) := by
      rw [hs]
      rfl
    rw [hs']
    group
  calc (Finset.univ.filter fun g => ∃ a ∈ H, ∃ b ∈ H, g = a * x * b).card
      ≤ (Finset.univ : Finset (H × (H ⧸ S.subgroupOf H))).card :=
        Finset.card_le_card_of_surjOn f hsurj
    _ = Nat.card H * S.relIndex H := by
      rw [Finset.card_univ, Fintype.card_prod, ← Nat.card_eq_fintype_card,
        ← Nat.card_eq_fintype_card, Subgroup.relIndex, Subgroup.index_eq_card]

theorem card_biUnion_dc_le [Fintype G] {r : ℕ} (H : Subgroup G) (S : Fin r → Subgroup G)
    (x : Fin r → G) (hconj : ∀ i, ∀ s ∈ S i, x i * s * (x i)⁻¹ ∈ H) (U : Finset (Fin r)) :
    (U.biUnion fun i => Finset.univ.filter fun g => ∃ a ∈ H, ∃ b ∈ H, g = a * x i * b).card ≤
      Nat.card H * ∑ i ∈ U, (S i).relIndex H := by
  rw [Finset.mul_sum]
  exact Finset.card_biUnion_le.trans
    (Finset.sum_le_sum fun i _ => card_dc_le H (S i) (x i) (hconj i))

theorem exact_of_cover [Fintype G] {r : ℕ} (H K : Subgroup G) (S : Fin r → Subgroup G)
    (x : Fin r → G) (v : Fin r → ℕ) (E : Finset (Fin r))
    (hconj : ∀ i, ∀ s ∈ S i, x i * s * (x i)⁻¹ ∈ H)
    (hcov : ∀ g : G, ∃ i, ∃ a ∈ H, ∃ b ∈ H, g = a * x i * b)
    (hv : ∀ i, (S i).relIndex H ≤ v i) (hE : ∀ i, x i ∈ K ↔ i ∈ E)
    (hHK : H ≤ K) (c : ℕ) (hc : Nat.card H ≤ c) (htot : c * ∑ i ∈ E, v i ≤ Nat.card K) :
    (∀ i ∈ E, (Finset.univ.filter fun g => ∃ a ∈ H, ∃ b ∈ H, g = a * x i * b).card =
      Nat.card H * v i) ∧
    (∀ i ∈ E, ∀ j ∈ E, (∃ a ∈ H, ∃ b ∈ H, x j = a * x i * b) → i = j) ∧
    c * ∑ i ∈ E, v i ≤ Nat.card H * ∑ i ∈ E, v i := by
  let dc : Fin r → Finset G := fun i =>
    Finset.univ.filter fun g => ∃ a ∈ H, ∃ b ∈ H, g = a * x i * b
  have hdc : ∀ i g, g ∈ dc i ↔ ∃ a ∈ H, ∃ b ∈ H, g = a * x i * b := fun i g => by
    simp only [dc, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcardK : Nat.card K = (Finset.univ.filter fun g => g ∈ K).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hsub : (Finset.univ.filter fun g => g ∈ K) ⊆ E.biUnion dc := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨i, a, ha, b, hb, rfl⟩ := hcov g
    refine Finset.mem_biUnion.2 ⟨i, (hE i).1 ?_, (hdc i _).2 ⟨a, ha, b, hb, rfl⟩⟩
    have e : x i = a⁻¹ * (a * x i * b) * b⁻¹ := by group
    rw [e]
    exact K.mul_mem (K.mul_mem (hHK (H.inv_mem ha)) hg) (hHK (H.inv_mem hb))
  have hle : ∀ i, (dc i).card ≤ Nat.card H * v i := fun i =>
    (card_dc_le H (S i) (x i) (hconj i)).trans (Nat.mul_le_mul_left _ (hv i))
  have hsumle : ∑ i ∈ E, (dc i).card ≤ Nat.card H * ∑ i ∈ E, v i := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hle i
  have hchain : Nat.card H * ∑ i ∈ E, v i ≤ ∑ i ∈ E, (dc i).card := by
    calc Nat.card H * ∑ i ∈ E, v i ≤ c * ∑ i ∈ E, v i := Nat.mul_le_mul_right _ hc
      _ ≤ Nat.card K := htot
      _ ≤ (E.biUnion dc).card := by rw [hcardK]; exact Finset.card_le_card hsub
      _ ≤ ∑ i ∈ E, (dc i).card := Finset.card_biUnion_le
  refine ⟨fun i hi => ?_, fun i hi j hj hji => ?_, ?_⟩
  rotate_right
  · calc c * ∑ i ∈ E, v i ≤ Nat.card K := htot
      _ ≤ (E.biUnion dc).card := by rw [hcardK]; exact Finset.card_le_card hsub
      _ ≤ ∑ i ∈ E, (dc i).card := Finset.card_biUnion_le
      _ ≤ Nat.card H * ∑ i ∈ E, v i := hsumle
  ·
    have hsum : ∑ k ∈ E, (dc k).card = ∑ k ∈ E, Nat.card H * v k := by
      refine le_antisymm (Finset.sum_le_sum fun k _ => hle k) ?_
      rw [← Finset.mul_sum]
      exact hchain
    exact (Finset.sum_eq_sum_iff_of_le (fun k _ => hle k)).1 hsum i hi
  · by_contra hne
    have hxi : x j ∈ dc i := (hdc i _).2 hji
    have hxj : x j ∈ dc j := (hdc j _).2 ⟨1, H.one_mem, 1, H.one_mem, by group⟩
    have hE' : E = insert i (E.erase i) := (Finset.insert_erase hi).symm
    have hjE : j ∈ E.erase i := Finset.mem_erase.2 ⟨Ne.symm hne, hj⟩
    have h1 : (E.biUnion dc).card + 1 ≤ (dc i).card + ((E.erase i).biUnion dc).card := by
      rw [hE', Finset.biUnion_insert, Finset.erase_insert (Finset.notMem_erase i E)]
      have hint : 1 ≤ (dc i ∩ (E.erase i).biUnion dc).card :=
        Finset.card_pos.2 ⟨x j, Finset.mem_inter.2 ⟨hxi, Finset.mem_biUnion.2 ⟨j, hjE, hxj⟩⟩⟩
      have := Finset.card_union_add_card_inter (dc i) ((E.erase i).biUnion dc)
      omega
    have h2 : ((E.erase i).biUnion dc).card ≤ ∑ k ∈ E.erase i, (dc k).card := Finset.card_biUnion_le
    have h3 : (dc i).card + ∑ k ∈ E.erase i, (dc k).card = ∑ k ∈ E, (dc k).card :=
      Finset.add_sum_erase E (fun k => (dc k).card) hi
    have hbig : (E.biUnion dc).card = ∑ i ∈ E, (dc i).card := by
      refine le_antisymm Finset.card_biUnion_le ?_
      calc ∑ i ∈ E, (dc i).card ≤ Nat.card H * ∑ i ∈ E, v i := hsumle
        _ ≤ c * ∑ i ∈ E, v i := Nat.mul_le_mul_right _ hc
        _ ≤ Nat.card K := htot
        _ ≤ (E.biUnion dc).card := by rw [hcardK]; exact Finset.card_le_card hsub
    omega

theorem eq_or_eq_of_cover [Finite G] {r : ℕ} (H K L : Subgroup G) (S : Fin r → Subgroup G)
    (x : Fin r → G) (v : Fin r → ℕ) (E : Finset (Fin r)) (i0 : Fin r)
    (hconj : ∀ i, ∀ s ∈ S i, x i * s * (x i)⁻¹ ∈ H)
    (hcov : ∀ g : G, ∃ i, ∃ a ∈ H, ∃ b ∈ H, g = a * x i * b)
    (hv : ∀ i, (S i).relIndex H ≤ v i) (hE : ∀ i, x i ∈ K ↔ i ∈ E)
    (hHK : H ≤ K) (hHL : H ≤ L) (hLK : L ≤ K) (c : ℕ) (hc : Nat.card H ≤ c)
    (htot : c * ∑ i ∈ E, v i ≤ Nat.card K) (hi0 : x i0 ∈ H) (hv0 : v i0 = 1)
    (harith : ∀ U ⊆ E, i0 ∈ U → (∑ i ∈ U, v i) ∣ ∑ i ∈ E, v i → U = {i0} ∨ U = E) :
    L = H ∨ L = K := by
  have := Fintype.ofFinite G
  let dc : Fin r → Finset G := fun i =>
    Finset.univ.filter fun g => ∃ a ∈ H, ∃ b ∈ H, g = a * x i * b
  have hdc : ∀ i g, g ∈ dc i ↔ ∃ a ∈ H, ∃ b ∈ H, g = a * x i * b := fun i g => by
    simp only [dc, Finset.mem_filter, Finset.mem_univ, true_and]
  have hiff : ∀ M : Subgroup G, H ≤ M → ∀ i g, g ∈ dc i → (g ∈ M ↔ x i ∈ M) := by
    intro M hHM i g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := (hdc i g).1 hg
    constructor
    · intro hgM
      have e : x i = a⁻¹ * (a * x i * b) * b⁻¹ := by group
      rw [e]
      exact M.mul_mem (M.mul_mem (hHM (H.inv_mem ha)) hgM) (hHM (H.inv_mem hb))
    · intro hx
      exact M.mul_mem (M.mul_mem (hHM ha) hx) (hHM hb)
  have hcardM : ∀ M : Subgroup G, Nat.card M = (Finset.univ.filter fun g => g ∈ M).card := by
    intro M
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hvS : ∀ V : Finset (Fin r), ∑ i ∈ V, (S i).relIndex H ≤ ∑ i ∈ V, v i :=
    fun V => Finset.sum_le_sum fun i _ => hv i
  have hup : ∀ M : Subgroup G, H ≤ M → M ≤ K →
      Nat.card M ≤ Nat.card H * ∑ i ∈ E.filter (fun i => x i ∈ M), v i := by
    intro M hHM hMK
    rw [hcardM]
    refine (Finset.card_le_card ?_).trans
      ((card_biUnion_dc_le H S x hconj _).trans (Nat.mul_le_mul_left _ (hvS _)))
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
    obtain ⟨i, a, ha, b, hb, rfl⟩ := hcov g
    have hgi : a * x i * b ∈ dc i := (hdc i _).2 ⟨a, ha, b, hb, rfl⟩
    have hxi : x i ∈ M := (hiff M hHM i _ hgi).1 hg
    exact Finset.mem_biUnion.2 ⟨i, Finset.mem_filter.2 ⟨(hE i).1 (hMK hxi), hxi⟩, hgi⟩
  set U := E.filter fun i => x i ∈ L with hU
  have hUE : U ⊆ E := Finset.filter_subset _ _
  have hEK : E.filter (fun i => x i ∈ K) = E :=
    Finset.filter_true_of_mem fun i hi => (hE i).2 hi
  have hKup : Nat.card K ≤ Nat.card H * ∑ i ∈ E, v i := by
    have h := hup K hHK le_rfl
    rwa [hEK] at h
  have hK : Nat.card K ≤ Nat.card L + Nat.card H * ∑ i ∈ E \ U, v i := by
    rw [hcardM K, hcardM L]
    have hsplit : (Finset.univ.filter fun g => g ∈ K) ⊆ (Finset.univ.filter fun g => g ∈ L) ∪
        (E \ U).biUnion dc := by
      intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      by_cases hgL : g ∈ L
      · exact Finset.mem_union_left _ (by simpa using hgL)
      · obtain ⟨i, a, ha, b, hb, rfl⟩ := hcov g
        have hgi : a * x i * b ∈ dc i := (hdc i _).2 ⟨a, ha, b, hb, rfl⟩
        have hxK : x i ∈ K := (hiff K hHK i _ hgi).1 hg
        have hxL : x i ∉ L := fun h => hgL ((hiff L hHL i _ hgi).2 h)
        refine Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, ?_, hgi⟩)
        exact Finset.mem_sdiff.2 ⟨(hE i).1 hxK, fun hiU => hxL (Finset.mem_filter.1 hiU).2⟩
    refine (Finset.card_le_card hsplit).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_left ((card_biUnion_dc_le H S x hconj _).trans
        (Nat.mul_le_mul_left _ (hvS _))) _))
  have hsum : ∑ i ∈ E \ U, v i + ∑ i ∈ U, v i = ∑ i ∈ E, v i := Finset.sum_sdiff hUE
  have hL : Nat.card L ≤ Nat.card H * ∑ i ∈ U, v i := hup L hHL hLK
  have hHc : Nat.card H * ∑ i ∈ E, v i ≤ c * ∑ i ∈ E, v i := Nat.mul_le_mul_right _ hc
  have hm1 : Nat.card H * ∑ i ∈ E, v i =
      Nat.card H * ∑ i ∈ E \ U, v i + Nat.card H * ∑ i ∈ U, v i := by
    rw [← hsum, Nat.mul_add]
  have hLeq : Nat.card L = Nat.card H * ∑ i ∈ U, v i := le_antisymm hL (by linarith)
  have hKeq : Nat.card K = Nat.card H * ∑ i ∈ E, v i := le_antisymm hKup (by linarith)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hdvd : (∑ i ∈ U, v i) ∣ ∑ i ∈ E, v i := by
    have h := Subgroup.card_dvd_of_le hLK
    rw [hLeq, hKeq] at h
    exact Nat.dvd_of_mul_dvd_mul_left hHpos h
  have hi0U : i0 ∈ U :=
    Finset.mem_filter.2 ⟨(hE i0).1 (hHK hi0), hHL hi0⟩
  rcases harith U hUE hi0U hdvd with h | h
  · left
    have hcardL : Nat.card L ≤ Nat.card H := by
      rw [hLeq, h, Finset.sum_singleton, hv0, mul_one]
    exact (Subgroup.eq_of_le_of_card_ge hHL hcardL).symm
  · right
    have hcardK : Nat.card K ≤ Nat.card L := by
      rw [hLeq, hKeq, h]
    exact Subgroup.eq_of_le_of_card_ge hLK hcardK

end CFSG.KC.B433Alt

end
