module

import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.LargeExtraspecial.DW.W3

open Subgroup Matrix
open scoped Pointwise

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

@[expose] def sMat : Mat3 := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def tMat : Mat3 := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

@[expose] def conjMat : Fin 21 → Mat3 :=
  ![!![1, 0, 0; 0, 0, 1; 1, 1, 0], !![1, 0, 0; 1, 0, 1; 1, 1, 0], !![1, 0, 0; 1, 1, 0; 0, 0, 1],
    !![1, 0, 0; 1, 1, 0; 1, 0, 1], !![1, 0, 0; 0, 0, 1; 1, 1, 1], !![1, 0, 0; 1, 0, 1; 0, 1, 1],
    !![0, 0, 1; 1, 0, 0; 1, 1, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0],
    !![0, 0, 1; 0, 1, 1; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 0, 1; 1, 0, 0; 1, 1, 1],
    !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 1, 0, 1], !![0, 0, 1; 1, 0, 0; 0, 1, 1],
    !![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 1, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 1, 0; 1, 0, 1], !![1, 0, 0; 1, 0, 1; 1, 1, 1], !![1, 0, 0; 0, 0, 1; 0, 1, 1]]

@[expose] def conjInv : Fin 21 → Mat3 :=
  ![!![1, 0, 0; 1, 0, 1; 0, 1, 0], !![1, 0, 0; 1, 0, 1; 1, 1, 0], !![1, 0, 0; 1, 1, 0; 0, 0, 1],
    !![1, 0, 0; 1, 1, 0; 1, 0, 1], !![1, 0, 0; 1, 1, 1; 0, 1, 0], !![1, 0, 0; 1, 1, 1; 1, 1, 0],
    !![0, 1, 0; 0, 1, 1; 1, 0, 0], !![0, 0, 1; 0, 1, 0; 1, 0, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0],
    !![0, 0, 1; 1, 1, 0; 1, 0, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], !![0, 1, 0; 1, 1, 1; 1, 0, 0],
    !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 1, 1], !![0, 1, 0; 1, 0, 1; 1, 0, 0],
    !![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 1, 1, 0], !![1, 0, 0; 0, 1, 0; 0, 0, 1],
    !![1, 0, 0; 0, 1, 0; 1, 0, 1], !![1, 0, 0; 0, 1, 1; 1, 1, 0], !![1, 0, 0; 0, 1, 1; 0, 1, 0]]

theorem conjMat_mul_conjInv : ∀ k : Fin 21, conjMat k * conjInv k = 1 := by decide

theorem conjInv_mul_conjMat : ∀ k : Fin 21, conjInv k * conjMat k = 1 := by decide

theorem exists_conjMat9 : ∀ a b c d e f g h i : ZMod 2,
    (!![a, b, c; d, e, f; g, h, i] : Mat3) * !![a, b, c; d, e, f; g, h, i] = 1 →
    (!![a, b, c; d, e, f; g, h, i] : Mat3) ≠ 1 →
    ∃ k : Fin 21, conjMat k * sMat = !![a, b, c; d, e, f; g, h, i] * conjMat k := by
  decide

theorem exists_conjMat (B : Mat3) (hB : B * B = 1) (hB1 : B ≠ 1) :
    ∃ k : Fin 21, conjMat k * sMat = B * conjMat k := by
  have h := exists_conjMat9 (B 0 0) (B 0 1) (B 0 2) (B 1 0) (B 1 1) (B 1 2) (B 2 0) (B 2 1)
    (B 2 2)
  rw [← Matrix.eta_fin_three B] at h
  exact h hB hB1

@[expose] def sU : GL (Fin 3) (ZMod 2) := ⟨sMat, sMat, by decide, by decide⟩

@[expose] def tU : GL (Fin 3) (ZMod 2) := ⟨tMat, tMat, by decide, by decide⟩

@[expose] def conjU (k : Fin 21) : GL (Fin 3) (ZMod 2) :=
  ⟨conjMat k, conjInv k, conjMat_mul_conjInv k, conjInv_mul_conjMat k⟩

theorem exists_conj_sU {b : GL (Fin 3) (ZMod 2)} (hb : b * b = 1) (hb1 : b ≠ 1) :
    ∃ c : GL (Fin 3) (ZMod 2), c * sU * c⁻¹ = b := by
  have hB : (b : Mat3) * b = 1 := by
    rw [← Units.val_mul, hb, Units.val_one]
  have hB1 : (b : Mat3) ≠ 1 := fun h => hb1 (Units.ext (by rw [h, Units.val_one]))
  obtain ⟨k, hk⟩ := exists_conjMat b hB hB1
  refine ⟨conjU k, ?_⟩
  have h1 : conjU k * sU = b * conjU k := Units.ext (by
    rw [Units.val_mul, Units.val_mul]
    exact hk)
  rw [h1, mul_inv_cancel_right]

theorem exists_conj_eq {a b : GL (Fin 3) (ZMod 2)} (ha : a * a = 1) (ha1 : a ≠ 1)
    (hb : b * b = 1) (hb1 : b ≠ 1) : ∃ c : GL (Fin 3) (ZMod 2), c * a * c⁻¹ = b := by
  obtain ⟨ca, hca⟩ := exists_conj_sU ha ha1
  obtain ⟨cb, hcb⟩ := exists_conj_sU hb hb1
  refine ⟨cb * ca⁻¹, ?_⟩
  rw [← hca, ← hcb]
  group

theorem sU_mul_self : sU * sU = 1 := by decide

theorem tU_mul_self : tU * tU = 1 := by decide

theorem sU_ne_one : sU ≠ 1 := by decide

theorem tU_ne_one : tU ≠ 1 := by decide

theorem sq_sU_mul_tU_mul_self : (sU * tU) ^ 2 * (sU * tU) ^ 2 = 1 := by decide

theorem sq_sU_mul_tU_ne_one : (sU * tU) ^ 2 ≠ 1 := by decide

theorem sU_pow_mul_injective : ∀ b b' : Fin 2, ∀ k k' : Fin 4,
    sU ^ (b : ℕ) * (sU * tU) ^ (k : ℕ) = sU ^ (b' : ℕ) * (sU * tU) ^ (k' : ℕ) →
      b = b' ∧ k = k' := by
  decide

theorem card_GL_three : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

theorem sign_eq_neg_one {α : Type*} [Fintype α] [DecidableEq α] {σ : Equiv.Perm α}
    (h2 : σ * σ = 1) (hfree : ∀ a, σ a ≠ a) {n : ℕ} (hcard : Fintype.card α = 2 * n)
    (hn : Odd n) : Equiv.Perm.sign σ = -1 := by
  obtain ⟨a⟩ : Nonempty α := Fintype.card_pos_iff.mp (by obtain ⟨m, rfl⟩ := hn; omega)
  have hσ1 : σ ≠ 1 := fun h => hfree a (by rw [h]; rfl)
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact h2) hσ1
  obtain ⟨m, hm⟩ := Equiv.Perm.cycleType_prime_order (σ := σ) (by rw [hord]; exact Nat.prime_two)
  have hsupp : σ.support = Finset.univ := by
    ext x
    simp [Equiv.Perm.mem_support, hfree x]
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hm, hord, hsupp, Finset.card_univ, hcard, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [Equiv.Perm.sign_of_cycleType, hm, hord, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul, show (m + 1) * 2 + (m + 1) = 3 * n by omega]
  exact (Odd.mul ⟨1, rfl⟩ hn).neg_one_pow

theorem exists_index_two {J : Type*} [Group J] [Finite J] (T : Subgroup J) {z : J}
    (hzc : ∀ g, z * g = g * z) (hz2 : z * z = 1) (hzT : z ∉ T) {n : ℕ} (hidx : T.index = 2 * n)
    (hn : Odd n) : ∃ K : Subgroup J, K.index = 2 ∧ z ∉ K := by
  classical
  have : Fintype (J ⧸ T) := Fintype.ofFinite _
  let ε : J →* ℤˣ := Equiv.Perm.sign.comp (MulAction.toPermHom J (J ⧸ T))
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hz : ε z = -1 := by
    show Equiv.Perm.sign (MulAction.toPermHom J (J ⧸ T) z) = -1
    refine sign_eq_neg_one (n := n) ?_ ?_ ?_ hn
    · rw [← map_mul, hz2, map_one]
    · intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        change z • (g : J ⧸ T) ≠ g
        rw [MulAction.Quotient.smul_mk, Ne, QuotientGroup.eq]
        intro h
        apply hzT
        have e : (z * g)⁻¹ * g = z := by
          rw [_root_.mul_inv_rev, hzinv, mul_assoc, hzc g, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [← e]
        exact h
    · rw [← Nat.card_eq_fintype_card]
      exact hidx
  refine ⟨ε.ker, ?_, fun h => ?_⟩
  · have hsurj : Function.Surjective ε := fun u => by
      rcases Int.units_eq_one_or u with rfl | rfl
      · exact ⟨1, map_one ε⟩
      · exact ⟨z, hz⟩
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_units_int]
  · rw [MonoidHom.mem_ker, hz] at h
    exact absurd h (by decide)

theorem exists_section_of_involution {J : Type*} [Group J] [Finite J]
    (η : J →* GL (Fin 3) (ZMod 2)) (hη : Function.Surjective η) {z : J}
    (hker : ∀ j, η j = 1 ↔ j = 1 ∨ j = z) (hz1 : z ≠ 1) (hzc : ∀ j, z * j = j * z)
    (hz2 : z * z = 1) {j₀ : J} (hj₀ : j₀ * j₀ = 1) (hj₀1 : η j₀ ≠ 1) :
    ∃ σ : GL (Fin 3) (ZMod 2) →* J, ∀ g, η (σ g) = g := by
  have hlift : ∀ g : J, η g * η g = 1 → η g ≠ 1 → g * g = 1 := by
    intro g hg hg1
    have hj₀' : η j₀ * η j₀ = 1 := by rw [← map_mul, hj₀, map_one]
    obtain ⟨c, hc⟩ := exists_conj_eq hj₀' hj₀1 hg hg1
    obtain ⟨c', rfl⟩ := hη c
    have h1 : η ((c' * j₀ * c'⁻¹)⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_inv, hc, inv_mul_cancel]
    have hsq : c' * j₀ * c'⁻¹ * (c' * j₀ * c'⁻¹) = 1 := by
      calc c' * j₀ * c'⁻¹ * (c' * j₀ * c'⁻¹) = c' * (j₀ * j₀) * c'⁻¹ := by group
        _ = 1 := by rw [hj₀, mul_one, mul_inv_cancel]
    rcases (hker _).mp h1 with h | h
    · rw [inv_mul_eq_one] at h
      rw [← h]
      exact hsq
    · have hg' : g = c' * j₀ * c'⁻¹ * z := by
        rw [← h]
        group
      rw [hg']
      calc c' * j₀ * c'⁻¹ * z * (c' * j₀ * c'⁻¹ * z) =
          c' * j₀ * c'⁻¹ * (z * (c' * j₀ * c'⁻¹)) * z := by group
        _ = c' * j₀ * c'⁻¹ * (c' * j₀ * c'⁻¹) * (z * z) := by rw [hzc]; group
        _ = 1 := by rw [hsq, hz2, one_mul]
  obtain ⟨s, hs⟩ := hη sU
  obtain ⟨t, ht⟩ := hη tU
  have hs2 : s * s = 1 := hlift s (by rw [hs]; exact sU_mul_self) (by rw [hs]; exact sU_ne_one)
  have ht2 : t * t = 1 := hlift t (by rw [ht]; exact tU_mul_self) (by rw [ht]; exact tU_ne_one)
  set r := s * t with hr
  have hηr : η r = sU * tU := by rw [hr, map_mul, hs, ht]
  have hr4 : r ^ 4 = 1 := by
    have h := hlift (r ^ 2) (by rw [map_pow, hηr]; exact sq_sU_mul_tU_mul_self)
      (by rw [map_pow, hηr]; exact sq_sU_mul_tU_ne_one)
    rw [show 4 = 2 + 2 from rfl, pow_add]
    exact h
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hsr : s * r * s⁻¹ = r⁻¹ := by
    rw [hr, hsinv, _root_.mul_inv_rev, hsinv, htinv]
    calc s * (s * t) * s = s * s * t * s := by group
      _ = t * s := by rw [hs2, one_mul]
  have hconj : ∀ x ∈ zpowers r, s * x * s⁻¹ ∈ zpowers r := by
    rintro _ ⟨k, rfl⟩
    refine ⟨-k, ?_⟩
    change r ^ (-k) = s * r ^ k * s⁻¹
    rw [← conj_zpow, hsr, _root_.inv_zpow']
  have hsN : s ∈ normalizer (zpowers r : Set J) := by
    refine mem_normalizer_iff.mpr fun x => ⟨hconj x, fun hx => ?_⟩
    have h := hconj _ hx
    have e : s * (s * x * s⁻¹) * s⁻¹ = x := by
      calc s * (s * x * s⁻¹) * s⁻¹ = s * s * x * (s * s)⁻¹ := by group
        _ = x := by rw [hs2, inv_one, one_mul, mul_one]
    rwa [e] at h
  have hle : zpowers s ≤ normalizer (zpowers r : Set J) := (zpowers_le).mpr hsN
  set T : Subgroup J := zpowers s ⊔ zpowers r with hT
  have hTcard : Nat.card T ≤ 8 := by
    have h1 : ((T : Subgroup J) : Set J) = (zpowers s : Set J) * (zpowers r : Set J) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle
    have h2 : Nat.card T = Nat.card ((zpowers s : Set J) * (zpowers r : Set J) : Set J) := by
      rw [← h1]
      rfl
    have h4 : Nat.card (zpowers s : Set J) ≤ 2 := by
      rw [SetLike.coe_sort_coe, Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [sq]; exact hs2)
    have h5 : Nat.card (zpowers r : Set J) ≤ 4 := by
      rw [SetLike.coe_sort_coe, Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) hr4
    rw [h2]
    exact Set.natCard_mul_le.trans (Nat.mul_le_mul h4 h5)
  have hmem : ∀ (b : Fin 2) (k : Fin 4), s ^ (b : ℕ) * r ^ (k : ℕ) ∈ T := fun b k =>
    T.mul_mem (Subgroup.mem_sup_left (npow_mem_zpowers s b))
      (Subgroup.mem_sup_right (npow_mem_zpowers r k))
  have hηmem : ∀ (b : Fin 2) (k : Fin 4),
      η (s ^ (b : ℕ) * r ^ (k : ℕ)) = sU ^ (b : ℕ) * (sU * tU) ^ (k : ℕ) := by
    intro b k
    rw [map_mul, map_pow, map_pow, hs, hηr]
  have hηz : η z = 1 := (hker z).mpr (Or.inr rfl)
  let f : Fin 2 × Fin 4 → T := fun p => ⟨s ^ (p.1 : ℕ) * r ^ (p.2 : ℕ), hmem p.1 p.2⟩
  have hf : Function.Injective f := by
    rintro ⟨b, k⟩ ⟨b', k'⟩ h
    have h1 := congrArg (fun x : T => η (x : J)) h
    simp only [f, hηmem] at h1
    obtain ⟨rfl, rfl⟩ := sU_pow_mul_injective b b' k k' h1
    rfl
  have hcard8 : Nat.card (Fin 2 × Fin 4) = 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hT8 : Nat.card T = 8 := le_antisymm hTcard
    (hcard8 ▸ Nat.card_le_card_of_injective f hf)
  have hfb : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hT8, hcard8])
  have hzT : z ∉ T := by
    intro hz
    obtain ⟨⟨b, k⟩, hbk⟩ := hfb.2 ⟨z, hz⟩
    have h0 : s ^ (b : ℕ) * r ^ (k : ℕ) = z := congrArg Subtype.val hbk
    have h1 : sU ^ (b : ℕ) * (sU * tU) ^ (k : ℕ) =
        sU ^ ((0 : Fin 2) : ℕ) * (sU * tU) ^ ((0 : Fin 4) : ℕ) := by
      rw [← hηmem, h0, hηz]
      simp
    obtain ⟨rfl, rfl⟩ := sU_pow_mul_injective b 0 k 0 h1
    apply hz1
    rw [← h0]
    simp
  have hkerc : Nat.card η.ker = 2 := by
    have h : (η.ker : Set J) = {1, z} := by
      ext j
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hker j
    rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_pair (Ne.symm hz1)]
  have hJ : Nat.card J = 336 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv, card_GL_three,
      hkerc]
  have hidx : T.index = 2 * 21 := by
    have h := T.card_mul_index
    rw [hT8, hJ] at h
    omega
  obtain ⟨K, hK2, hzK⟩ := exists_index_two T hzc hz2 hzT hidx ⟨10, rfl⟩
  have hKcard : Nat.card K = 168 := by
    have h := K.card_mul_index
    rw [hK2, hJ] at h
    omega
  have hinj : Function.Injective (η.comp K.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro k hk
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype] at hk
    rcases (hker _).mp hk with h | h
    · exact (mem_bot).mpr (Subtype.ext h)
    · exact absurd (h ▸ k.2) hzK
  have hbij : Function.Bijective (η.comp K.subtype) :=
    hinj.bijective_of_nat_card_le (card_GL_three.trans hKcard.symm).le
  let e : K ≃* GL (Fin 3) (ZMod 2) := MulEquiv.ofBijective _ hbij
  refine ⟨K.subtype.comp e.symm.toMonoidHom, fun g => ?_⟩
  change (η.comp K.subtype) (e.symm g) = g
  exact e.apply_symm_apply g

end CFSG.LargeExtraspecial.DW.W3
