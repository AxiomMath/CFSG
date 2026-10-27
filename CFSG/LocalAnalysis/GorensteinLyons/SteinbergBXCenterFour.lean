module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
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
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

instance zpowers_subgroupOf_inf_centralizer_normal (Q : Subgroup G) (a : G) :
    ((zpowers a).subgroupOf (Q ⊓ centralizer {a})).Normal where
  conj_mem x hx g := by
    rw [mem_subgroupOf] at hx ⊢
    obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hx
    have hga : Commute (g : G) a := mem_centralizer_singleton_iff.mp (mem_inf.mp g.2).2
    have hgx : (g : G) * x * (g : G)⁻¹ = x := by
      rw [← hm, (hga.zpow_right m).eq, mul_inv_cancel_right]
    simpa only [coe_mul, coe_inv, hgx] using hx

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two {a x : G} (ha : orderOf a = 2)
    (hx : x ∈ zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hx
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one m with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem center_four_missing_core_inclusion_quotient_obstruction [Finite G] {Q : Subgroup G}
    (_hQ : IsPGroup 2 Q) {c : G} (hcQ : c ∈ Q) (hZ : (center Q).map Q.subtype = zpowers c)
    (hc4 : orderOf c = 4) (hQ' : ⁅Q, Q⁆ = zpowers (c ^ 2))
    (_hVe : CFSG.IsElementaryAbelian 2 (Q ⧸ center Q)) {v : ℕ} (hv : 2 ≤ v)
    (hV : Nat.card (Q ⧸ center Q) = 2 ^ (2 * v)) {a : G} (haQ : a ∈ Q) (haZ : a ∉ zpowers c)
    (ha2 : orderOf a = 2) {N : Subgroup G} (hNC : N ≤ centralizer {a})
    [hNn : (N.subgroupOf (centralizer {a})).Normal] (haN : a ∈ N) (hzN : c ^ 2 ∉ N) :
    (Q ⊓ centralizer {a}).relIndex Q = 2 ∧
      ⁅Q ⊓ centralizer {a}, Q ⊓ centralizer {a}⁆ = zpowers (c ^ 2) ∧
      (center (Q ⊓ centralizer {a} : Subgroup G)).map (Q ⊓ centralizer {a}).subtype =
        zpowers c ⊔ zpowers a ∧
      Nonempty (center (Q ⊓ centralizer {a} : Subgroup G) ≃*
        Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) ∧
      Q ⊓ N = zpowers a ∧
      Nat.card (↥(Q ⊓ centralizer {a}) ⧸ (zpowers a).subgroupOf (Q ⊓ centralizer {a})) =
        2 ^ (2 * v) ∧
      center (↥(Q ⊓ centralizer {a}) ⧸ (zpowers a).subgroupOf (Q ⊓ centralizer {a})) =
        (center (Q ⊓ centralizer {a} : Subgroup G)).map (QuotientGroup.mk' _) ∧
      IsCyclic (center (↥(Q ⊓ centralizer {a}) ⧸ (zpowers a).subgroupOf (Q ⊓ centralizer {a}))) ∧
      Nat.card (center (↥(Q ⊓ centralizer {a}) ⧸ (zpowers a).subgroupOf (Q ⊓ centralizer {a}))) =
        4 ∧
      (∃ φ : (↥(Q ⊓ centralizer {a}) ⧸ (zpowers a).subgroupOf (Q ⊓ centralizer {a})) →*
          (centralizer {a} ⧸ N.subgroupOf (centralizer {a})),
        Function.Injective φ ∧ ∀ p : (Q ⊓ centralizer {a} : Subgroup G),
          φ (QuotientGroup.mk p) = QuotientGroup.mk ⟨p, (mem_inf.mp p.2).2⟩) ∧
      ∃ x : centralizer {a} ⧸ N.subgroupOf (centralizer {a}), orderOf x = 4 := by
  classical
  set z := c ^ 2 with hzdef
  set P := Q ⊓ centralizer {a} with hP
  have hPQ : P ≤ Q := inf_le_left
  have hPC : P ≤ centralizer {a} := inf_le_right
  have hcen : ∀ x ∈ Q, x ∈ zpowers c ↔ ∀ y ∈ Q, y * x = x * y := by
    intro x hx
    rw [← hZ, mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩ w hw
      exact congrArg Subtype.val (mem_center_iff.mp hy ⟨w, hw⟩)
    · intro h
      exact ⟨⟨x, hx⟩, mem_center_iff.mpr fun g => Subtype.ext (h g g.2), rfl⟩
  have hcZ : ∀ y ∈ Q, y * c = c * y := (hcen c hcQ).mp (mem_zpowers c)
  have hzQ : z ∈ Q := pow_mem hcQ 2
  have hzZ : ∀ y ∈ Q, y * z = z * y := (hcen z hzQ).mp (pow_mem (mem_zpowers c) 2)
  have hz1 : z ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hc4] at this
    norm_num at this
  have hzz : z * z = 1 := by
    rw [← pow_two, hzdef, ← pow_mul, show 2 * 2 = orderOf c by rw [hc4], pow_orderOf_eq_one]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzz
  have hoz : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two, hzz]) hz1
  have hval : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ = 1 ∨ ⁅x, y⁆ = z := fun x hx y hy =>
    eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two hoz (hQ' ▸ commutator_mem_commutator hx hy)
  have hwc : ∀ w : G, (w = 1 ∨ w = z) → ∀ y ∈ Q, y * w = w * y := by
    rintro w (rfl | rfl) y hy
    · rw [mul_one, one_mul]
    · exact hzZ y hy
  have hww : ∀ w w' : G, (w = 1 ∨ w = z) → (w' = 1 ∨ w' = z) → w * w' = w' * w := by
    rintro w w' (rfl | rfl) (rfl | rfl) <;> simp
  have hwinv : ∀ w : G, (w = 1 ∨ w = z) → w⁻¹ = w := by
    rintro w (rfl | rfl)
    · exact inv_one
    · exact hzinv
  have hwsq : ∀ w : G, (w = 1 ∨ w = z) → w * w = 1 := by
    rintro w (rfl | rfl)
    · exact mul_one 1
    · exact hzz
  have hmulr : ∀ x ∈ Q, ∀ y ∈ Q, ∀ y' ∈ Q, ⁅x, y * y'⁆ = ⁅x, y⁆ * ⁅x, y'⁆ := by
    intro x hx y hy y' hy'
    have hxyx : x * y * x⁻¹ ∈ Q := mul_mem (mul_mem hx hy) (inv_mem hx)
    calc ⁅x, y * y'⁆ = x * y * x⁻¹ * ⁅x, y'⁆ * y⁻¹ := by
          simp only [commutatorElement_def]; group
      _ = ⁅x, y'⁆ * (x * y * x⁻¹ * y⁻¹) := by
          rw [hwc _ (hval x hx y' hy') _ hxyx]; simp only [mul_assoc]
      _ = ⁅x, y⁆ * ⁅x, y'⁆ := by
          rw [← commutatorElement_def]; exact hww _ _ (hval x hx y' hy') (hval x hx y hy)
  have hmull : ∀ x ∈ Q, ∀ x' ∈ Q, ∀ y ∈ Q, ⁅x * x', y⁆ = ⁅x, y⁆ * ⁅x', y⁆ := by
    intro x hx x' hx' y hy
    calc ⁅x * x', y⁆ = x * ⁅x', y⁆ * (y * x⁻¹ * y⁻¹) := by
          simp only [commutatorElement_def]; group
      _ = ⁅x', y⁆ * (x * y * x⁻¹ * y⁻¹) := by
          rw [hwc _ (hval x' hx' y hy) _ hx]; simp only [mul_assoc]
      _ = ⁅x, y⁆ * ⁅x', y⁆ := by
          rw [← commutatorElement_def]; exact hww _ _ (hval x' hx' y hy) (hval x hx y hy)
  have hinvr : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁻¹⁆ = ⁅x, y⁆ := by
    intro x hx y hy
    have h := hmulr x hx y hy y⁻¹ (inv_mem hy)
    rw [mul_inv_cancel, commutatorElement_one_right] at h
    rw [← hwinv _ (hval x hx y hy), eq_inv_of_mul_eq_one_right h.symm]
  have hinvl : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x⁻¹, y⁆ = ⁅x, y⁆ := by
    intro x hx y hy
    have h := hmull x hx x⁻¹ (inv_mem hx) y hy
    rw [mul_inv_cancel, commutatorElement_one_left] at h
    rw [← hwinv _ (hval x hx y hy), eq_inv_of_mul_eq_one_right h.symm]
  have hcomm1 : ∀ x y : G, ⁅x, y⁆ = 1 ↔ y * x = x * y := fun x y => by
    rw [commutatorElement_eq_one_iff_mul_comm, eq_comm]
  have hmemP : ∀ y, y ∈ P ↔ y ∈ Q ∧ ⁅a, y⁆ = 1 := by
    intro y
    rw [hP, mem_inf, mem_centralizer_singleton_iff, hcomm1]
  have haP : a ∈ P := (hmemP a).mpr ⟨haQ, commutatorElement_self a⟩
  have hcP : c ∈ P := (hmemP c).mpr ⟨hcQ, (hcomm1 a c).mpr (hcZ a haQ).symm⟩
  have hnotcen : ∀ x ∈ Q, x ∉ zpowers c → ∃ q ∈ Q, ⁅x, q⁆ = z := by
    intro x hx hxZ
    by_contra h
    refine hxZ ((hcen x hx).mpr fun y hy => (hcomm1 x y).mp ?_)
    rcases hval x hx y hy with h' | h'
    · exact h'
    · exact absurd ⟨y, hy, h'⟩ h
  obtain ⟨q₀, hq₀Q, hq₀⟩ := hnotcen a haQ haZ
  have hidx : P.relIndex Q = 2 := by
    rw [relIndex_eq_two_iff]
    refine ⟨q₀, hq₀Q, fun b hb => ?_⟩
    rw [hmemP, hmemP, hmulr a haQ b hb q₀ hq₀Q, hq₀]
    rcases hval a haQ b hb with h | h
    · simp [h, hz1, hb, mul_mem hb hq₀Q]
    · simp [h, hz1, hzz, hb, mul_mem hb hq₀Q]
  have hcardZ : Nat.card (center Q) = 4 := by
    rw [← card_map_of_injective (f := Q.subtype) Q.subtype_injective, hZ, Nat.card_zpowers, hc4]
  have hcardQ : Nat.card Q = 2 ^ (2 * v + 2) := by
    rw [← (center Q).card_mul_index, hcardZ, index_eq_card, hV]
    ring
  have hcardP : Nat.card P = 2 ^ (2 * v + 1) := by
    have h := (P.subgroupOf Q).card_mul_index
    rw [← relIndex, hidx, Nat.card_congr (subgroupOfEquivOfLe hPQ).toEquiv, hcardQ] at h
    have : 2 ^ (2 * v + 2) = 2 ^ (2 * v + 1) * 2 := by ring
    omega
  have hcenP : ∀ x ∈ P, (∀ y ∈ P, y * x = x * y) → ∃ i : ℤ, x = c ^ i ∨ x = c ^ i * a := by
    intro x hx hxc
    have hxQ := hPQ hx
    by_cases hxZ : x ∈ zpowers c
    · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hxZ
      exact ⟨i, Or.inl rfl⟩
    obtain ⟨q, hqQ, hq⟩ := hnotcen x hxQ hxZ
    have hqP : q ∉ P := fun hqP => hz1 (hq ▸ (hcomm1 x q).mpr (hxc q hqP))
    have hxa : x * a⁻¹ ∈ zpowers c := by
      rw [hcen _ (mul_mem hxQ (inv_mem haQ))]
      intro y hy
      refine (hcomm1 _ _).mp ?_
      rw [hmull x hxQ a⁻¹ (inv_mem haQ) y hy, hinvl a haQ y hy]
      by_cases hyP : y ∈ P
      · rw [(hcomm1 x y).mpr (hxc y hyP), ((hmemP y).mp hyP).2, mul_one]
      · have hay : ⁅a, y⁆ = z := by
          rcases hval a haQ y hy with h | h
          · exact absurd ((hmemP y).mpr ⟨hy, h⟩) hyP
          · exact h
        have haq : ⁅a, q⁆ = z := by
          rcases hval a haQ q hqQ with h | h
          · exact absurd ((hmemP q).mpr ⟨hqQ, h⟩) hqP
          · exact h
        have hyq : y⁻¹ * q ∈ P := by
          rw [hmemP]
          refine ⟨mul_mem (inv_mem hy) hqQ, ?_⟩
          rw [hmulr a haQ _ (inv_mem hy) q hqQ, hinvr a haQ y hy, hay, haq, hzz]
        have hxy : ⁅x, y⁆ = z := by
          have h := hmulr x hxQ y hy (y⁻¹ * q) (mul_mem (inv_mem hy) hqQ)
          rw [mul_inv_cancel_left, hq, (hcomm1 x _).mpr (hxc _ hyq), mul_one] at h
          exact h.symm
        rw [hxy, hay, hzz]
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hxa
    exact ⟨i, Or.inr (by rw [hi, inv_mul_cancel_right])⟩
  have hca : Commute c a := (hcZ a haQ).symm
  have hcenc : ⟨c, hcP⟩ ∈ center P := mem_center_iff.mpr fun g => Subtype.ext (hcZ g (hPQ g.2))
  have hcena : ⟨a, haP⟩ ∈ center P := mem_center_iff.mpr fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hPC g.2))
  have hZP : (center P).map P.subtype = zpowers c ⊔ zpowers a := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hxP⟩, hxc, rfl⟩
      obtain ⟨i, h | h⟩ := hcenP x hxP fun y hy =>
        congrArg Subtype.val (mem_center_iff.mp hxc ⟨y, hy⟩)
      · exact mem_sup_left (h ▸ zpow_mem (mem_zpowers c) i)
      · exact h ▸ mul_mem (mem_sup_left (zpow_mem (mem_zpowers c) i)) (mem_sup_right
          (mem_zpowers a))
    · rw [sup_le_iff, zpowers_le, zpowers_le]
      exact ⟨⟨⟨c, hcP⟩, hcenc, rfl⟩, ⟨⟨a, haP⟩, hcena, rfl⟩⟩
  have hcomm' : ∀ (m : zpowers c) (n : zpowers a),
      Commute ((zpowers c).subtype m) ((zpowers a).subtype n) := by
    rintro ⟨m, hm⟩ ⟨n, hn⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hm
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hn
    exact hca.zpow_zpow i j
  set f := (zpowers c).subtype.noncommCoprod (zpowers a).subtype hcomm' with hf
  have hdisj : _root_.Disjoint (zpowers c) (zpowers a) := by
    rw [disjoint_def]
    intro x hxc hxa
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ha2 hxa with h | h
    · exact h
    · exact absurd (h ▸ hxc) haZ
  have hfinj : Function.Injective f := by
    rw [hf, MonoidHom.noncommCoprod_injective]
    refine ⟨(zpowers c).subtype_injective, (zpowers a).subtype_injective, ?_⟩
    rwa [range_subtype, range_subtype]
  have hfrange : f.range = zpowers c ⊔ zpowers a := by
    rw [hf, MonoidHom.noncommCoprod_range, range_subtype, range_subtype]
  have hcardsup : Nat.card (zpowers c ⊔ zpowers a : Subgroup G) = 8 := by
    rw [← hfrange, ← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, Nat.card_prod,
      Nat.card_zpowers, Nat.card_zpowers, hc4, ha2]
  have hcardZP : Nat.card (center P) = 8 := by
    rw [← card_map_of_injective (f := P.subtype) P.subtype_injective, hZP, hcardsup]
  have hP' : ⁅P, P⁆ = zpowers z := by
    apply le_antisymm
    · rw [← hQ']; exact commutator_mono hPQ hPQ
    · rw [zpowers_le]
      by_contra hcon
      have hall : ∀ x ∈ P, ∀ y ∈ P, y * x = x * y := by
        intro x hx y hy
        refine (hcomm1 x y).mp ?_
        rcases hval x (hPQ hx) y (hPQ hy) with h | h
        · exact h
        · exact absurd (h ▸ commutator_mem_commutator hx hy) hcon
      have htop : center P = ⊤ := eq_top_iff.mpr fun x _ =>
        mem_center_iff.mpr fun g => Subtype.ext (hall x x.2 g g.2)
      have : Nat.card P = 8 := by rw [← hcardZP, htop, card_top]
      rw [hcardP] at this
      have : 2 ^ 5 ≤ 2 ^ (2 * v + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  have hiso : Nonempty (center P ≃* Multiplicative (ZMod 4) × Multiplicative (ZMod 2)) := by
    have e1 := (center P).equivMapOfInjective P.subtype P.subtype_injective
    have e2 := MulEquiv.subgroupCongr (hZP.trans hfrange.symm)
    have e3 := (MonoidHom.ofInjective hfinj).symm
    have ec : zpowers c ≃* Multiplicative (ZMod 4) :=
      (zmodCyclicMulEquiv inferInstance).symm.trans
        (AddEquiv.toMultiplicative (ZMod.ringEquivCongr (by rw [Nat.card_zpowers, hc4])).toAddEquiv)
    have ea : zpowers a ≃* Multiplicative (ZMod 2) :=
      (zmodCyclicMulEquiv inferInstance).symm.trans
        (AddEquiv.toMultiplicative (ZMod.ringEquivCongr (by rw [Nat.card_zpowers, ha2])).toAddEquiv)
    exact ⟨((e1.trans e2).trans e3).trans (MulEquiv.prodCongr ec ea)⟩
  have hcN : ∀ i : ℤ, c ^ i ∈ N → c ^ i = 1 := by
    intro i hi
    rw [← zpow_mod_orderOf, hc4] at hi ⊢
    have h0 : 0 ≤ i % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
    have h4 : i % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
    obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le h0
    rw [hr] at hi ⊢
    have hr4 : r < 4 := by omega
    rw [zpow_natCast] at hi ⊢
    interval_cases r
    · exact pow_zero c
    · have := pow_mem hi 2
      rw [pow_one] at this
      exact absurd this hzN
    · exact absurd hi hzN
    · have h6 : (c ^ 3) ^ 2 = c ^ 2 := by
        rw [← pow_mul, show 3 * 2 = orderOf c + 2 by rw [hc4], pow_add, pow_orderOf_eq_one,
          one_mul]
      have := pow_mem hi 2
      rw [h6] at this
      exact absurd this hzN
  have hQN : Q ⊓ N = zpowers a := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxQ, hxN⟩ := mem_inf.mp hx
      have hxP : x ∈ P := mem_inf.mpr ⟨hxQ, hNC hxN⟩
      have hxc : ∀ y ∈ P, y * x = x * y := by
        intro y hy
        refine (hcomm1 y x).mp ?_ |>.symm
        rcases hval y (hPQ hy) x hxQ with h | h
        · exact (hcomm1 y x).mpr ((hcomm1 y x).mp h)
        · exfalso
          apply hzN
          rw [← h]
          have hconj := hNn.conj_mem ⟨x, hNC hxN⟩ (by rw [mem_subgroupOf]; exact hxN)
            ⟨y, hPC hy⟩
          rw [mem_subgroupOf] at hconj
          rw [commutatorElement_def]
          exact mul_mem (by simpa using hconj) (inv_mem hxN)
      obtain ⟨i, h | h⟩ := hcenP x hxP hxc
      · rw [h, hcN i (h ▸ hxN)]; exact one_mem _
      · have hciN : c ^ i ∈ N := by
          have := mul_mem (h ▸ hxN) (inv_mem haN)
          rwa [mul_inv_cancel_right] at this
        rw [h, hcN i hciN, one_mul]; exact mem_zpowers a
    · rw [zpowers_le]; exact mem_inf.mpr ⟨haQ, haN⟩
  have hle : zpowers a ≤ P := by rw [zpowers_le]; exact haP
  have hcardA : Nat.card ((zpowers a).subgroupOf P) = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, ha2]
  have hcardquot : Nat.card (P ⧸ (zpowers a).subgroupOf P) = 2 ^ (2 * v) := by
    have h := card_eq_card_quotient_mul_card_subgroup ((zpowers a).subgroupOf P)
    rw [hcardA, hcardP, pow_succ] at h
    exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h).symm
  have hzA : ∀ w : G, (w = 1 ∨ w = z) → w ∈ zpowers a → w = 1 := by
    rintro w (rfl | rfl) hw
    · rfl
    · rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_eq_two ha2 hw with h | h
      · exact h
      · exact absurd (h ▸ pow_mem (mem_zpowers c) 2) haZ
  have hcenquot : center (P ⧸ (zpowers a).subgroupOf P) =
      (center P).map (QuotientGroup.mk' _) := by
    apply le_antisymm
    · intro q hq
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      refine ⟨x, mem_center_iff.mpr fun y => ?_, rfl⟩
      have h := mem_center_iff.mp hq (QuotientGroup.mk y)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf] at h
      have hw : ((y * x)⁻¹ * (x * y) : P) = ⁅(x : G)⁻¹, (y : G)⁻¹⁆ := by
        simp only [coe_mul, coe_inv, commutatorElement_def, inv_inv]; group
      rw [hw] at h
      have hv := hval _ (inv_mem (hPQ x.2)) _ (inv_mem (hPQ y.2))
      have h1 := hzA _ hv h
      rw [hinvl _ (hPQ x.2) _ (inv_mem (hPQ y.2)), hinvr _ (hPQ x.2) _ (hPQ y.2)] at h1
      exact Subtype.ext ((hcomm1 _ _).mp h1)
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_center_iff.mpr fun g => by
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
        rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          mem_center_iff.mp hx y]
  set cbar : P ⧸ (zpowers a).subgroupOf P := QuotientGroup.mk ⟨c, hcP⟩ with hcbar
  have habar : (QuotientGroup.mk ⟨a, haP⟩ : P ⧸ (zpowers a).subgroupOf P) = 1 := by
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]; exact mem_zpowers a
  have hcenquot' : center (P ⧸ (zpowers a).subgroupOf P) = zpowers cbar := by
    rw [hcenquot]
    apply le_antisymm
    · rintro _ ⟨⟨x, hxP⟩, hxc, rfl⟩
      obtain ⟨i, h | h⟩ := hcenP x hxP fun y hy =>
        congrArg Subtype.val (mem_center_iff.mp hxc ⟨y, hy⟩)
      · refine mem_zpowers_iff.mpr ⟨i, ?_⟩
        have hx : (⟨x, hxP⟩ : P) = ⟨c, hcP⟩ ^ i :=
          Subtype.ext (by simp only [SubgroupClass.coe_zpow]; exact h)
        rw [QuotientGroup.mk'_apply, hx, hcbar, QuotientGroup.mk_zpow]
      · refine mem_zpowers_iff.mpr ⟨i, ?_⟩
        have hx : (⟨x, hxP⟩ : P) = ⟨c, hcP⟩ ^ i * ⟨a, haP⟩ :=
          Subtype.ext (by simp only [coe_mul, SubgroupClass.coe_zpow]; exact h)
        rw [QuotientGroup.mk'_apply, hx, QuotientGroup.mk_mul, habar, mul_one, hcbar,
          QuotientGroup.mk_zpow]
    · rw [zpowers_le]
      exact ⟨⟨c, hcP⟩, hcenc, rfl⟩
  have hcbar2 : cbar ^ 2 ≠ 1 := by
    rw [hcbar, ← QuotientGroup.mk_pow, Ne, QuotientGroup.eq_one_iff, mem_subgroupOf]
    intro h
    exact hz1 (hzA _ (Or.inr rfl) (by simpa using h))
  have hcbar4 : cbar ^ 4 = 1 := by
    rw [hcbar, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
    have : (((⟨c, hcP⟩ : P) ^ 4 : P) : G) = 1 := by
      rw [SubgroupClass.coe_pow, ← hc4, pow_orderOf_eq_one]
    rw [this]
    exact one_mem _
  have hocbar : orderOf cbar = 4 :=
    orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hcbar2) (by simpa using hcbar4)
  set φ₀ : P →* centralizer {a} ⧸ N.subgroupOf (centralizer {a}) :=
    (QuotientGroup.mk' _).comp (inclusion hPC) with hφ₀
  have hkerφ₀ : (zpowers a).subgroupOf P = φ₀.ker := by
    ext x
    rw [mem_subgroupOf, MonoidHom.mem_ker, hφ₀, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf, coe_inclusion]
    constructor
    · intro hx
      exact (hQN ▸ hx : (x : G) ∈ Q ⊓ N).2
    · intro hx
      exact hQN ▸ mem_inf.mpr ⟨hPQ x.2, hx⟩
  refine ⟨hidx, hP', hZP, hiso, hQN, hcardquot, hcenquot, hcenquot' ▸ inferInstance,
    by rw [hcenquot', Nat.card_zpowers, hocbar], ⟨(QuotientGroup.kerLift φ₀).comp
      (QuotientGroup.quotientMulEquivOfEq hkerφ₀).toMonoidHom, ?_, fun p => rfl⟩, ?_⟩
  · exact (QuotientGroup.kerLift_injective φ₀).comp (QuotientGroup.quotientMulEquivOfEq
      hkerφ₀).injective
  ·
    have hcC : c ∈ centralizer {a} := hPC hcP
    refine ⟨QuotientGroup.mk ⟨c, hcC⟩, orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_⟩
    · rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hzN
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      have : (((⟨c, hcC⟩ : centralizer {a}) ^ 2 ^ (1 + 1) : centralizer {a}) : G) = 1 := by
        rw [SubgroupClass.coe_pow, show 2 ^ (1 + 1) = orderOf c by rw [hc4]; norm_num,
          pow_orderOf_eq_one]
      rw [this]
      exact one_mem _

end CFSG.LocalAnalysis.GorensteinLyons
