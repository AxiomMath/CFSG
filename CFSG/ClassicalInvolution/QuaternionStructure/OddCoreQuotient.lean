module

public import CFSG.GroupTheory.PCore.Defs
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
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.ClassicalInvolution.QuaternionStructure

open CFSG

theorem quaternionGroup_eq_a_of_orderOf_eq_two {N : ℕ} [NeZero N] {q : QuaternionGroup N}
    (hq : orderOf q = 2) : q = QuaternionGroup.a (N : ZMod (2 * N)) := by
  cases q with
  | xa i =>
    have hfour := QuaternionGroup.orderOf_xa i
    omega
  | a i =>
    have hi_ne : i ≠ 0 := by
      intro hi
      subst i
      simp at hq
    have hpow := pow_orderOf_eq_one (QuaternionGroup.a i)
    rw [hq] at hpow
    rw [pow_two, QuaternionGroup.a_mul_a, QuaternionGroup.one_def, QuaternionGroup.a.injEq] at hpow
    have hcast : ((2 * i.val : ℕ) : ZMod (2 * N)) = 0 := by
      calc
        (↑(2 * i.val) : ZMod (2 * N)) = 2 * (↑i.val : ZMod (2 * N)) := by norm_num
        _ = i + i := by rw [ZMod.natCast_zmod_val]; noncomm_ring
        _ = 0 := hpow
    have hdvd2 : 2 * N ∣ 2 * i.val := (ZMod.natCast_eq_zero_iff (2 * i.val) (2 * N)).mp hcast
    have hdvd : N ∣ i.val := Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd2
    have hval_ne : i.val ≠ 0 := by simpa [ZMod.val_eq_zero] using hi_ne
    have hval : i.val = N := Nat.eq_of_dvd_of_lt_two_mul hval_ne hdvd (ZMod.val_lt i)
    rw [← ZMod.natCast_zmod_val i, hval]

theorem eq_of_orderOf_eq_two_of_mulEquiv_quaternion {P : Type*} [Group P] {N : ℕ} [NeZero N]
    (e : P ≃* QuaternionGroup N) {x y : P} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  apply e.injective
  rw [quaternionGroup_eq_a_of_orderOf_eq_two (e.orderOf_eq x |>.trans hx),
    quaternionGroup_eq_a_of_orderOf_eq_two (e.orderOf_eq y |>.trans hy)]

theorem oddCore_eq_pPrimeCore_two (G : Type*) [Group G] : oddCore G = pPrimeCore 2 G := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp [Nat.coprime_two_left]

theorem odd_natCard_oddCore (G : Type*) [Group G] [Finite G] : Odd (Nat.card (oddCore G)) := by
  rw [oddCore_eq_pPrimeCore_two]
  exact Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card

theorem not_mem_oddCore_of_orderOf_eq_two {G : Type*} [Group G] [Finite G] {t : G}
    (ht : orderOf t = 2) : t ∉ oddCore G := by
  intro h
  have h1 : orderOf t ∣ Nat.card (oddCore G) := Subgroup.orderOf_dvd_natCard (oddCore G) h
  rw [ht] at h1
  exact (Nat.not_even_iff_odd.mpr (odd_natCard_oddCore G)) (even_iff_two_dvd.mpr h1)

theorem natCard_comap_eq {E G : Type*} [Group E] [Group G] (f : E →* G)
    (hf : Function.Surjective f) (P : Subgroup G) [Finite E] :
    Nat.card (P.comap f) = Nat.card f.ker * Nat.card P := by
  let g : P.comap f →* P := (f.comp (P.comap f).subtype).codRestrict P (fun x => x.2)
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hf y
    refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
    change f x ∈ P
    rw [hx]
    exact y.2
  have hker : g.ker = f.ker.subgroupOf (P.comap f) := by
    ext x
    change ((g x : P) = 1) ↔ f x = 1
    exact Subtype.ext_iff
  have h1 := Subgroup.card_ker_mul_card_of_surjective hg
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (P.ker_le_comap f)).toEquiv] at h1
  exact h1.symm

theorem oddCore_quotient_oddCore_eq_bot (X : Type*) [Group X] [Finite X] :
    oddCore (X ⧸ oddCore X) = ⊥ := by
  let π : X →* X ⧸ oddCore X := QuotientGroup.mk' (oddCore X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = oddCore X := QuotientGroup.ker_mk' _
  let N : Subgroup X := (oddCore (X ⧸ oddCore X)).comap π
  have hNnormal : N.Normal := (inferInstance : (oddCore (X ⧸ oddCore X)).Normal).comap π
  have hcard : Nat.card N = Nat.card (oddCore X) * Nat.card (oddCore (X ⧸ oddCore X)) := by
    rw [natCard_comap_eq π hπ, hker]
  have hodd : Odd (Nat.card N) := by
    rw [hcard]
    exact (odd_natCard_oddCore X).mul (odd_natCard_oddCore _)
  have hle : N ≤ oddCore X := le_sSup ⟨hNnormal, hodd⟩
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hπ x
  have : y ∈ N := hx
  have hy : y ∈ oddCore X := hle this
  have : π y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
  rw [this]
  exact one_mem _

theorem injective_domRestrict_mk' {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) (P : Subgroup G) (hP : IsPGroup 2 P) [Finite P] :
    Function.Injective ((QuotientGroup.mk' N).domRestrict P) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hcop : (Nat.card P).Coprime (Nat.card N) := by
    rw [hm]
    exact (Nat.coprime_two_left.mpr hN).pow_left m
  have hdisj : Disjoint P N := Subgroup.disjoint_of_coprime_natCard hcop
  have hxP : (x : G) ∈ P := x.2
  have hxN : (x : G) ∈ N := by
    have : QuotientGroup.mk' N (x : G) = 1 := hx
    exact (QuotientGroup.eq_one_iff _).mp this
  have : (x : G) ∈ P ⊓ N := ⟨hxP, hxN⟩
  rw [(disjoint_iff.mp hdisj)] at this
  have h1 : (x : G) = 1 := this
  exact Subtype.ext h1

noncomputable def mulEquivMapOfInjective {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (P : Subgroup G) (hf : Function.Injective (f.domRestrict P)) : P ≃* P.map f :=
  (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range P f))

noncomputable def mulEquivMapOddCore {X : Type*} [Group X] [Finite X] (P : Subgroup X)
    (hP : IsPGroup 2 P) : P ≃* P.map (QuotientGroup.mk' (oddCore X)) :=
  mulEquivMapOfInjective _ P (injective_domRestrict_mk' _ (odd_natCard_oddCore X) P hP)

variable {X : Type*} [Group X] [Finite X]

theorem sylow_oddCore_quotient_equiv (S : Sylow 2 X) (P : Sylow 2 (X ⧸ oddCore X)) :
    Nonempty ((P : Subgroup (X ⧸ oddCore X)) ≃* (S : Subgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P', rfl⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective (oddCore X)) 2 P
  exact ⟨((mulEquivMapOddCore (P' : Subgroup X) P'.isPGroup').symm).trans (Sylow.equiv P' S)⟩

theorem sylow_oddCore_quotient_quaternion (S : Sylow 2 X) {n : ℕ}
    (e : (S : Subgroup X) ≃* QuaternionGroup n) (P : Sylow 2 (X ⧸ oddCore X)) :
    Nonempty ((P : Subgroup (X ⧸ oddCore X)) ≃* QuaternionGroup n) := by
  obtain ⟨f⟩ := sylow_oddCore_quotient_equiv S P
  exact ⟨f.trans e⟩

theorem mem_sylow_of_mem_center {G : Type*} [Group G] [Finite G] (P Q : Sylow 2 G) {z : G}
    (hz : z ∈ Subgroup.center G) (hP : z ∈ (P : Subgroup G)) : z ∈ (Q : Subgroup G) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  refine ⟨z, hP, ?_⟩
  have := Subgroup.mem_center_iff.mp hz g
  simp only [MulAut.smul_def, MulAut.conj_apply]
  rw [this, mul_assoc, mul_inv_cancel, mul_one]

theorem exists_central_unique_involution (S : Sylow 2 X)
    (hS : ∃ r : ℕ, 3 ≤ r ∧ Nonempty ((S : Subgroup X) ≃* QuaternionGroup (2 ^ (r - 2))))
    (hBS : ∀ t ∈ (S : Subgroup X), orderOf t = 2 →
      (QuotientGroup.mk t : X ⧸ oddCore X) ∈ Subgroup.center (X ⧸ oddCore X)) :
    ∃ z : X ⧸ oddCore X, orderOf z = 2 ∧ z ∈ Subgroup.center (X ⧸ oddCore X) ∧
      ∀ t : X ⧸ oddCore X, orderOf t = 2 → t = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr, ⟨e⟩⟩ := hS
  have : NeZero (2 ^ (r - 2)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hcard : 2 ∣ Nat.card (S : Subgroup X) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    exact Dvd.dvd.mul_right (by norm_num) _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := (S : Subgroup X)) 2 hcard
  have hu' : orderOf (u : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hcen := hBS (u : X) u.2 hu'
  have hne : ((u : X) : X ⧸ oddCore X) ≠ 1 := fun h =>
    not_mem_oddCore_of_orderOf_eq_two hu' ((QuotientGroup.eq_one_iff _).mp h)
  have hu2 : (u : X) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hu')
  have hsq : ((u : X) : X ⧸ oddCore X) ^ 2 = 1 := by
    rw [← QuotientGroup.mk_pow, hu2, QuotientGroup.mk_one]
  have hord : orderOf (((u : X) : X ⧸ oddCore X)) = 2 := orderOf_eq_prime hsq hne
  refine ⟨((u : X) : X ⧸ oddCore X), hord, hcen, fun t ht => ?_⟩
  let P₀ : Sylow 2 (X ⧸ oddCore X) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (oddCore X)) S
  have hz₀ : ((u : X) : X ⧸ oddCore X) ∈ (P₀ : Subgroup (X ⧸ oddCore X)) :=
    ⟨u, u.2, rfl⟩
  have ht2 : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht]; simp)
  obtain ⟨P, hP⟩ := ht2.exists_le_sylow
  have htP : t ∈ (P : Subgroup (X ⧸ oddCore X)) := hP (Subgroup.mem_zpowers t)
  have hzP : ((u : X) : X ⧸ oddCore X) ∈ (P : Subgroup (X ⧸ oddCore X)) :=
    mem_sylow_of_mem_center P₀ P hcen hz₀
  obtain ⟨f⟩ := sylow_oddCore_quotient_quaternion S e P
  have := eq_of_orderOf_eq_two_of_mulEquiv_quaternion f
    (x := (⟨t, htP⟩ : (P : Subgroup (X ⧸ oddCore X))))
    (y := (⟨((u : X) : X ⧸ oddCore X), hzP⟩ : (P : Subgroup (X ⧸ oddCore X))))
    (by rw [Subgroup.orderOf_mk]; exact ht) (by rw [Subgroup.orderOf_mk]; exact hord)
  exact congrArg Subtype.val this

end CFSG.ClassicalInvolution.QuaternionStructure
