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
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
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

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.BMRows.M13Normal

theorem le_normalCore_of_small_index {C : Type*} [Group C] [Finite C] {Q H : Subgroup C}
    [IsSimpleGroup ↥Q] (hidx : H.index ≤ 5) (hQ : 120 < Nat.card ↥Q) : Q ≤ H.normalCore := by
  classical
  let ψ : ↥Q →* Equiv.Perm (C ⧸ H) := (MulAction.toPermHom C (C ⧸ H)).comp Q.subtype
  have hker : ψ.ker = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exfalso
      have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).1 h
      have h1 : Nat.card ↥Q ≤ Nat.card (Equiv.Perm (C ⧸ H)) :=
        Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_perm] at h1
      have h2 : Nat.card (C ⧸ H) ≤ 5 := hidx
      have h3 : (Nat.card (C ⧸ H)).factorial ≤ (5 : ℕ).factorial := Nat.factorial_le h2
      have h4 : (5 : ℕ).factorial = 120 := by decide
      omega
    · exact h
  intro q hq
  rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker]
  have : (⟨q, hq⟩ : ↥Q) ∈ ψ.ker := hker ▸ Subgroup.mem_top _
  exact this

theorem normal_of_commutator {C : Type*} [Group C] {Q K H : Subgroup C} [K.Normal]
    (hQK : Q ≤ K) (hKH : K ≤ H) (hcomm : ⁅H, H⁆ ≤ Q) (hperf : ⁅Q, Q⁆ = Q) : Q.Normal := by
  have h1 : ⁅K, K⁆ = Q := le_antisymm ((Subgroup.commutator_mono hKH hKH).trans hcomm)
    (calc Q = ⁅Q, Q⁆ := hperf.symm
      _ ≤ ⁅K, K⁆ := Subgroup.commutator_mono hQK hQK)
  rw [← h1]
  exact Subgroup.commutator_normal K K

theorem commutator_self_eq {C : Type*} [Group C] {Q : Subgroup C}
    (h : commutator ↥Q = ⊤) : ⁅Q, Q⁆ = Q := by
  have hr : (⊤ : Subgroup ↥Q).map Q.subtype = Q := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h1 : (commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
    rw [commutator_def, Subgroup.map_commutator, hr]
  rw [← h1, h, hr]

theorem center_eq_bot_of_simple_nonab {J : Type*} [Group J] [IsSimpleGroup J]
    (hnab : ∃ a b : J, a * b ≠ b * a) : Subgroup.center J = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a)

theorem commutator_eq_top_of_simple_nonab {J : Type*} [Group J] [IsSimpleGroup J]
    (hnab : ∃ a b : J, a * b ≠ b * a) : commutator J = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator J) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
  · exact h

theorem eq_one_of_central {G : Type*} [Group G] {Q : Subgroup G} [IsSimpleGroup ↥Q]
    (hnab : ∃ a b : ↥Q, a * b ≠ b * a) : ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) → z = 1 := by
  intro z hz hc
  have hmem : (⟨z, hz⟩ : ↥Q) ∈ Subgroup.center ↥Q :=
    Subgroup.mem_center_iff.2 fun q => Subtype.ext (hc q q.2)
  rw [center_eq_bot_of_simple_nonab hnab, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

theorem commutator_mul_central_left {C : Type*} [Group C] {a g z : C}
    (hz : ∀ h : C, z * h = h * z) : ⁅a * z, g⁆ = ⁅a, g⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * z * g * (a * z)⁻¹ * g⁻¹ = a * (z * g) * z⁻¹ * a⁻¹ * g⁻¹ := by group
    _ = a * (g * z) * z⁻¹ * a⁻¹ * g⁻¹ := by rw [hz g]
    _ = a * g * a⁻¹ * g⁻¹ := by group

theorem commutator_mul_central_right {C : Type*} [Group C] {a b z : C}
    (hz : ∀ h : C, z * h = h * z) : ⁅a, b * z⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * z) * a⁻¹ * (b * z)⁻¹ = a * b * (z * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * z) * z⁻¹ * b⁻¹ := by rw [hz a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem conj_mem_of_small_index {G : Type*} [Group G] [Finite G] {x : G} {Q : Subgroup G}
    [IsSimpleGroup ↥Q] (hnab : ∃ a b : ↥Q, a * b ≠ b * a)
    (hQC : Q ≤ Subgroup.centralizer ({x} : Set G)) (hQ : 120 < Nat.card ↥Q)
    (hC : Nat.card ↥(Subgroup.centralizer ({x} : Set G)) <
      6 * (Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥Q)) :
    ∀ g ∈ Subgroup.centralizer ({x} : Set G), ∀ l ∈ Q, g * l * g⁻¹ ∈ Q := by
  classical
  set C : Subgroup G := Subgroup.centralizer ({x} : Set G) with hCdef
  have hxC : x ∈ C := Subgroup.mem_centralizer_singleton_iff.2 rfl
  let x' : ↥C := ⟨x, hxC⟩
  let Q' : Subgroup ↥C := Q.subgroupOf C
  let eQ : ↥Q' ≃* ↥Q := Subgroup.subgroupOfEquivOfLe hQC
  haveI hs' : IsSimpleGroup ↥Q' := (MulEquiv.isSimpleGroup_congr eQ).2 inferInstance
  have hnab' : ∃ a b : ↥Q', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eQ.symm a, eQ.symm b, fun h => hab (by simpa using congrArg eQ h)⟩
  have hQ' : 120 < Nat.card ↥Q' := by rwa [Nat.card_congr eQ.toEquiv]
  have hZ : ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) → z = 1 := eq_one_of_central hnab
  have hcent : ∀ c : ↥C, x' * c = c * x' := fun c =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2).symm
  have hx'c : x' ∈ Subgroup.center ↥C := Subgroup.mem_center_iff.2 fun c => (hcent c).symm
  have hzc : Subgroup.zpowers x' ≤ Subgroup.center ↥C := by
    rw [Subgroup.zpowers_le]
    exact hx'c
  haveI hZn : (Subgroup.zpowers x').Normal := by
    constructor
    intro n hn g
    have hnc : n ∈ Subgroup.center ↥C := hzc hn
    rw [Subgroup.mem_center_iff] at hnc
    have : g * n * g⁻¹ = n := by rw [hnc g]; group
    rw [this]
    exact hn
  let H : Subgroup ↥C := Q' ⊔ Subgroup.zpowers x'
  have hinf : Q' ⊓ Subgroup.zpowers x' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyQ, hyZ⟩
    rw [Subgroup.mem_bot]
    have hy : ((y : ↥C) : G) = 1 := by
      refine hZ _ hyQ fun q hq => ?_
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hyZ
      have hxq : q * x = x * q := Subgroup.mem_centralizer_singleton_iff.1 (hQC hq)
      have : ((y : ↥C) : G) = x ^ k := by rw [← hk]; rfl
      rw [this]
      exact ((Commute.zpow_right (show Commute q x from hxq) k)).eq
    exact Subtype.ext hy
  have hcardZ : Nat.card ↥(Subgroup.zpowers x') = Nat.card ↥(Subgroup.zpowers x) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, ← Subgroup.orderOf_coe x']
  have hHcard : Nat.card ↥(Subgroup.zpowers x) * Nat.card ↥Q ≤ Nat.card ↥H := by
    rw [← hcardZ, ← Nat.card_congr eQ.toEquiv, mul_comm, ← Nat.card_prod]
    refine Nat.card_le_card_of_injective
      (fun p : ↥Q' × ↥(Subgroup.zpowers x') => (⟨p.1 * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥H))
      ?_
    rintro ⟨⟨q₁, hq₁⟩, ⟨z₁, hz₁⟩⟩ ⟨⟨q₂, hq₂⟩, ⟨z₂, hz₂⟩⟩ h
    have h' : q₁ * z₁ = q₂ * z₂ := congrArg Subtype.val h
    have hm : q₂⁻¹ * q₁ = z₂ * z₁⁻¹ :=
      calc q₂⁻¹ * q₁ = q₂⁻¹ * (q₁ * z₁) * z₁⁻¹ := by group
        _ = q₂⁻¹ * (q₂ * z₂) * z₁⁻¹ := by rw [h']
        _ = z₂ * z₁⁻¹ := by group
    have hmem : q₂⁻¹ * q₁ ∈ Q' ⊓ Subgroup.zpowers x' :=
      ⟨Q'.mul_mem (Q'.inv_mem hq₂) hq₁, hm ▸ Subgroup.mul_mem _ hz₂ (Subgroup.inv_mem _ hz₁)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at hmem
    subst hmem
    have : z₁ = z₂ := mul_left_cancel h'
    subst this
    rfl
  have hidx : H.index ≤ 5 := by
    have h1 := Subgroup.card_mul_index H
    have hHpos : 0 < Nat.card ↥H := Nat.card_pos
    by_contra hgt
    push Not at hgt
    have h2 : Nat.card ↥H * 6 ≤ Nat.card ↥H * H.index := Nat.mul_le_mul_left _ hgt
    omega
  have hcore : Q' ≤ H.normalCore := le_normalCore_of_small_index hidx hQ'
  have hcomm : ⁅H, H⁆ ≤ Q' := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a, ha, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg₁
    obtain ⟨b, hb, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 hg₂
    have hz₁c : ∀ h : ↥C, z₁ * h = h * z₁ := fun h =>
      (Subgroup.mem_center_iff.1 (hzc hz₁) h).symm
    have hz₂c : ∀ h : ↥C, z₂ * h = h * z₂ := fun h =>
      (Subgroup.mem_center_iff.1 (hzc hz₂) h).symm
    rw [commutator_mul_central_left hz₁c, commutator_mul_central_right hz₂c, commutatorElement_def]
    exact Q'.mul_mem (Q'.mul_mem (Q'.mul_mem ha hb) (Q'.inv_mem ha)) (Q'.inv_mem hb)
  have hperf' : ⁅Q', Q'⁆ = Q' := commutator_self_eq (commutator_eq_top_of_simple_nonab hnab')
  haveI : H.normalCore.Normal := inferInstance
  have hQn : Q'.Normal := normal_of_commutator hcore (Subgroup.normalCore_le H) hcomm hperf'
  intro g hg l hl
  exact hQn.conj_mem (⟨l, hQC hl⟩ : ↥C) hl (⟨g, hg⟩ : ↥C)

theorem card_mul_cent_le {G : Type*} [Group G] [Finite G] {x : G} {Q : Subgroup G}
    (hQC : Q ≤ Subgroup.centralizer ({x} : Set G))
    (hZ : ∀ z ∈ Q, (∀ q ∈ Q, q * z = z * q) → z = 1) (u : ↥Q) :
    Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (Q : Set G)) *
        Nat.card ↥(Subgroup.centralizer ({u} : Set ↥Q)) ≤
      Nat.card ↥(Subgroup.centralizer ({(u : G)} : Set G) ⊓
        Subgroup.centralizer ({x} : Set G)) := by
  set Z : Subgroup G := Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer (Q : Set G)
    with hZdef
  set R : Subgroup ↥Q := Subgroup.centralizer ({u} : Set ↥Q) with hRdef
  set T : Subgroup G := Subgroup.centralizer ({(u : G)} : Set G) ⊓
    Subgroup.centralizer ({x} : Set G) with hTdef
  have hzQ : ∀ z ∈ Z, ∀ q ∈ Q, q * z = z * q := fun z hz q hq =>
    Subgroup.mem_centralizer_iff.1 hz.2 q hq
  have hzx : ∀ z ∈ Z, z * x = x * z := fun z hz => Subgroup.mem_centralizer_singleton_iff.1 hz.1
  have hqx : ∀ q ∈ Q, q * x = x * q := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.1 (hQC hq)
  have hmem : ∀ p : ↥Z × ↥R, ((p.1 : G) * (((p.2 : ↥Q)) : G)) ∈ T := by
    rintro ⟨⟨z, hz⟩, ⟨q, hq⟩⟩
    have hqu : q * u = u * q := Subgroup.mem_centralizer_singleton_iff.1 hq
    have hqu' : (q : G) * u = u * q := congrArg Subtype.val hqu
    have hzu : (u : G) * z = z * u := hzQ z hz u u.2
    refine ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · show z * q * u = u * (z * q)
      rw [mul_assoc, hqu', ← mul_assoc, ← hzu, mul_assoc]
    · show z * q * x = x * (z * q)
      rw [mul_assoc, hqx q q.2, ← mul_assoc, hzx z hz, mul_assoc]
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_injective (fun p : ↥Z × ↥R => (⟨_, hmem p⟩ : ↥T)) ?_
  rintro ⟨⟨z₁, hz₁⟩, ⟨q₁, hq₁⟩⟩ ⟨⟨z₂, hz₂⟩, ⟨q₂, hq₂⟩⟩ h
  have h' : z₁ * (q₁ : G) = z₂ * (q₂ : G) := congrArg Subtype.val h
  have hy : z₂⁻¹ * z₁ = (q₂ : G) * (q₁ : G)⁻¹ :=
    calc z₂⁻¹ * z₁ = z₂⁻¹ * (z₁ * (q₁ : G)) * (q₁ : G)⁻¹ := by group
      _ = z₂⁻¹ * (z₂ * (q₂ : G)) * (q₁ : G)⁻¹ := by rw [h']
      _ = (q₂ : G) * (q₁ : G)⁻¹ := by group
  have hyQ : z₂⁻¹ * z₁ ∈ Q := hy ▸ Q.mul_mem q₂.2 (Q.inv_mem q₁.2)
  have hy1 : z₂⁻¹ * z₁ = 1 := by
    refine hZ _ hyQ fun q hq => ?_
    have h1 : q * z₁ = z₁ * q := hzQ z₁ hz₁ q hq
    have h2 : q * z₂⁻¹ = z₂⁻¹ * q := by
      have := hzQ z₂ hz₂ q hq
      calc q * z₂⁻¹ = z₂⁻¹ * (z₂ * q) * z₂⁻¹ := by group
        _ = z₂⁻¹ * (q * z₂) * z₂⁻¹ := by rw [this]
        _ = z₂⁻¹ * q := by group
    rw [← mul_assoc, h2, mul_assoc, h1, mul_assoc]
  have hz : z₁ = z₂ := by
    have : z₁ = z₂ * (z₂⁻¹ * z₁) := by group
    rw [this, hy1, mul_one]
  subst hz
  have hq : (q₁ : G) = q₂ := mul_left_cancel h'
  have hq' : q₁ = q₂ := Subtype.ext hq
  subst hq'
  rfl

theorem isPGroup_of_card_lt {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] {Z : Subgroup G}
    [Finite Z] {x : G} (hx : x ∈ Z) (hxo : orderOf x = p) {m N : ℕ} (hm : 0 < m)
    (hZ : Nat.card ↥Z * m ≤ N) (hN : N < 2 * p * m) : IsPGroup p ↥Z := by
  have hdvd : p ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : ↥Z)
    rwa [Subgroup.orderOf_mk, hxo] at this
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, mul_zero] at hk
      exact absurd hk Nat.card_pos.ne'
    · exact h
  have hk1 : k = 1 := by
    by_contra hne
    have hk2 : 2 ≤ k := by omega
    have : 2 * p * m ≤ Nat.card ↥Z * m := by
      rw [hk]
      exact Nat.mul_le_mul_right m (by nlinarith)
    omega
  exact IsPGroup.of_card (n := 1) (by rw [hk, hk1, mul_one, pow_one])

end CFSG.HardMathSupport.Dickson.BMRows.M13Normal
