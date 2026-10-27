module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Theorem5_1
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

namespace CFSG.LargeExtraspecial.S14.W4Loc

open Subgroup

variable {K V : Type*} [Group K] [Finite K] [Group V] (f : K →* V)

omit [Finite K] in
theorem inf_ker_eq_bot (hf : ∀ y : K, (∃ n : ℕ, y ^ 2 ^ n = 1) → f y = 1 → y = 1)
    {L : Subgroup K} (hL : IsPGroup 2 L) : L ⊓ f.ker = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun y hy => ?_
  obtain ⟨n, hn⟩ := hL ⟨y, hy.1⟩
  exact hf y ⟨n, congrArg Subtype.val hn⟩ hy.2

theorem odd_card_ker (hf : ∀ y : K, (∃ n : ℕ, y ^ 2 ^ n = 1) → f y = 1 → y = 1) :
    ¬ 2 ∣ Nat.card f.ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hy2 : (y : K) ^ 2 ^ 1 = 1 := by
    have := congrArg Subtype.val (pow_orderOf_eq_one y)
    rw [hy] at this
    simpa using this
  have h1 : (y : K) = 1 := hf y ⟨1, hy2⟩ y.2
  have : y = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hy
  norm_num at hy

omit [Finite K] in
theorem mem_sup_ker_iff {L : Subgroup K} {z : K} :
    z ∈ L ⊔ f.ker ↔ ∃ ℓ ∈ L, ∃ y ∈ f.ker, ℓ * y = z := by
  rw [← SetLike.mem_coe, Subgroup.mul_normal L f.ker, Set.mem_mul]
  rfl

omit [Finite K] in
theorem conj_mem_sup_ker {L : Subgroup K} {a : K}
    (ha : f a ∈ normalizer ((L.map f : Subgroup V) : Set V)) {z : K} (hz : z ∈ L ⊔ f.ker) :
    a * z * a⁻¹ ∈ L ⊔ f.ker := by
  obtain ⟨ℓ, hℓ, y, hy, rfl⟩ := (mem_sup_ker_iff f).mp hz
  have h1 : f a * f ℓ * (f a)⁻¹ ∈ L.map f :=
    (mem_normalizer_iff.mp ha (f ℓ)).mp (Subgroup.mem_map_of_mem f hℓ)
  obtain ⟨ℓ', hℓ', he⟩ := Subgroup.mem_map.mp h1
  have hk : ℓ'⁻¹ * (a * ℓ * a⁻¹) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, map_inv, he]
    group
  have hy' : a * y * a⁻¹ ∈ f.ker := (MonoidHom.normal_ker f).conj_mem y hy a
  have e : a * (ℓ * y) * a⁻¹ = ℓ' * ((ℓ'⁻¹ * (a * ℓ * a⁻¹)) * (a * y * a⁻¹)) := by group
  rw [e]
  exact mul_mem (mem_sup_left hℓ') (mem_sup_right (mul_mem hk hy'))

theorem exists_conj_normalizes {G : Type*} [Group G] [Finite G] {Y L L' : Subgroup G}
    [hY : Y.Normal] (hYodd : ¬ 2 ∣ Nat.card Y) (hL : IsPGroup 2 L) (hLY : L ⊓ Y = ⊥)
    [hN : (L ⊔ Y).Normal] (hL' : IsPGroup 2 L') :
    ∃ y ∈ Y, ∀ a ∈ L', ∀ ℓ ∈ L, ∃ ℓ' ∈ L, a * (y * ℓ * y⁻¹) * a⁻¹ = y * ℓ' * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hL'.exists_le_sylow
  obtain ⟨P, hP⟩ := CFSG.Glauberman.sylow_inf_normal S (N := L ⊔ Y)
  have hLN : L ≤ L ⊔ Y := le_sup_left
  have hcardN : Nat.card (L ⊔ Y : Subgroup G) = Nat.card L * Nat.card Y := by
    have h1 := Subgroup.relIndex_mul_card Y (L ⊔ Y)
    rw [inf_of_le_left le_sup_right, Subgroup.relIndex_sup_right] at h1
    have h2 := Subgroup.relIndex_mul_card Y L
    rw [inf_comm, hLY, Subgroup.card_bot, mul_one] at h2
    rw [← h1, h2, mul_comm]
  have hidx : ¬ 2 ∣ (L.subgroupOf (L ⊔ Y)).index := by
    have h3 := Subgroup.relIndex_mul_card L (L ⊔ Y)
    rw [inf_of_le_left hLN, hcardN] at h3
    have h4 : L.relIndex (L ⊔ Y) = Nat.card Y :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h3, mul_comm])
    change ¬ 2 ∣ L.relIndex (L ⊔ Y)
    rw [h4]
    exact hYodd
  have hLp : IsPGroup 2 (L.subgroupOf (L ⊔ Y)) :=
    hL.of_equiv (Subgroup.subgroupOfEquivOfLe hLN).symm
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq (L ⊔ Y : Subgroup G) (hLp.toSylow hidx) P
  have hn' : (n : G) ∈ (↑(Y ⊔ L) : Set G) := by rw [sup_comm]; exact n.2
  rw [Subgroup.normal_mul Y L, Set.mem_mul] at hn'
  obtain ⟨y, hy, ℓ₀, hℓ₀, hyl⟩ := hn'
  have hmem : ∀ z : G, z ∈ (S : Subgroup G) ⊓ (L ⊔ Y) ↔ (n : G)⁻¹ * z * n ∈ L := by
    intro z
    constructor
    · intro hz
      have hzP : (⟨z, hz.2⟩ : (L ⊔ Y : Subgroup G)) ∈ (P : Subgroup (L ⊔ Y : Subgroup G)) := by
        rw [hP]; exact hz
      rw [← hn, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hzP
      exact hzP
    · intro hz
      have hzN : z ∈ L ⊔ Y := by
        have : (n : G) * ((n : G)⁻¹ * z * n) * (n : G)⁻¹ ∈ L ⊔ Y :=
          mul_mem (mul_mem n.2 (hLN hz)) (inv_mem n.2)
        simpa [mul_assoc] using this
      have hzP : (⟨z, hzN⟩ : (L ⊔ Y : Subgroup G)) ∈ (P : Subgroup (L ⊔ Y : Subgroup G)) := by
        rw [← hn, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
        exact hz
      rw [hP] at hzP
      exact Subgroup.mem_subgroupOf.mp hzP
  refine ⟨y, hy, fun a ha ℓ hℓ => ?_⟩
  have e1 : y * ℓ * y⁻¹ ∈ (S : Subgroup G) ⊓ (L ⊔ Y) := by
    refine (hmem _).mpr ?_
    rw [← hyl]
    have : ℓ₀⁻¹ * ℓ * ℓ₀ ∈ L := mul_mem (mul_mem (inv_mem hℓ₀) hℓ) hℓ₀
    simpa [mul_assoc] using this
  have e2 : a * (y * ℓ * y⁻¹) * a⁻¹ ∈ (S : Subgroup G) ⊓ (L ⊔ Y) :=
    ⟨mul_mem (mul_mem (hS ha) e1.1) ((S : Subgroup G).inv_mem (hS ha)), hN.conj_mem _ e1.2 a⟩
  have e3 := (hmem _).mp e2
  rw [← hyl] at e3
  refine ⟨ℓ₀ * ((y * ℓ₀)⁻¹ * (a * (y * ℓ * y⁻¹) * a⁻¹) * (y * ℓ₀)) * ℓ₀⁻¹,
    mul_mem (mul_mem hℓ₀ e3) (inv_mem hℓ₀), ?_⟩
  group

theorem map_conj_eq_of_weaklyClosed (hf : ∀ y : K, (∃ n : ℕ, y ^ 2 ^ n = 1) → f y = 1 → y = 1)
    {L : Subgroup K} (hL : IsPGroup 2 L)
    (hwc : ∀ x : K, (∀ a ∈ L.map (MulAut.conj x).toMonoidHom, ∀ ℓ ∈ L, a * ℓ * a⁻¹ ∈ L) →
      L.map (MulAut.conj x).toMonoidHom = L)
    (x : K) (hx : ∀ a ∈ L.map (MulAut.conj x).toMonoidHom,
      f a ∈ normalizer ((L.map f : Subgroup V) : Set V)) :
    (L.map (MulAut.conj x).toMonoidHom).map f = L.map f := by
  set L' := L.map (MulAut.conj x).toMonoidHom with hL'
  set N := L ⊔ f.ker with hNdef
  set J := normalizer (N : Set K) with hJ
  have hL'J : L' ≤ J := by
    intro a ha
    refine mem_normalizer_iff.mpr fun z => ⟨fun hz => conj_mem_sup_ker f (hx a ha) hz,
      fun hz => ?_⟩
    have := conj_mem_sup_ker f (hx a⁻¹ (inv_mem ha)) hz
    simpa [mul_assoc] using this
  have hNJ : N ≤ J := le_normalizer
  have hLJ : L ≤ J := le_sup_left.trans hNJ
  have hYJ : f.ker ≤ J := le_sup_right.trans hNJ
  have : (f.ker.subgroupOf J).Normal := (MonoidHom.normal_ker f).subgroupOf J
  have hYodd : ¬ 2 ∣ Nat.card (f.ker.subgroupOf J) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYJ).toEquiv]
    exact odd_card_ker f hf
  have hLp : IsPGroup 2 (L.subgroupOf J) := hL.of_equiv (Subgroup.subgroupOfEquivOfLe hLJ).symm
  have hLY : L.subgroupOf J ⊓ f.ker.subgroupOf J = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => Subtype.ext ?_
    have hz' : (z : K) ∈ L ⊓ f.ker :=
      ⟨Subgroup.mem_subgroupOf.mp hz.1, Subgroup.mem_subgroupOf.mp hz.2⟩
    rw [inf_ker_eq_bot f hf hL] at hz'
    exact Subgroup.mem_bot.mp hz'
  have : (L.subgroupOf J ⊔ f.ker.subgroupOf J).Normal := by
    rw [← Subgroup.subgroupOf_sup hLJ hYJ]
    exact Subgroup.normal_in_normalizer
  have hL'p : IsPGroup 2 (L'.subgroupOf J) :=
    (hL.map _).of_equiv (Subgroup.subgroupOfEquivOfLe hL'J).symm
  obtain ⟨y, hy, hyL⟩ := exists_conj_normalizes hYodd hLp hLY hL'p
  have hfy : f (y : K) = 1 := hy
  have key : L.map (MulAut.conj ((y : K)⁻¹ * x)).toMonoidHom = L := by
    refine hwc _ fun b hb ℓ hℓ => ?_
    obtain ⟨ℓ₁, hℓ₁, rfl⟩ := Subgroup.mem_map.mp hb
    have ha : x * ℓ₁ * x⁻¹ ∈ L' := Subgroup.mem_map_of_mem _ hℓ₁
    obtain ⟨ℓ', hℓ', he⟩ := hyL ⟨_, hL'J ha⟩ (Subgroup.mem_subgroupOf.mpr ha) ⟨ℓ, hLJ hℓ⟩
      (Subgroup.mem_subgroupOf.mpr hℓ)
    have he' := congrArg Subtype.val he
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at he'
    have hℓ'' : ((ℓ' : J) : K) ∈ L := Subgroup.mem_subgroupOf.mp hℓ'
    have e : MulAut.conj ((y : K)⁻¹ * x) ℓ₁ * ℓ * (MulAut.conj ((y : K)⁻¹ * x) ℓ₁)⁻¹ =
        (y : K)⁻¹ * ((x * ℓ₁ * x⁻¹) * ((y : K) * ℓ * (y : K)⁻¹) * (x * ℓ₁ * x⁻¹)⁻¹) * y := by
      simp only [MulAut.conj_apply]
      group
    simp only [MulEquiv.coe_toMonoidHom]
    rw [e, he']
    simpa [mul_assoc] using hℓ''
  ext v
  constructor
  · rintro ⟨_, ⟨ℓ₁, hℓ₁, rfl⟩, rfl⟩
    have hm : (y : K)⁻¹ * (x * ℓ₁ * x⁻¹) * y ∈ L := by
      rw [← key]
      exact ⟨ℓ₁, hℓ₁, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    refine ⟨_, hm, ?_⟩
    simp only [map_mul, map_inv, hfy, inv_one, one_mul, mul_one, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
  · rintro ⟨ℓ, hℓ, rfl⟩
    rw [← key] at hℓ
    obtain ⟨ℓ₁, hℓ₁, he⟩ := Subgroup.mem_map.mp hℓ
    refine ⟨x * ℓ₁ * x⁻¹, Subgroup.mem_map_of_mem _ hℓ₁, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    rw [← he]
    simp only [map_mul, map_inv, hfy, inv_one, one_mul]

end CFSG.LargeExtraspecial.S14.W4Loc
