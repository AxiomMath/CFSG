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
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating
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

namespace CFSG.QuasithinUnique.Klein

open Equiv

@[expose] def kleinSet : Finset (Perm (Fin 4)) :=
  {1, swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2}

theorem kleinSet_mul : ∀ a ∈ kleinSet, ∀ b ∈ kleinSet, a * b ∈ kleinSet := by decide

theorem kleinSet_inv : ∀ a ∈ kleinSet, a⁻¹ ∈ kleinSet := by decide

@[expose] def kleinV : Subgroup (Perm (Fin 4)) where
  carrier := ↑kleinSet
  mul_mem' {a b} ha hb := by
    simpa using kleinSet_mul a (by simpa using ha) b (by simpa using hb)
  one_mem' := by decide
  inv_mem' {a} ha := by simpa using kleinSet_inv a (by simpa using ha)

theorem mem_kleinV_iff {g : Perm (Fin 4)} : g ∈ kleinV ↔ g ∈ kleinSet := Iff.rfl

theorem card_kleinV : Nat.card kleinV = 4 := by
  have h : Nat.card kleinV = Nat.card (kleinSet : Set (Perm (Fin 4))) := rfl
  rw [h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

instance : kleinV.Normal where
  conj_mem n hn g := by
    rw [mem_kleinV_iff] at hn ⊢
    revert n g
    decide

set_option maxRecDepth 100000 in
theorem not_mem_kleinSet_card : ∀ g : Perm (Fin 4), g ∉ kleinSet →
    3 < (Finset.univ.image (fun k : Perm (Fin 4) => k⁻¹ * g * k)).card := by
  decide

theorem eq_kleinV_of_normal {F : Subgroup (Perm (Fin 4))} [F.Normal] (hF : Nat.card F = 4) :
    F = kleinV := by
  have hle : F ≤ kleinV := by
    intro g hg
    by_contra hgk
    have hgk' : g ∉ kleinSet := hgk
    have hcard := not_mem_kleinSet_card g hgk'
    have hg1 : g ≠ 1 := by
      rintro rfl
      exact hgk' (by decide)
    set C := Finset.univ.image (fun k : Perm (Fin 4) => k⁻¹ * g * k) with hC
    have h1C : (1 : Perm (Fin 4)) ∉ C := by
      intro h1
      rw [hC, Finset.mem_image] at h1
      obtain ⟨k, -, hk⟩ := h1
      apply hg1
      calc g = k * (k⁻¹ * g * k) * k⁻¹ := by group
        _ = 1 := by rw [hk]; group
    have hsub : ((insert 1 C : Finset (Perm (Fin 4))) : Set (Perm (Fin 4))) ⊆
        (F : Set (Perm (Fin 4))) := by
      intro x hx
      simp only [hC, Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_insert_iff, Set.mem_range] at hx
      rcases hx with rfl | ⟨k, rfl⟩
      · exact F.one_mem
      · simpa using Subgroup.Normal.conj_mem ‹F.Normal› g hg k⁻¹
    have hle' : Set.ncard ((insert 1 C : Finset (Perm (Fin 4))) : Set (Perm (Fin 4))) ≤
        Set.ncard (F : Set (Perm (Fin 4))) := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, Finset.card_insert_of_notMem h1C, ← Nat.card_coe_set_eq] at hle'
    have : Nat.card (F : Set (Perm (Fin 4))) = 4 := hF
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_kleinV, hF])

theorem mem_kleinSet_of_commute : ∀ g : Perm (Fin 4),
    (∀ v ∈ kleinSet, g * v = v * g) → g ∈ kleinSet := by decide

@[expose] def kleinA : Perm (Fin 4) := swap 0 1 * swap 2 3

@[expose] def kleinB : Perm (Fin 4) := swap 0 2 * swap 1 3

theorem kleinA_mem : kleinA ∈ kleinSet := by decide
theorem kleinB_mem : kleinB ∈ kleinSet := by decide

theorem kleinSet_eq : ∀ v ∈ kleinSet, v = 1 ∨ v = kleinA ∨ v = kleinB ∨ v = kleinA * kleinB := by
  decide

theorem exists_conj_pair : ∀ x ∈ kleinSet, ∀ y ∈ kleinSet, x ≠ 1 → y ≠ 1 → x ≠ y →
    ∃ g : Perm (Fin 4), g⁻¹ * kleinA * g = x ∧ g⁻¹ * kleinB * g = y := by
  decide

theorem kleinA_ne_one : kleinA ≠ 1 := by decide
theorem kleinB_ne_one : kleinB ≠ 1 := by decide
theorem kleinA_ne_kleinB : kleinA ≠ kleinB := by decide

@[expose] def kleinC : Perm (Fin 4) := swap 0 1 * swap 1 2

theorem kleinC_pow : kleinC ^ 3 = 1 := by decide

theorem kleinC_ne_one : kleinC ≠ 1 := by decide

theorem orderOf_kleinC : orderOf kleinC = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime kleinC_pow kleinC_ne_one

theorem kleinSet_sign : ∀ v ∈ kleinSet, Equiv.Perm.sign v = 1 := by decide

set_option maxRecDepth 100000 in
theorem mem_kleinSet_of_sign_of_pow : ∀ g : Perm (Fin 4), Equiv.Perm.sign g = 1 →
    g ^ 8 = 1 → g ∈ kleinSet := by decide

@[expose] def threeSet : Finset (Perm (Fin 4)) := Finset.univ.filter fun g => g ≠ 1 ∧ g ^ 3 = 1

theorem threeSet_conj : ∀ d ∈ threeSet, ∀ c ∈ threeSet,
    ∃ e ∈ kleinSet, c = e⁻¹ * d * e ∨ c = e⁻¹ * d⁻¹ * e := by decide

theorem natCard_perm_four : Nat.card (Perm (Fin 4)) = 24 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem pow_three_of_odd {g : Perm (Fin 4)} (h : Odd (orderOf g)) : g ^ 3 = 1 := by
  have hdvd : orderOf g ∣ 24 := by
    have := orderOf_dvd_natCard g
    rwa [natCard_perm_four] at this
  have hcop : Nat.Coprime (orderOf g) 8 :=
    Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr h)
  have : orderOf g ∣ 3 := by
    have : orderOf g ∣ 8 * 3 := by simpa using hdvd
    exact hcop.dvd_of_dvd_mul_left this
  exact orderOf_dvd_iff_pow_eq_one.mp this

theorem sign_eq_one_of_odd {g : Perm (Fin 4)} (h : Odd (orderOf g)) :
    Equiv.Perm.sign g = 1 := by
  have hg := pow_three_of_odd h
  have h1 : Equiv.Perm.sign g ^ 3 = 1 := by rw [← map_pow, hg, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h2 | h2
  · exact h2
  · rw [h2] at h1
    exact absurd h1 (by decide)

theorem pow_pow_two_of_mem_alt {g : Perm (Fin 4)} (hs : Equiv.Perm.sign g = 1) {k : ℕ}
    (hk : g ^ 2 ^ k = 1) : g ∈ kleinSet := by
  apply mem_kleinSet_of_sign_of_pow g hs
  have hdvd : orderOf g ∣ 24 := by
    have := orderOf_dvd_natCard g
    rwa [natCard_perm_four] at this
  have h2k : orderOf g ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2k
  rw [hj] at hdvd
  have hj3 : j ≤ 3 := by
    by_contra hcon
    have h4 : 2 ^ 4 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
    have := h4.trans hdvd
    norm_num at this
  have : orderOf g ∣ 8 := by
    rw [hj]
    exact (pow_dvd_pow 2 hj3 : 2 ^ j ∣ 2 ^ 3)
  exact orderOf_dvd_iff_pow_eq_one.mp this

section Abstract

variable {G : Type*} [Group G]

structure Data (P E : Subgroup G) where
  φ : ↥P ≃* Perm (Fin 4)
  le : E ≤ P
  normal : P ≤ Subgroup.normalizer (E : Set G)
  card : Nat.card E = 4

variable {P E : Subgroup G} (D : Data P E)

include D

theorem Data.mem_iff {x : G} (hx : x ∈ P) : x ∈ E ↔ D.φ ⟨x, hx⟩ ∈ kleinSet := by
  have hnorm : (E.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer D.le).mpr D.normal
  have hcard : Nat.card (E.subgroupOf P) = 4 := by
    rw [← D.card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.le).toEquiv
  have hmap : (E.subgroupOf P).map D.φ.toMonoidHom = kleinV := by
    have : ((E.subgroupOf P).map D.φ.toMonoidHom).Normal :=
      Subgroup.Normal.map hnorm D.φ.toMonoidHom D.φ.surjective
    apply eq_kleinV_of_normal
    rw [Subgroup.card_map_of_injective D.φ.injective]
    exact hcard
  have : (⟨x, hx⟩ : ↥P) ∈ E.subgroupOf P ↔
      D.φ ⟨x, hx⟩ ∈ (E.subgroupOf P).map D.φ.toMonoidHom := by
    constructor
    · intro h
      exact Subgroup.mem_map_of_mem _ h
    · rintro ⟨y, hy, hyx⟩
      have := D.φ.injective hyx
      rw [← this]
      exact hy
  rw [hmap, mem_kleinV_iff] at this
  exact this

theorem Data.centralizer {x : G} (hx : x ∈ P) (hc : ∀ e ∈ E, x * e = e * x) : x ∈ E := by
  rw [D.mem_iff hx]
  apply mem_kleinSet_of_commute
  intro v hv
  obtain ⟨y, rfl⟩ := D.φ.surjective v
  have hyE : (y : G) ∈ E := (D.mem_iff y.2).mpr (by simpa using hv)
  have h2 : (⟨x, hx⟩ : ↥P) * y = y * ⟨x, hx⟩ := Subtype.ext (hc y hyE)
  simpa using congrArg D.φ h2

theorem Data.exists_gens :
    ∃ a b : G, a ∈ E ∧ b ∈ E ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      (∀ f ∈ E, f = 1 ∨ f = a ∨ f = b ∨ f = a * b) ∧
      ∀ x ∈ E, ∀ y ∈ E, x ≠ 1 → y ≠ 1 → x ≠ y →
        ∃ n ∈ P, n⁻¹ * a * n = x ∧ n⁻¹ * b * n = y := by
  let a₀ : ↥P := D.φ.symm kleinA
  let b₀ : ↥P := D.φ.symm kleinB
  have ha : (a₀ : G) ∈ E := (D.mem_iff a₀.2).mpr (by simpa [a₀] using kleinA_mem)
  have hb : (b₀ : G) ∈ E := (D.mem_iff b₀.2).mpr (by simpa [b₀] using kleinB_mem)
  have hφE : ∀ f : ↥P, (f : G) ∈ E → D.φ f ∈ kleinSet := fun f hf => by
    simpa using (D.mem_iff f.2).mp hf
  refine ⟨a₀, b₀, ha, hb, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h' : a₀ = 1 := Subtype.ext h
    have : D.φ a₀ = D.φ 1 := by rw [h']
    simp only [a₀, MulEquiv.apply_symm_apply, map_one] at this
    exact kleinA_ne_one this
  · intro h
    have h' : b₀ = 1 := Subtype.ext h
    have : D.φ b₀ = D.φ 1 := by rw [h']
    simp only [b₀, MulEquiv.apply_symm_apply, map_one] at this
    exact kleinB_ne_one this
  · intro h
    have h' : a₀ = b₀ := Subtype.ext h
    have : D.φ a₀ = D.φ b₀ := by rw [h']
    simp only [a₀, b₀, MulEquiv.apply_symm_apply] at this
    exact kleinA_ne_kleinB this
  · intro f hf
    have hfP : f ∈ P := D.le hf
    have h1 := hφE ⟨f, hfP⟩ hf
    rcases kleinSet_eq _ h1 with h | h | h | h
    · left
      have := D.φ.injective (h.trans (map_one D.φ).symm)
      exact congrArg Subtype.val this
    · right; left
      have := D.φ.injective (h.trans (D.φ.apply_symm_apply kleinA).symm)
      exact congrArg Subtype.val this
    · right; right; left
      have := D.φ.injective (h.trans (D.φ.apply_symm_apply kleinB).symm)
      exact congrArg Subtype.val this
    · right; right; right
      have hab : D.φ (a₀ * b₀) = kleinA * kleinB := by
        rw [map_mul]
        simp only [a₀, b₀, MulEquiv.apply_symm_apply]
      have := D.φ.injective (h.trans hab.symm)
      exact congrArg Subtype.val this
  · intro x hx y hy hx1 hy1 hxy
    have hxP : x ∈ P := D.le hx
    have hyP : y ∈ P := D.le hy
    have h1 := hφE ⟨x, hxP⟩ hx
    have h2 := hφE ⟨y, hyP⟩ hy
    have hx1' : D.φ ⟨x, hxP⟩ ≠ 1 := fun h => hx1 (congrArg Subtype.val (D.φ.injective
      (h.trans (map_one D.φ).symm)))
    have hy1' : D.φ ⟨y, hyP⟩ ≠ 1 := fun h => hy1 (congrArg Subtype.val (D.φ.injective
      (h.trans (map_one D.φ).symm)))
    have hxy' : D.φ ⟨x, hxP⟩ ≠ D.φ ⟨y, hyP⟩ := fun h => hxy (congrArg Subtype.val
      (D.φ.injective h))
    obtain ⟨g, hg1, hg2⟩ := exists_conj_pair _ h1 _ h2 hx1' hy1' hxy'
    refine ⟨(D.φ.symm g : G), (D.φ.symm g).2, ?_, ?_⟩
    · have := congrArg (fun z => (D.φ.symm z : G)) hg1
      simpa [a₀, mul_assoc] using this
    · have := congrArg (fun z => (D.φ.symm z : G)) hg2
      simpa [b₀, mul_assoc] using this

theorem Data.exists_odd : ∃ d ∈ P, d ≠ 1 ∧ Odd (orderOf d) := by
  refine ⟨(D.φ.symm kleinC : G), (D.φ.symm kleinC).2, ?_, ?_⟩
  · intro h
    have h' : D.φ.symm kleinC = 1 := Subtype.ext h
    have := congrArg D.φ h'
    simp only [MulEquiv.apply_symm_apply, map_one] at this
    exact kleinC_ne_one this
  · have h3 : orderOf (D.φ.symm kleinC) = 3 := by rw [MulEquiv.orderOf_eq, orderOf_kleinC]
    rw [Subgroup.orderOf_coe, h3]
    decide

@[expose] def Data.A : Subgroup G :=
  ((alternatingGroup (Fin 4)).comap D.φ.toMonoidHom).map P.subtype

theorem Data.mem_A_iff {x : G} :
    x ∈ D.A ↔ ∃ hx : x ∈ P, Equiv.Perm.sign (D.φ ⟨x, hx⟩) = 1 := by
  unfold Data.A
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, ?_⟩
    have := Equiv.Perm.mem_alternatingGroup.mp (Subgroup.mem_comap.mp hy)
    simpa using this
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, Subgroup.mem_comap.mpr (Equiv.Perm.mem_alternatingGroup.mpr (by simpa using h)), rfl⟩

theorem Data.A_le : D.A ≤ P := by
  rintro x ⟨y, -, rfl⟩
  exact y.2

theorem Data.E_le_A : E ≤ D.A := by
  intro x hx
  have hxP := D.le hx
  rw [Data.mem_A_iff]
  exact ⟨hxP, kleinSet_sign _ ((D.mem_iff hxP).mp hx)⟩

theorem Data.nonempty_equiv_A : Nonempty (↥D.A ≃* alternatingGroup (Fin 4)) := by
  let C : Subgroup ↥P := (alternatingGroup (Fin 4)).comap D.φ.toMonoidHom
  have e1 : ↥D.A ≃* ↥C := (Subgroup.equivMapOfInjective C P.subtype P.subtype_injective).symm
  have hC : C = (alternatingGroup (Fin 4)).map D.φ.symm.toMonoidHom :=
    Subgroup.comap_equiv_eq_map_symm' D.φ _
  have e2 : ↥C ≃* ↥(alternatingGroup (Fin 4)) :=
    (MulEquiv.subgroupCongr hC).trans (D.φ.symm.subgroupMap (alternatingGroup (Fin 4))).symm
  exact ⟨e1.trans e2⟩

theorem Data.odd_mem_A {x : G} (hx : x ∈ P) (hodd : Odd (orderOf x)) : x ∈ D.A := by
  rw [Data.mem_A_iff]
  refine ⟨hx, sign_eq_one_of_odd ?_⟩
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact hodd

theorem Data.two_mem_E {x : G} (hx : x ∈ D.A) {k : ℕ} (hk : x ^ 2 ^ k = 1) : x ∈ E := by
  obtain ⟨hxP, hs⟩ := (Data.mem_A_iff D).mp hx
  rw [D.mem_iff hxP]
  apply pow_pow_two_of_mem_alt hs (k := k)
  rw [← map_pow]
  have : (⟨x, hxP⟩ : ↥P) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
  rw [this, map_one]

theorem Data.A_le_of_conj {d : G} (hd : d ∈ D.A) (hd3 : Odd (orderOf d)) (hd1 : d ≠ 1)
    {X : Subgroup G} (hconj : ∀ e ∈ E, e⁻¹ * d * e ∈ X) : D.A ≤ X := by
  obtain ⟨hdP, -⟩ := (Data.mem_A_iff D).mp hd
  let X' : Subgroup (Perm (Fin 4)) := (X.subgroupOf P).map D.φ.toMonoidHom
  have hmemX' : ∀ y : ↥P, (y : G) ∈ X → D.φ y ∈ X' := fun y hy =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
  have hdφ : D.φ ⟨d, hdP⟩ ∈ threeSet := by
    simp only [threeSet, Finset.mem_filter, Finset.mem_univ, true_and]
    have hodd : Odd (orderOf (D.φ ⟨d, hdP⟩)) := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hd3
    refine ⟨fun h => hd1 ?_, pow_three_of_odd hodd⟩
    have := D.φ.injective (h.trans (map_one D.φ).symm)
    exact congrArg Subtype.val this
  have hthree : ∀ c : Perm (Fin 4), c.IsThreeCycle → c ∈ X' := by
    intro c hc
    have hord := hc.orderOf
    have hc3 : c ^ 3 = 1 := by
      rw [← hord]
      exact pow_orderOf_eq_one c
    have hc1 : c ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      omega
    have hcset : c ∈ threeSet := by
      simp only [threeSet, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hc1, hc3⟩
    obtain ⟨e, he, hce⟩ := threeSet_conj _ hdφ c hcset
    obtain ⟨e₀, rfl⟩ := D.φ.surjective e
    have he₀E : (e₀ : G) ∈ E := (D.mem_iff e₀.2).mpr (by simpa using he)
    have hconj' : ((e₀⁻¹ * ⟨d, hdP⟩ * e₀ : ↥P) : G) ∈ X := by
      simpa [mul_assoc] using hconj _ he₀E
    rcases hce with h | h
    · rw [h]
      simpa using hmemX' _ hconj'
    · rw [h]
      have hinv : (((e₀⁻¹ * ⟨d, hdP⟩ * e₀)⁻¹ : ↥P) : G) ∈ X := X.inv_mem hconj'
      simpa [mul_assoc] using hmemX' _ hinv
  have hA : alternatingGroup (Fin 4) ≤ X' := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    exact (Subgroup.closure_le X').mpr fun c hc => hthree c hc
  intro x hx
  obtain ⟨hxP, hs⟩ := (Data.mem_A_iff D).mp hx
  have hxX' : D.φ ⟨x, hxP⟩ ∈ X' := hA (Equiv.Perm.mem_alternatingGroup.mpr hs)
  obtain ⟨y, hy, hyx⟩ := hxX'
  have hyx' : y = ⟨x, hxP⟩ := D.φ.injective hyx
  have h2 : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
  rw [congrArg Subtype.val hyx'] at h2
  exact h2

theorem Data.mul_inv_mem_A {x y : G} (hx : x ∈ P) (hy : y ∈ P) (hxA : x ∉ D.A) (hyA : y ∉ D.A) :
    x * y⁻¹ ∈ D.A := by
  rw [Data.mem_A_iff] at hxA hyA ⊢
  refine ⟨P.mul_mem hx (P.inv_mem hy), ?_⟩
  have hx' : Equiv.Perm.sign (D.φ ⟨x, hx⟩) ≠ 1 := fun h => hxA ⟨hx, h⟩
  have hy' : Equiv.Perm.sign (D.φ ⟨y, hy⟩) ≠ 1 := fun h => hyA ⟨hy, h⟩
  have hxm : Equiv.Perm.sign (D.φ ⟨x, hx⟩) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (D.φ ⟨x, hx⟩)) with h | h
    · exact absurd h hx'
    · exact h
  have hym : Equiv.Perm.sign (D.φ ⟨y, hy⟩) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (D.φ ⟨y, hy⟩)) with h | h
    · exact absurd h hy'
    · exact h
  have : (⟨x * y⁻¹, P.mul_mem hx (P.inv_mem hy)⟩ : ↥P) = ⟨x, hx⟩ * ⟨y, hy⟩⁻¹ := rfl
  rw [this, map_mul, map_inv, map_mul, map_inv, hxm, hym]
  decide

theorem Data.natCard_P : Nat.card P = 24 := by
  rw [Nat.card_congr D.φ.toEquiv, natCard_perm_four]

theorem Data.card_le_of_isPGroup {X : Subgroup G} (hXP : X ≤ P) (hX : IsPGroup 2 X) :
    Nat.card X ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPfin : Finite ↥P := Finite.of_equiv (Perm (Fin 4)) D.φ.symm.toEquiv
  have hXfin : Finite ↥X :=
    Finite.of_injective (Subgroup.inclusion hXP) (Subgroup.inclusion_injective hXP)
  obtain ⟨n, hn⟩ := hX.exists_card_eq
  have hdvd : Nat.card X ∣ Nat.card P := Subgroup.card_dvd_of_le hXP
  rw [hn, D.natCard_P] at hdvd
  have hn3 : n ≤ 3 := by
    by_contra hcon
    have h4 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 (by omega)
    have := h4.trans hdvd
    norm_num at this
  rw [hn]
  calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    _ = 8 := by norm_num

end Abstract

end CFSG.QuasithinUnique.Klein
