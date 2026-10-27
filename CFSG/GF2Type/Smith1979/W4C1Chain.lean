module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PGroup.NormalSubgroups
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
public import Mathlib.GroupTheory.Nilpotent
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

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979.W4C1

open Subgroup

structure Chain {S : Type*} [Group S] (z x y : S) : Prop where
  z_ne : z ≠ 1
  z_sq : z * z = 1
  z_cent : ∀ s : S, s * z = z * s
  x_ne : x ≠ 1
  x_ne_z : x ≠ z
  x_sq : x * x = 1
  x_comm : x * z = z * x
  x_conj : ∀ s : S, s * x = x * s ∨ s * x = (x * z) * s
  y_ne : y ≠ 1
  y_ne_z : y ≠ z
  y_ne_x : y ≠ x
  y_ne_xz : y ≠ x * z
  y_sq : y * y = 1
  y_comm_z : y * z = z * y
  y_comm_x : y * x = x * y
  y_conj : ∀ s : S, s * y = y * s ∨ s * y = (y * z) * s ∨ s * y = (y * x) * s ∨
    s * y = (y * (x * z)) * s

@[expose] def T8 {S : Type*} [Group S] (z x y : S) : Set S :=
  {1, z, x, x * z, y, y * z, y * x, y * (x * z)}

theorem Chain.map {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') {z x y : S}
    (h : Chain z x y) : Chain (e z) (e x) (e y) where
  z_ne := fun h1 => h.z_ne (e.injective (by rw [h1, map_one]))
  z_sq := by rw [← map_mul, h.z_sq, map_one]
  z_cent := fun s' => by
    obtain ⟨s, rfl⟩ := e.surjective s'
    rw [← map_mul, ← map_mul, h.z_cent]
  x_ne := fun h1 => h.x_ne (e.injective (by rw [h1, map_one]))
  x_ne_z := fun h1 => h.x_ne_z (e.injective h1)
  x_sq := by rw [← map_mul, h.x_sq, map_one]
  x_comm := by rw [← map_mul, ← map_mul, h.x_comm]
  x_conj := fun s' => by
    obtain ⟨s, rfl⟩ := e.surjective s'
    rcases h.x_conj s with h1 | h1
    · left
      rw [← map_mul, ← map_mul, h1]
    · right
      rw [← map_mul, ← map_mul, ← map_mul, h1]
  y_ne := fun h1 => h.y_ne (e.injective (by rw [h1, map_one]))
  y_ne_z := fun h1 => h.y_ne_z (e.injective h1)
  y_ne_x := fun h1 => h.y_ne_x (e.injective h1)
  y_ne_xz := fun h1 => h.y_ne_xz (e.injective (by rw [map_mul]; exact h1))
  y_sq := by rw [← map_mul, h.y_sq, map_one]
  y_comm_z := by rw [← map_mul, ← map_mul, h.y_comm_z]
  y_comm_x := by rw [← map_mul, ← map_mul, h.y_comm_x]
  y_conj := fun s' => by
    obtain ⟨s, rfl⟩ := e.surjective s'
    rcases h.y_conj s with h1 | h1 | h1 | h1
    · left
      rw [← map_mul, ← map_mul, h1]
    · right; left
      rw [← map_mul, ← map_mul, ← map_mul, h1]
    · right; right; left
      rw [← map_mul, ← map_mul, ← map_mul, h1]
    · right; right; right
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, h1]

theorem mem_T8_map {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') {z x y : S} {w : S'}
    (h : w ∈ T8 (e z) (e x) (e y)) : e.symm w ∈ T8 z x y := by
  simp only [T8, Set.mem_insert_iff, Set.mem_singleton_iff] at h ⊢
  simp only [MulEquiv.symm_apply_eq, map_mul, map_one]
  exact h

theorem inv_mul_mem_of_card_eq_two_mul {S : Type*} [Group S] [Finite S] {H N : Subgroup S}
    (hHN : H ≤ N) (hcard : Nat.card N = 2 * Nat.card H) {a b : S} (ha : a ∈ N) (hb : b ∈ N)
    (ha' : a ∉ H) (hb' : b ∉ H) : a⁻¹ * b ∈ H := by
  set H' : Subgroup N := H.subgroupOf N with hH'
  have hcardH' : Nat.card H' = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv
  have hidx : H'.index = 2 := by
    have h1 := Subgroup.card_mul_index H'
    rw [hcardH', hcard] at h1
    have hpos : 0 < Nat.card H := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, mul_comm])
  haveI : H'.Normal := Subgroup.normal_of_index_eq_two hidx
  obtain ⟨c, hc⟩ := Subgroup.index_eq_two_iff.mp hidx
  have hu : (⟨a, ha⟩ : N) * c ∈ H' := by
    have := hc ⟨a, ha⟩
    rcases this with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact h1
    · exact absurd (by simpa [hH', Subgroup.mem_subgroupOf] using h2) ha'
  have hv : (⟨b, hb⟩ : N) * c ∈ H' := by
    have := hc ⟨b, hb⟩
    rcases this with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact h1
    · exact absurd (by simpa [hH', Subgroup.mem_subgroupOf] using h2) hb'
  have h3 : ((⟨a, ha⟩ : N) * c)⁻¹ * ((⟨b, hb⟩ : N) * c) ∈ H' := mul_mem (inv_mem hu) hv
  have h4 : (⟨a, ha⟩ : N)⁻¹ * ⟨b, hb⟩ =
      c * (((⟨a, ha⟩ : N) * c)⁻¹ * ((⟨b, hb⟩ : N) * c)) * c⁻¹ := by
    group
  have h5 : (⟨a, ha⟩ : N)⁻¹ * ⟨b, hb⟩ ∈ H' := by
    rw [h4]
    exact (Subgroup.Normal.conj_mem inferInstance _ h3 c)
  simpa [hH', Subgroup.mem_subgroupOf] using h5

theorem exists_eq_one_or_eq_of_card_eq_two {S : Type*} [Group S] {H : Subgroup S}
    (h : Nat.card H = 2) : ∃ z ∈ H, z ≠ 1 ∧ ∀ f ∈ H, f = 1 ∨ f = z := by
  obtain ⟨z, hz1, hzu⟩ := (Nat.card_eq_two_iff' (1 : H)).mp h
  refine ⟨z, z.2, fun h1 => hz1 (Subtype.ext h1), fun f hf => ?_⟩
  by_cases h1 : f = 1
  · exact Or.inl h1
  · exact Or.inr (congrArg Subtype.val (hzu ⟨f, hf⟩ fun h2 => h1 (congrArg Subtype.val h2)))

theorem exists_chain {S : Type*} [Group S] [Finite S] (hS : IsPGroup 2 S) (F : Subgroup S)
    (hF : F.Normal) (hcomm : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a) (hsq : ∀ a ∈ F, a * a = 1)
    (h8 : 8 ≤ Nat.card F) : ∃ z x y : S, Chain z x y ∧ z ∈ F ∧ x ∈ F ∧ y ∈ F := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 S) := ⟨hS⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hS.to_subgroup F)
  have hk3 : 3 ≤ k := by
    by_contra hlt
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨F8, hF8n, hF8le, hF8c⟩ := CFSG.exists_normal_subgroup_card_pow_of_normal F hF hk 3 hk3
  obtain ⟨F4, hF4n, hF4le, hF4c⟩ :=
    CFSG.exists_normal_subgroup_card_pow_of_normal F8 hF8n hF8c 2 (by norm_num)
  obtain ⟨F2, hF2n, hF2le, hF2c⟩ :=
    CFSG.exists_normal_subgroup_card_pow_of_normal F4 hF4n hF4c 1 (by norm_num)
  have hF2c' : Nat.card F2 = 2 := by simpa using hF2c
  have hF4c' : Nat.card F4 = 4 := by simpa using hF4c
  have hF8c' : Nat.card F8 = 8 := by simpa using hF8c
  obtain ⟨z, hzF2, hz1, hz⟩ := exists_eq_one_or_eq_of_card_eq_two hF2c'
  have hlt24 : F2 < F4 := lt_of_le_of_ne hF2le fun h => by
    rw [h, hF4c'] at hF2c'
    omega
  have hlt48 : F4 < F8 := lt_of_le_of_ne hF4le fun h => by
    rw [h, hF8c'] at hF4c'
    omega
  obtain ⟨x, hxF4, hxF2⟩ := SetLike.exists_of_lt hlt24
  obtain ⟨y, hyF8, hyF4⟩ := SetLike.exists_of_lt hlt48
  have hc24 : Nat.card F4 = 2 * Nat.card F2 := by rw [hF4c', hF2c']
  have hc48 : Nat.card F8 = 2 * Nat.card F4 := by rw [hF8c', hF4c']
  have hF2F : F2 ≤ F := hF2le.trans (hF4le.trans hF8le)
  have hF4F : F4 ≤ F := hF4le.trans hF8le
  have hzF : z ∈ F := hF2F hzF2
  have hxF : x ∈ F := hF4F hxF4
  have hyF : y ∈ F := hF8le hyF8
  have hF4el : ∀ f ∈ F4, f = 1 ∨ f = z ∨ f = x ∨ f = x * z := by
    intro f hf
    by_cases hfF2 : f ∈ F2
    · rcases hz f hfF2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · have h1 := inv_mul_mem_of_card_eq_two_mul hF2le hc24 hxF4 hf hxF2 hfF2
      rcases hz _ h1 with h | h
      · right; right; left
        rw [inv_mul_eq_one] at h
        exact h.symm
      · right; right; right
        rw [inv_mul_eq_iff_eq_mul] at h
        exact h
  have hz1' : z ≠ 1 := hz1
  have hx1 : x ≠ 1 := fun h => hxF2 (h ▸ F2.one_mem)
  have hxz : x ≠ z := fun h => hxF2 (h ▸ hzF2)
  have hxcz : x * z = z * x := hcomm x hxF z hzF
  have hyc4 : ∀ c ∈ F4, y ≠ c := fun c hc h => hyF4 (h ▸ hc)
  refine ⟨z, x, y, ?_, hzF, hxF, hyF⟩
  refine
    { z_ne := hz1'
      z_sq := hsq z hzF
      z_cent := ?_
      x_ne := hx1
      x_ne_z := hxz
      x_sq := hsq x hxF
      x_comm := hxcz
      x_conj := ?_
      y_ne := hyc4 1 F4.one_mem
      y_ne_z := hyc4 z (hF2le hzF2)
      y_ne_x := hyc4 x hxF4
      y_ne_xz := hyc4 (x * z) (F4.mul_mem hxF4 (hF2le hzF2))
      y_sq := hsq y hyF
      y_comm_z := hcomm y hyF z hzF
      y_comm_x := hcomm y hyF x hxF
      y_conj := ?_ }
  · intro s
    have h1 : s * z * s⁻¹ ∈ F2 := hF2n.conj_mem z hzF2 s
    rcases hz _ h1 with h | h
    · exact absurd (by simpa using h) hz1'
    · calc s * z = (s * z * s⁻¹) * s := by group
        _ = z * s := by rw [h]
  · intro s
    have h1 : s * x * s⁻¹ ∈ F4 := hF4n.conj_mem x hxF4 s
    have h2 : s * x * s⁻¹ ∉ F2 := by
      intro h
      apply hxF2
      have := hF2n.conj_mem _ h s⁻¹
      simpa [mul_assoc] using this
    have h3 := inv_mul_mem_of_card_eq_two_mul hF2le hc24 hxF4 h1 hxF2 h2
    have hux : s * x = (s * x * s⁻¹) * s := by group
    rcases hz _ h3 with h | h
    · left
      rw [inv_mul_eq_one] at h
      rw [hux, ← h]
    · right
      rw [inv_mul_eq_iff_eq_mul] at h
      rw [hux, h]
  · intro s
    have h1 : s * y * s⁻¹ ∈ F8 := hF8n.conj_mem y hyF8 s
    have h2 : s * y * s⁻¹ ∉ F4 := by
      intro h
      apply hyF4
      have := hF4n.conj_mem _ h s⁻¹
      simpa [mul_assoc] using this
    have h3 := inv_mul_mem_of_card_eq_two_mul hF4le hc48 hyF8 h1 hyF4 h2
    have huy : s * y = (s * y * s⁻¹) * s := by group
    rcases hF4el _ h3 with h | h | h | h
    · left
      rw [inv_mul_eq_one] at h
      rw [huy, ← h]
    · right; left
      rw [inv_mul_eq_iff_eq_mul] at h
      rw [huy, h]
    · right; right; left
      rw [inv_mul_eq_iff_eq_mul] at h
      rw [huy, h]
    · right; right; right
      rw [inv_mul_eq_iff_eq_mul] at h
      rw [huy, h]

end CFSG.GF2Type.Smith1979.W4C1
