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

namespace CFSG.CGT.PushingUpLit.A78

open scoped commutatorElement

structure JStructure (G : Type) [Group G] (J V V₂ : Subgroup G) (e : ℕ) : Prop where
  two_le : 2 ≤ e
  sup_eq : V ⊔ V₂ = J
  conj_V : ∀ j ∈ J, ∀ x ∈ V, j * x * j⁻¹ ∈ V
  conj_V₂ : ∀ j ∈ J, ∀ x ∈ V₂, j * x * j⁻¹ ∈ V₂
  abelian_V : ∀ x ∈ V, ∀ y ∈ V, Commute x y
  sq_V : ∀ x ∈ V, x * x = 1
  abelian_V₂ : ∀ x ∈ V₂, ∀ y ∈ V₂, Commute x y
  sq_V₂ : ∀ x ∈ V₂, x * x = 1
  index_V : (V ⊓ V₂).relIndex V = 2 ^ e
  index_V₂ : (V ⊓ V₂).relIndex V₂ = 2 ^ e
  comm_ge : ∀ v₂ ∈ V₂, v₂ ∉ V → 2 ^ e ≤ Nat.card ↥⁅V, Subgroup.zpowers v₂⁆

theorem mem_sup_iff_of_normalizes {G : Type} [Group G] {K H : Subgroup G}
    (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) {x : G} :
    x ∈ K ⊔ H ↔ ∃ k ∈ K, ∃ h ∈ H, x = k * h := by
  constructor
  · intro hx
    let P : Subgroup G :=
      { carrier := {x | ∃ k ∈ K, ∃ h ∈ H, x = k * h}
        one_mem' := ⟨1, K.one_mem, 1, H.one_mem, (mul_one 1).symm⟩
        mul_mem' := by
          rintro _ _ ⟨k, hk, h, hh, rfl⟩ ⟨k', hk', h', hh', rfl⟩
          refine ⟨k * (h * k' * h⁻¹), K.mul_mem hk (hHK h hh k' hk'), h * h', H.mul_mem hh hh',
            by group⟩
        inv_mem' := by
          rintro _ ⟨k, hk, h, hh, rfl⟩
          refine ⟨h⁻¹ * k⁻¹ * h, ?_, h⁻¹, H.inv_mem hh, by group⟩
          have := hHK h⁻¹ (H.inv_mem hh) k⁻¹ (K.inv_mem hk)
          simpa [mul_assoc] using this }
    have hle : K ⊔ H ≤ P := sup_le (fun k hk => ⟨k, hk, 1, H.one_mem, (mul_one k).symm⟩)
      (fun h hh => ⟨1, K.one_mem, h, hh, (one_mul h).symm⟩)
    exact hle hx
  · rintro ⟨k, hk, h, hh, rfl⟩
    exact Subgroup.mul_mem_sup hk hh

variable {G : Type} [Group G] {J V V₂ : Subgroup G} {e : ℕ}

namespace JStructure

variable (h : JStructure G J V V₂ e)

include h

theorem V_le : V ≤ J := h.sup_eq ▸ le_sup_left

theorem V₂_le : V₂ ≤ J := h.sup_eq ▸ le_sup_right

theorem inv_eq_of_V {x : G} (hx : x ∈ V) : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h.sq_V x hx)

theorem inv_eq_of_V₂ {x : G} (hx : x ∈ V₂) : x⁻¹ = x := inv_eq_of_mul_eq_one_right (h.sq_V₂ x hx)

theorem commutator_mem {v w : G} (hv : v ∈ V) (hw : w ∈ V₂) : ⁅v, w⁆ ∈ V ⊓ V₂ := by
  refine ⟨?_, ?_⟩
  · have : w * v⁻¹ * w⁻¹ ∈ V := h.conj_V w (h.V₂_le hw) _ (V.inv_mem hv)
    have := V.mul_mem hv this
    simpa [commutatorElement_def, mul_assoc] using this
  · have : v * w * v⁻¹ ∈ V₂ := h.conj_V₂ v (h.V_le hv) _ hw
    have := V₂.mul_mem this (V₂.inv_mem hw)
    simpa [commutatorElement_def, mul_assoc] using this

theorem sq_mul {v w : G} (hv : v ∈ V) (hw : w ∈ V₂) : v * w * (v * w) = ⁅v, w⁆ := by
  rw [commutatorElement_def, h.inv_eq_of_V hv, h.inv_eq_of_V₂ hw]
  group

theorem mem_sup_iff {x : G} : x ∈ J ↔ ∃ v ∈ V, ∃ w ∈ V₂, x = v * w := by
  rw [← h.sup_eq]
  exact mem_sup_iff_of_normalizes (fun w hw v hv => h.conj_V w (h.V₂_le hw) v hv)

omit h in
theorem eq_one_or_eq_of_mem_zpowers {w y : G} (hw : w * w = 1) (hy : y ∈ Subgroup.zpowers w) :
    y = 1 ∨ y = w := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hw, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hw, one_zpow, one_mul]

theorem card_V_eq : Nat.card V = 2 ^ e * Nat.card ↥(V ⊓ V₂) := by
  have := Subgroup.relIndex_mul_card (V ⊓ V₂) V
  rw [inf_eq_left.2 (inf_le_left : V ⊓ V₂ ≤ V), h.index_V] at this
  exact this.symm

theorem card_V₂_eq' : Nat.card V₂ = 2 ^ e * Nat.card ↥(V ⊓ V₂) := by
  have := Subgroup.relIndex_mul_card (V ⊓ V₂) V₂
  rw [inf_eq_left.2 (inf_le_right : V ⊓ V₂ ≤ V₂), h.index_V₂] at this
  exact this.symm

theorem card_V₂_eq : Nat.card V₂ = Nat.card V := h.card_V₂_eq'.trans h.card_V_eq.symm

section Centralizer

variable [Finite G]

noncomputable def commHom {w : G} (hw : w ∈ V₂) : ↥V →* ↥(V ⊓ V₂) :=
  MonoidHom.mk' (fun v => ⟨⁅(v : G), w⁆, h.commutator_mem v.2 hw⟩) (by
    intro v v'
    apply Subtype.ext
    show ⁅((v : G) * (v' : G)), w⁆ = ⁅(v : G), w⁆ * ⁅(v' : G), w⁆
    have h1 : ⁅((v : G) * (v' : G)), w⁆ = (v : G) * ⁅(v' : G), w⁆ * (v : G)⁻¹ * ⁅(v : G), w⁆ := by
      simp only [commutatorElement_def]
      group
    have hc : Commute (v : G) ⁅(v' : G), w⁆ :=
      h.abelian_V _ v.2 _ (h.commutator_mem v'.2 hw).1
    rw [h1, hc.mul_inv_cancel]
    exact (h.abelian_V _ (h.commutator_mem v'.2 hw).1 _ (h.commutator_mem v.2 hw).1).eq)

theorem inf_centralizer_eq {w : G} (hw : w ∈ V₂) (hwV : w ∉ V) :
    V ⊓ Subgroup.centralizer ({w} : Set G) = V ⊓ V₂ := by
  set N := V ⊓ V₂ with hN
  set φ := h.commHom hw with hφ
  have hker := Subgroup.card_ker_mul_card_range φ
  have hrange : 2 ^ e ≤ Nat.card φ.range := by
    refine (h.comm_ge w hw hwV).trans ?_
    have hle : ⁅V, Subgroup.zpowers w⁆ ≤ φ.range.map N.subtype := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      rcases eq_one_or_eq_of_mem_zpowers (h.sq_V₂ w hw) hy with rfl | rfl
      · rw [commutatorElement_one_right]
        exact Subgroup.one_mem _
      · exact ⟨φ ⟨v, hv⟩, ⟨⟨v, hv⟩, rfl⟩, rfl⟩
    calc Nat.card ↥⁅V, Subgroup.zpowers w⁆ ≤ Nat.card ↥(φ.range.map N.subtype) :=
          Subgroup.card_le_of_le hle
      _ = Nat.card φ.range := Subgroup.card_map_of_injective N.subtype_injective
  have hV : Nat.card V = 2 ^ e * Nat.card N := h.card_V_eq
  have hkN : Nat.card φ.ker ≤ Nat.card N := by
    have hpos : 0 < 2 ^ e := by positivity
    have : 2 ^ e * Nat.card φ.ker ≤ 2 ^ e * Nat.card N := by
      calc 2 ^ e * Nat.card φ.ker = Nat.card φ.ker * 2 ^ e := mul_comm _ _
        _ ≤ Nat.card φ.ker * Nat.card φ.range := Nat.mul_le_mul_left _ hrange
        _ = 2 ^ e * Nat.card N := by rw [hker, hV]
    exact Nat.le_of_mul_le_mul_left this hpos
  have hmap : φ.ker.map V.subtype = V ⊓ Subgroup.centralizer ({w} : Set G) := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨v.2, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : φ v = 1 := hv
      have h2 : ⁅(v : G), y⁆ = 1 := congrArg Subtype.val h1
      exact (commutatorElement_eq_one_iff_mul_comm.1 h2).symm
    · rintro ⟨hxV, hxc⟩
      refine ⟨⟨x, hxV⟩, ?_, rfl⟩
      have h1 := Subgroup.mem_centralizer_iff.1 hxc w (Set.mem_singleton w)
      show φ ⟨x, hxV⟩ = 1
      apply Subtype.ext
      exact commutatorElement_eq_one_iff_mul_comm.2 h1.symm
  have hCcard : Nat.card ↥(V ⊓ Subgroup.centralizer ({w} : Set G)) = Nat.card φ.ker := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective V.subtype_injective
  have hNC : N ≤ V ⊓ Subgroup.centralizer ({w} : Set G) := by
    intro n hn
    refine ⟨hn.1, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (h.abelian_V₂ _ hw n hn.2).eq
  exact (Subgroup.eq_of_le_of_card_ge hNC (hCcard ▸ hkN)).symm

theorem inf_centralizer_eq' {v : G} (hv : v ∈ V) (hvV₂ : v ∉ V₂) :
    V₂ ⊓ Subgroup.centralizer ({v} : Set G) = V ⊓ V₂ := by
  apply le_antisymm
  · rintro x ⟨hx₂, hxc⟩
    by_contra hxN
    have hxV : x ∉ V := fun hxV => hxN ⟨hxV, hx₂⟩
    have hvmem : v ∈ V ⊓ Subgroup.centralizer ({x} : Set G) := by
      refine ⟨hv, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_iff.1 hxc v (Set.mem_singleton v)).symm
    rw [h.inf_centralizer_eq hx₂ hxV] at hvmem
    exact hvV₂ hvmem.2
  · rintro n ⟨hnV, hnV₂⟩
    refine ⟨hnV₂, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact (h.abelian_V _ hv n hnV).eq

end Centralizer

section Involutions

theorem involution_mem [Finite G] {x : G} (hx : x ∈ J) (hx2 : x * x = 1) : x ∈ V ∨ x ∈ V₂ := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.mem_sup_iff).1 hx
  have hc : ⁅v, w⁆ = 1 := by rw [← h.sq_mul hv hw]; exact hx2
  by_cases hwV : w ∈ V
  · exact Or.inl (V.mul_mem hv hwV)
  · right
    have hvC : v ∈ V ⊓ Subgroup.centralizer ({w} : Set G) := by
      refine ⟨hv, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (commutatorElement_eq_one_iff_mul_comm.1 hc).symm
    rw [h.inf_centralizer_eq hw hwV] at hvC
    exact V₂.mul_mem hvC.2 hw

theorem elemAbelian_le [Finite G] {E : Subgroup G} (hE : E ≤ J) (hsq : ∀ x ∈ E, x * x = 1) :
    E ≤ V ∨ E ≤ V₂ := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨x, hxE, hxV⟩, ⟨y, hyE, hyV₂⟩⟩ : (∃ x ∈ E, x ∉ V) ∧ ∃ y ∈ E, y ∉ V₂ := by
    refine ⟨?_, ?_⟩
    · by_contra hh
      push Not at hh
      exact hcon.1 hh
    · by_contra hh
      push Not at hh
      exact hcon.2 hh
  have hx₂ : x ∈ V₂ := (h.involution_mem (hE hxE) (hsq x hxE)).resolve_left hxV
  have hyV : y ∈ V := (h.involution_mem (hE hyE) (hsq y hyE)).resolve_right hyV₂
  have hxy : x * y ∈ E := E.mul_mem hxE hyE
  rcases h.involution_mem (hE hxy) (hsq _ hxy) with h1 | h1
  · exact hxV (by simpa using V.mul_mem h1 (V.inv_mem hyV))
  · exact hyV₂ (by simpa using V₂.mul_mem (V₂.inv_mem hx₂) h1)

theorem card_le_of_elemAbelian [Finite G] {E : Subgroup G} (hE : E ≤ J)
    (hsq : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ Nat.card V := by
  rcases h.elemAbelian_le hE hsq with hV | hV₂
  · exact Subgroup.card_le_of_le hV
  · exact (Subgroup.card_le_of_le hV₂).trans h.card_V₂_eq.le

theorem mem_of_card [Finite G] {E : Subgroup G} (hE : E ≤ J) (hsq : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card E = Nat.card V) : E = V ∨ E = V₂ := by
  rcases h.elemAbelian_le hE hsq with hV | hV₂
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hV hcard.ge)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hV₂ (h.card_V₂_eq.le.trans hcard.ge))

end Involutions

section Center

theorem commute_of_mem_inf {n : G} (hn : n ∈ V ⊓ V₂) {j : G} (hj : j ∈ J) : Commute n j := by
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.mem_sup_iff).1 hj
  exact (h.abelian_V _ hn.1 _ hv).mul_right (h.abelian_V₂ _ hn.2 _ hw)

theorem not_le_V₂ : ¬ V ≤ V₂ := by
  intro hle
  have h1 := h.index_V
  rw [inf_eq_left.2 hle, Subgroup.relIndex_self] at h1
  have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.two_le
  omega

theorem not_le_V : ¬ V₂ ≤ V := by
  intro hle
  have h1 := h.index_V₂
  rw [inf_eq_right.2 hle, Subgroup.relIndex_self] at h1
  have : 2 ^ 2 ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) h.two_le
  omega

theorem center_eq [Finite G] : J ⊓ Subgroup.centralizer (J : Set G) = V ⊓ V₂ := by
  apply le_antisymm
  · rintro z ⟨hzJ, hzc⟩
    obtain ⟨v, hv, w, hw, rfl⟩ := (h.mem_sup_iff).1 hzJ
    have hcomm : ∀ j ∈ J, v * w * j = j * (v * w) := fun j hj =>
      (Subgroup.mem_centralizer_iff.1 hzc j hj).symm
    have hwV : w ∈ V := by
      by_contra hwV
      apply h.not_le_V₂
      intro u hu
      have hu' : u ∈ V ⊓ Subgroup.centralizer ({w} : Set G) := by
        refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have e : v * (y * u) = v * (u * y) := by
          calc v * (y * u) = v * y * u := by group
            _ = u * (v * y) := hcomm u (h.V_le hu)
            _ = (u * v) * y := by group
            _ = (v * u) * y := by rw [(h.abelian_V _ hu _ hv).eq]
            _ = v * (u * y) := by group
        exact mul_left_cancel e
      rw [h.inf_centralizer_eq hw hwV] at hu'
      exact hu'.2
    have hvV₂ : v ∈ V₂ := by
      by_contra hvV₂
      apply h.not_le_V
      intro u hu
      have hu' : u ∈ V₂ ⊓ Subgroup.centralizer ({v} : Set G) := by
        refine ⟨hu, Subgroup.mem_centralizer_iff.2 fun y hy => ?_⟩
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have e : (y * u) * w = (u * y) * w := by
          calc (y * u) * w = y * (u * w) := by group
            _ = y * (w * u) := by rw [(h.abelian_V₂ _ hu _ hw).eq]
            _ = (y * w) * u := by group
            _ = u * (y * w) := hcomm u (h.V₂_le hu)
            _ = (u * y) * w := by group
        exact mul_right_cancel e
      rw [h.inf_centralizer_eq' hv hvV₂] at hu'
      exact hu'.1
    exact (V ⊓ V₂).mul_mem ⟨hv, hvV₂⟩ ⟨hwV, hw⟩
  · intro n hn
    exact ⟨h.V_le hn.1, Subgroup.mem_centralizer_iff.2 fun j hj =>
      (h.commute_of_mem_inf hn hj).eq.symm⟩

theorem commutator_le : ⁅J, J⁆ ≤ V ⊓ V₂ := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨v, hv, w, hw, rfl⟩ := (h.mem_sup_iff).1 hx
  obtain ⟨v', hv', w', hw', rfl⟩ := (h.mem_sup_iff).1 hy
  set N := V ⊓ V₂ with hN
  have ha : ⁅v', w⁆ ∈ N := h.commutator_mem hv' hw
  have hb : ⁅v, w'⁆ ∈ N := h.commutator_mem hv hw'
  have hcen : ∀ n ∈ N, ∀ g ∈ V, n * g = g * n := fun n hn g hg =>
    (h.abelian_V _ hn.1 _ hg).eq
  set a := ⁅v', w⁆ with hadef
  set b := ⁅v, w'⁆ with hbdef
  have key1 : w * v' = a⁻¹ * (v' * w) := by
    rw [eq_inv_mul_iff_mul_eq, hadef, commutatorElement_def]
    group
  have key2 : w' * v = b⁻¹ * (v * w') := by
    rw [eq_inv_mul_iff_mul_eq, hbdef, commutatorElement_def]
    group
  have hxy : v * w * (v' * w') = a⁻¹ * (v * v' * (w * w')) := by
    calc v * w * (v' * w') = v * (w * v') * w' := by group
      _ = v * (a⁻¹ * (v' * w)) * w' := by rw [key1]
      _ = (v * a⁻¹) * (v' * w) * w' := by group
      _ = (a⁻¹ * v) * (v' * w) * w' := by rw [← hcen a⁻¹ (N.inv_mem ha) v hv]
      _ = a⁻¹ * (v * v' * (w * w')) := by group
  have hyx : v' * w' * (v * w) = b⁻¹ * (v * v' * (w * w')) := by
    calc v' * w' * (v * w) = v' * (w' * v) * w := by group
      _ = v' * (b⁻¹ * (v * w')) * w := by rw [key2]
      _ = (v' * b⁻¹) * (v * w') * w := by group
      _ = (b⁻¹ * v') * (v * w') * w := by rw [← hcen b⁻¹ (N.inv_mem hb) v' hv']
      _ = b⁻¹ * (v' * v * (w' * w)) := by group
      _ = b⁻¹ * (v * v' * (w * w')) := by
        rw [(h.abelian_V _ hv' _ hv).eq, (h.abelian_V₂ _ hw' _ hw).eq]
  have hc : ⁅v * w, v' * w'⁆ = a⁻¹ * b := by
    calc ⁅v * w, v' * w'⁆ = (v * w * (v' * w')) * (v' * w' * (v * w))⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = (a⁻¹ * (v * v' * (w * w'))) * (b⁻¹ * (v * v' * (w * w')))⁻¹ := by rw [hxy, hyx]
      _ = a⁻¹ * b := by group
  rw [hc]
  exact N.mul_mem (N.inv_mem ha) hb

end Center

section Complement

variable [Finite G]

theorem exists_complement : ∃ C : Subgroup G, C ≤ V₂ ∧ C ⊓ V = ⊥ ∧ V ⊔ C = J := by
  let S := {C : Subgroup G // C ≤ V₂ ∧ C ⊓ V = ⊥}
  have : Nonempty S := ⟨⟨⊥, bot_le, bot_inf_eq _⟩⟩
  obtain ⟨⟨C, hCV₂, hCV⟩, hmax⟩ := Finite.exists_max (fun C : S => Nat.card (C : Subgroup G))
  refine ⟨C, hCV₂, hCV, ?_⟩
  have hV₂le : V₂ ≤ V ⊔ C := by
    by_contra hnle
    obtain ⟨x, hx₂, hxVC⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    set C' : Subgroup G := C ⊔ Subgroup.zpowers x with hC'
    have hC'V₂ : C' ≤ V₂ := sup_le hCV₂ ((Subgroup.zpowers_le).2 hx₂)
    have hnorm : ∀ z ∈ Subgroup.zpowers x, ∀ c ∈ C, z * c * z⁻¹ ∈ C := by
      intro z hz c hc
      rcases eq_one_or_eq_of_mem_zpowers (h.sq_V₂ x hx₂) hz with hz1 | hzx
      · simpa [hz1] using hc
      · rw [hzx, (h.abelian_V₂ _ hx₂ _ (hCV₂ hc)).mul_inv_cancel]
        exact hc
    have hC'V : C' ⊓ V = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyC', hyV⟩
      obtain ⟨c, hc, z, hz, rfl⟩ := (mem_sup_iff_of_normalizes hnorm).1 hyC'
      rcases eq_one_or_eq_of_mem_zpowers (h.sq_V₂ x hx₂) hz with hz1 | hzx
      · rw [hz1, mul_one] at hyV ⊢
        have : c ∈ C ⊓ V := ⟨hc, hyV⟩
        rw [hCV] at this
        exact this
      · exfalso
        apply hxVC
        rw [hzx] at hyV
        have hx : x = c⁻¹ * (c * x) := by group
        rw [hx, sup_comm]
        exact Subgroup.mul_mem_sup (C.inv_mem hc) hyV
    have hle := hmax ⟨C', hC'V₂, hC'V⟩
    have heq : C = C' := Subgroup.eq_of_le_of_card_ge le_sup_left hle
    apply hxVC
    have hxC' : x ∈ C' := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
    rw [← heq] at hxC'
    exact Subgroup.mem_sup_right hxC'
  apply le_antisymm
  · exact sup_le h.V_le (hCV₂.trans h.V₂_le)
  · rw [← h.sup_eq]
    exact sup_le le_sup_left hV₂le

end Complement

end JStructure

end CFSG.CGT.PushingUpLit.A78
