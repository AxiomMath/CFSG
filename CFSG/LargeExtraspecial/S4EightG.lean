module

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

namespace CFSG.LargeExtraspecial.S4

open Subgroup

variable {X : Type*} [Group X] [Finite X]

theorem inf_eq_bot_of_odd_of_isPGroup {F P : Subgroup X} (hF : Odd (Nat.card F))
    (hP : IsPGroup 2 P) : F ⊓ P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  refine (disjoint_of_coprime_natCard ?_).eq_bot
  rw [hn]
  exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hF)

theorem commute_of_mem_normalizer {F L : Subgroup X} (hF : Odd (Nat.card F))
    (hL : IsPGroup 2 L) (hLF : L ≤ normalizer (F : Set X)) {f : X} (hf : f ∈ F)
    (hfN : f ∈ normalizer (L : Set X)) {l : X} (hl : l ∈ L) : l * f = f * l := by
  have h1 : f * l * f⁻¹ * l⁻¹ ∈ L :=
    mul_mem ((mem_normalizer_iff.mp hfN l).mp hl) (inv_mem hl)
  have h2 : f * l * f⁻¹ * l⁻¹ ∈ F := by
    rw [show f * l * f⁻¹ * l⁻¹ = f * (l * f⁻¹ * l⁻¹) by group]
    exact mul_mem hf ((mem_normalizer_iff.mp (hLF hl) f⁻¹).mp (inv_mem hf))
  have h3 : f * l * f⁻¹ * l⁻¹ ∈ F ⊓ L := mem_inf.mpr ⟨h2, h1⟩
  rw [inf_eq_bot_of_odd_of_isPGroup hF hL, mem_bot] at h3
  have := congrArg (· * l) h3
  simp only [one_mul, inv_mul_cancel_right] at this
  calc l * f = f * l * f⁻¹ * f := by rw [this]
    _ = f * l := by group

theorem card_le_of_isPGroup_le_sup {F L P : Subgroup X} (hF : Odd (Nat.card F))
    (hLF : L ≤ normalizer (F : Set X)) (hP : IsPGroup 2 P) (hPle : P ≤ F ⊔ L) :
    Nat.card P ≤ Nat.card L := by
  classical
  have hset := coe_mul_of_right_le_normalizer_left F L hLF
  have hdec : ∀ p : P, ∃ fl : F × L, (fl.1 : X) * fl.2 = p := by
    intro p
    have : (p : X) ∈ ((F ⊔ L : Subgroup X) : Set X) := hPle p.2
    rw [hset] at this
    obtain ⟨f, hf, l, hl, hfl⟩ := this
    exact ⟨(⟨f, hf⟩, ⟨l, hl⟩), hfl⟩
  choose φ hφ using hdec
  refine Nat.card_le_card_of_injective (fun p => (φ p).2) fun p q hpq => ?_
  have hFP := inf_eq_bot_of_odd_of_isPGroup hF hP
  have h1 : (p : X) * (q : X)⁻¹ = ((φ p).1 : X) * ((φ q).1 : X)⁻¹ := by
    rw [← hφ p, ← hφ q]
    simp only at hpq
    rw [hpq]
    group
  have h2 : (p : X) * (q : X)⁻¹ ∈ F ⊓ P :=
    mem_inf.mpr ⟨h1 ▸ mul_mem (φ p).1.2 (inv_mem (φ q).1.2), mul_mem p.2 (inv_mem q.2)⟩
  rw [hFP, mem_bot, mul_inv_eq_one] at h2
  exact Subtype.ext h2

theorem exists_eq_map_conj_of_card_eq {F L P : Subgroup X} (hF : Odd (Nat.card F))
    (hL : IsPGroup 2 L) (hLF : L ≤ normalizer (F : Set X)) (hP : IsPGroup 2 P)
    (hPle : P ≤ F ⊔ L) (hcard : Nat.card P = Nat.card L) :
    ∃ f ∈ F, P = L.map (MulAut.conj f).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := F ⊔ L with hY
  have hsyl : ∀ Q : Subgroup X, IsPGroup 2 Q → Q ≤ Y → Nat.card L ≤ Nat.card Q →
      ∃ S : Sylow 2 Y, (S : Subgroup Y) = Q.subgroupOf Y := by
    intro Q hQ hQY hQc
    have hQ' : IsPGroup 2 (Q.subgroupOf Y) := hQ.comap_of_injective _ Y.subtype_injective
    obtain ⟨S, hS⟩ := hQ'.exists_le_sylow
    refine ⟨S, le_antisymm ?_ hS⟩
    have hSc : Nat.card S ≤ Nat.card L := by
      have h1 := card_le_of_isPGroup_le_sup hF hLF (S.isPGroup'.map Y.subtype)
        (by rintro _ ⟨y, -, rfl⟩; exact y.2)
      rwa [card_map_of_injective Y.subtype_injective] at h1
    have hQc' : Nat.card (Q.subgroupOf Y) = Nat.card Q := by
      rw [← card_map_of_injective Y.subtype_injective, subgroupOf_map_subtype,
        inf_eq_left.mpr hQY]
    exact (eq_of_le_of_card_ge hS (by omega)).ge
  obtain ⟨SL, hSL⟩ := hsyl L hL le_sup_right le_rfl
  obtain ⟨SP, hSP⟩ := hsyl P hP hPle hcard.ge
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y SL SP
  have hy' : (P.subgroupOf Y) = (L.subgroupOf Y).map (MulAut.conj y).toMonoidHom := by
    rw [← hSP, ← hSL, ← hy, Sylow.coe_subgroup_smul]
    rfl
  have hyFL : ((y : X) ∈ ((F ⊔ L : Subgroup X) : Set X)) := y.2
  rw [coe_mul_of_right_le_normalizer_left F L hLF] at hyFL
  obtain ⟨f, hf, l, hl, hfl⟩ := hyFL
  refine ⟨f, hf, ?_⟩
  have hPY : P ≤ Y := hPle
  ext x
  constructor
  · intro hx
    have hx' : (⟨x, hPY hx⟩ : Y) ∈ (L.subgroupOf Y).map (MulAut.conj y).toMonoidHom := by
      rw [← hy']
      exact hx
    obtain ⟨w, hw, hwx⟩ := hx'
    refine ⟨l * w * l⁻¹, mul_mem (mul_mem hl hw) (inv_mem hl), ?_⟩
    have := congrArg Subtype.val hwx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at this ⊢
    rw [← this, ← hfl]
    group
  · rintro ⟨w, hw, rfl⟩
    have hwY : (l⁻¹ * w * l : X) ∈ L := mul_mem (mul_mem (inv_mem hl) hw) hl
    have hwY' : (l⁻¹ * w * l : X) ∈ Y := (le_sup_right (a := F) (b := L)) hwY
    have hmem : (MulAut.conj y).toMonoidHom (⟨l⁻¹ * w * l, hwY'⟩ : Y) ∈
        P.subgroupOf Y := by
      rw [hy']
      exact ⟨_, hwY, rfl⟩
    have : ((MulAut.conj y).toMonoidHom (⟨l⁻¹ * w * l, hwY'⟩ : Y) : X) =
        (MulAut.conj f).toMonoidHom w := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [← hfl]
      group
    rw [← this]
    exact hmem

end CFSG.LargeExtraspecial.S4
