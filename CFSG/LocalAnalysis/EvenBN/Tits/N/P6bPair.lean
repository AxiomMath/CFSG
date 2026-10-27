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
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P6b

@[expose] def fixedSub {V : Type*} [Group V] (U : Set (MulAut V)) : Subgroup V where
  carrier := {v | ∀ u ∈ U, u v = v}
  mul_mem' := fun {a b} ha hb u hu => by rw [map_mul, ha u hu, hb u hu]
  one_mem' := fun u _ => map_one u
  inv_mem' := fun {a} ha u hu => by rw [map_inv, ha u hu]

private theorem p6b_exists_gen {G : Type*} [Group G] (hG2 : ∀ a : G, a * a = 1)
    (hGc : ∀ a b : G, a * b = b * a) (hcard : Nat.card G = 2 ^ 4) :
    ∃ g : Fin 4 → G, Subgroup.closure (Set.range g) = ⊤ := by
  haveI : Finite G := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  letI : CommGroup G := { ‹Group G› with mul_comm := hGc }
  letI : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule fun x =>
    (two_nsmul x).trans (congrArg Additive.ofMul (hG2 (Additive.toMul x)))
  have hfin : Module.finrank (ZMod 2) (Additive G) = 4 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive G)
    rw [Nat.card_congr Additive.toMul, hcard, Nat.card_zmod] at h
    exact (Nat.pow_right_injective (le_refl 2) h).symm
  let b := Module.finBasisOfFinrankEq (ZMod 2) (Additive G) hfin
  refine ⟨fun i => Additive.toMul (b i), ?_⟩
  have hspan : Submodule.span (ZMod 2) (Set.range b) ≤
      AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup
        (Subgroup.closure (Set.range fun i => Additive.toMul (b i)))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show Additive.toMul (b i) ∈ Subgroup.closure (Set.range fun i => Additive.toMul (b i))
    exact Subgroup.subset_closure ⟨i, rfl⟩
  rw [b.span_eq] at hspan
  exact eq_top_iff.2 fun x _ => hspan (Submodule.mem_top : Additive.ofMul x ∈ ⊤)

private theorem p6b_index_fixedSub_le {V : Type*} [Group V] [Finite V]
    (hV : ∀ a b : V, a * b = b * a) (L : Subgroup V) (hL : Nat.card L ≤ 2) (u : MulAut V)
    (hu : ∀ v : V, v⁻¹ * u v ∈ L) : (fixedSub ({u} : Set (MulAut V))).index ≤ 2 := by
  letI : CommGroup V := { ‹Group V› with mul_comm := hV }
  let φ : V →* L :=
    { toFun := fun v => ⟨v⁻¹ * u v, hu v⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        ext
        simp only [map_mul, mul_inv_rev, Subgroup.coe_mul]
        rw [mul_comm b⁻¹ a⁻¹, mul_mul_mul_comm] }
  have hker : φ.ker = fixedSub ({u} : Set (MulAut V)) := by
    ext v
    constructor
    · intro hv w hw
      rw [Set.mem_singleton_iff.1 hw]
      have h : v⁻¹ * u v = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hv)
      exact (inv_mul_eq_one.1 h).symm
    · intro hv
      exact MonoidHom.mem_ker.2 (Subtype.ext (inv_mul_eq_one.2 (hv u rfl).symm))
  rw [← hker, Subgroup.index_ker]
  exact (Subgroup.card_le_card_group _).trans hL

theorem card_le_mul_card_fixedSub {V : Type*} [Group V] [Finite V]
    (hV : ∀ a b : V, a * b = b * a) (hV2 : ∀ a : V, a * a = 1)
    (U : Subgroup (MulAut V)) (hU2 : ∀ u ∈ U, u * u = 1)
    (hUc : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ * u₂ = u₂ * u₁) (hUcard : Nat.card U = 2 ^ 4)
    (L : Subgroup V) (hL : Nat.card L ≤ 2) (hUL : ∀ u ∈ U, ∀ v : V, v⁻¹ * u v ∈ L) :
    Nat.card V ≤ 2 ^ 4 * Nat.card (fixedSub (U : Set (MulAut V))) := by
  obtain ⟨g, hg⟩ := p6b_exists_gen (G := U) (fun a => Subtype.ext (hU2 a a.2))
    (fun a b => Subtype.ext (hUc a a.2 b b.2)) hUcard
  have hinf : (⨅ i, fixedSub ({(g i : MulAut V)} : Set (MulAut V))) ≤
      fixedSub (U : Set (MulAut V)) := by
    intro v hv w hw
    rw [Subgroup.mem_iInf] at hv
    have key : ∀ x : U, x ∈ Subgroup.closure (Set.range g) → (x : MulAut V) v = v := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hv i _ rfl
      | one => rfl
      | mul x y _ _ hx hy => exact (congrArg (x : MulAut V) hy).trans hx
      | inv x _ hx =>
        calc ((x⁻¹ : U) : MulAut V) v = ((x : MulAut V)⁻¹) ((x : MulAut V) v) := by rw [hx]; rfl
          _ = v := by simp
    exact key ⟨w, hw⟩ (by rw [hg]; trivial)
  have hidx : (⨅ i, fixedSub ({(g i : MulAut V)} : Set (MulAut V))).index ≤ 2 ^ 4 := by
    refine (Subgroup.index_iInf_le _).trans ?_
    calc ∏ i, (fixedSub ({(g i : MulAut V)} : Set (MulAut V))).index ≤ ∏ _i : Fin 4, 2 :=
          Finset.prod_le_prod fun i _ => p6b_index_fixedSub_le hV L hL _ (hUL _ (g i).2)
      _ = 2 ^ 4 := by simp
  calc Nat.card V
      = (fixedSub (U : Set (MulAut V))).index * Nat.card (fixedSub (U : Set (MulAut V))) :=
        (Subgroup.index_mul_card _).symm
    _ ≤ 2 ^ 4 * Nat.card (fixedSub (U : Set (MulAut V))) :=
        Nat.mul_le_mul_right _ ((Subgroup.index_antitone hinf).trans hidx)

end CFSG.LocalAnalysis.EvenBN.Tits.N.P6b
