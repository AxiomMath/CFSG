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
public import Mathlib.GroupTheory.NoncommCoprod
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

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace OmSeven

@[expose] def powHomThree {G : Type*} [Group G] (u : G) (hu : u ^ 3 = 1) :
    Multiplicative (ZMod 3) →* G where
  toFun a := u ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ZMod.val_add, ← pow_eq_pow_mod _ hu, pow_add]

@[expose] noncomputable def pairHom {G : Type*} [Group G] (u : Fin 3 → G)
    (hu : ∀ i, u i ^ 3 = 1) (hc : ∀ i j, Commute (u i) (u j)) :
    (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →* G :=
  (powHomThree (u 1) (hu 1)).noncommCoprod (powHomThree (u 2) (hu 2))
    (fun _ _ => (hc 1 2).pow_pow _ _)

theorem pairHom_apply {G : Type*} [Group G] (u : Fin 3 → G) (hu : ∀ i, u i ^ 3 = 1)
    (hc : ∀ i j, Commute (u i) (u j)) (b c : Multiplicative (ZMod 3)) :
    pairHom u hu hc (b, c) = u 1 ^ (Multiplicative.toAdd b).val *
      u 2 ^ (Multiplicative.toAdd c).val := by
  simp [pairHom, powHomThree]

theorem commute_powHomThree_pairHom {G : Type*} [Group G] (u : Fin 3 → G)
    (hu : ∀ i, u i ^ 3 = 1) (hc : ∀ i j, Commute (u i) (u j)) (a : Multiplicative (ZMod 3))
    (bc : Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) :
    Commute (powHomThree (u 0) (hu 0) a) (pairHom u hu hc bc) := by
  obtain ⟨b, c⟩ := bc
  rw [pairHom_apply]
  exact ((hc 0 1).pow_pow _ _).mul_right ((hc 0 2).pow_pow _ _)

@[expose] noncomputable def tripleHom {G : Type*} [Group G] (u : Fin 3 → G)
    (hu : ∀ i, u i ^ 3 = 1) (hc : ∀ i j, Commute (u i) (u j)) :
    (Multiplicative (ZMod 3) × (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) →* G :=
  (powHomThree (u 0) (hu 0)).noncommCoprod (pairHom u hu hc)
    (commute_powHomThree_pairHom u hu hc)

theorem tripleHom_apply {G : Type*} [Group G] (u : Fin 3 → G) (hu : ∀ i, u i ^ 3 = 1)
    (hc : ∀ i j, Commute (u i) (u j))
    (a b c : Multiplicative (ZMod 3)) :
    tripleHom u hu hc (a, b, c) = u 0 ^ (Multiplicative.toAdd a).val *
      (u 1 ^ (Multiplicative.toAdd b).val * u 2 ^ (Multiplicative.toAdd c).val) := by
  rw [tripleHom, MonoidHom.noncommCoprod_apply, pairHom_apply]
  rfl

theorem pow_smul_ne_of_ne {G X : Type*} [Group G] [MulAction G X] {u : G} (hu : u ^ 3 = 1)
    {v : X} (hv : u • v ≠ v) {k : ℕ} (hk : k % 3 ≠ 0) : u ^ k • v ≠ v := by
  rw [pow_eq_pow_mod k hu]
  have h : k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h with h | h
  · rw [h, pow_one]
    exact hv
  · rw [h]
    intro h2
    apply hv
    calc u • v = u • (u ^ 2 • v) := by rw [h2]
      _ = (u * u ^ 2) • v := (mul_smul _ _ _).symm
      _ = (u ^ 3) • v := by rw [← pow_succ' u 2]
      _ = v := by rw [hu, one_smul]

theorem tripleHom_injective {G X : Type*} [Group G] [MulAction G X] (u : Fin 3 → G)
    (hu : ∀ i, u i ^ 3 = 1) (hc : ∀ i j, Commute (u i) (u j)) (v : Fin 3 → X)
    (hfix : ∀ i j, i ≠ j → u i • v j = v j) (hmove : ∀ i, u i • v i ≠ v i) :
    Function.Injective (tripleHom u hu hc) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b, c⟩ h
  rw [tripleHom_apply] at h
  have hpf : ∀ i j, i ≠ j → ∀ n : ℕ, u i ^ n • v j = v j := fun i j hij n => by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hfix i j hij, ih]
  have hz : ∀ (i : Fin 3) (m : Multiplicative (ZMod 3)), u i ^ (Multiplicative.toAdd m).val • v i =
      v i → m = 1 := by
    intro i m hm
    by_contra hne
    refine pow_smul_ne_of_ne (hu i) (hmove i) ?_ hm
    have h1 : (Multiplicative.toAdd m) ≠ 0 := fun h0 => hne (by simpa using h0)
    have h2 : (Multiplicative.toAdd m).val ≠ 0 := fun h0 => h1 ((ZMod.val_eq_zero _).1 h0)
    have h3 : (Multiplicative.toAdd m).val < 3 := ZMod.val_lt _
    omega
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · have h0 := congrArg (fun g : G => g • v 0) h
    simp only [one_smul, mul_smul] at h0
    rw [hpf 2 0 (by decide), hpf 1 0 (by decide)] at h0
    exact hz 0 a h0
  · have h0 := congrArg (fun g : G => g • v 1) h
    have e : u 0 ^ (Multiplicative.toAdd a).val *
        (u 1 ^ (Multiplicative.toAdd b).val * u 2 ^ (Multiplicative.toAdd c).val) =
        u 1 ^ (Multiplicative.toAdd b).val *
          (u 0 ^ (Multiplicative.toAdd a).val * u 2 ^ (Multiplicative.toAdd c).val) :=
      ((hc 0 1).pow_pow _ _).left_comm _
    simp only [e, one_smul, mul_smul] at h0
    rw [hpf 2 1 (by decide), hpf 0 1 (by decide)] at h0
    exact hz 1 b h0
  · have h0 := congrArg (fun g : G => g • v 2) h
    have e : u 0 ^ (Multiplicative.toAdd a).val *
        (u 1 ^ (Multiplicative.toAdd b).val * u 2 ^ (Multiplicative.toAdd c).val) =
        u 2 ^ (Multiplicative.toAdd c).val *
          (u 0 ^ (Multiplicative.toAdd a).val * u 1 ^ (Multiplicative.toAdd b).val) := by
      rw [← mul_assoc]
      exact (((hc 0 2).pow_pow _ _).mul_left ((hc 1 2).pow_pow _ _)).eq
    simp only [e, one_smul, mul_smul] at h0
    rw [hpf 1 2 (by decide), hpf 0 2 (by decide)] at h0
    exact hz 2 c h0

end OmSeven

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
