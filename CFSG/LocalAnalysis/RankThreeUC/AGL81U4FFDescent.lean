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
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LocalAnalysis.RankThreeUC

lemma add_self_eq_zero_of_charP_two {K C : Type*} [Field K] [CharP K 2] [AddCommGroup C]
    [Module K C] (x : C) : x + x = 0 := by
  have h : (2 : ℕ) • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]
  rwa [two_nsmul] at h

@[expose] def involTrace {C : Type*} [AddCommGroup C] (s : C ≃+ C) : C →+ C :=
  AddMonoidHom.mk' (fun x => x + s x) (fun x y => by
    simp only [map_add]
    abel)

lemma involTrace_apply {C : Type*} [AddCommGroup C] (s : C ≃+ C) (x : C) :
    involTrace s x = x + s x :=
  rfl

lemma involTrace_eq_zero_iff {C : Type*} [AddCommGroup C] (s : C ≃+ C)
    (hch : ∀ x : C, x + x = 0) (x : C) : involTrace s x = 0 ↔ s x = x := by
  rw [involTrace_apply]
  constructor
  · intro h
    calc s x = s x + (x + x) := by rw [hch x, add_zero]
      _ = (x + s x) + x := by abel
      _ = x := by rw [h, zero_add]
  · intro h
    rw [h, hch x]

lemma involTrace_map_fix {C : Type*} [AddCommGroup C] (s : C ≃+ C)
    (hss : ∀ x, s (s x) = x) (x : C) : s (involTrace s x) = involTrace s x := by
  rw [involTrace_apply, map_add, hss]
  exact add_comm _ _

lemma exists_involTrace_eq_of_fix {K C : Type*} [Field K] [CharP K 2] [AddCommGroup C]
    [Module K C] (σ : K →+* K) (hσ : ∀ c, σ (σ c) = c) (hσne : ∃ c, σ c ≠ c) (s : C ≃+ C)
    (hs : ∀ (c : K) (x : C), s (c • x) = σ c • s x) (x : C) (hx : s x = x) :
    ∃ y, involTrace s y = x := by
  obtain ⟨t, ht⟩ := hσne
  have hu : t + σ t ≠ 0 := by
    intro h
    apply ht
    calc σ t = σ t + (t + t) := by
          rw [add_self_eq_zero_of_charP_two (K := K) (C := K) t, add_zero]
      _ = (t + σ t) + t := by abel
      _ = t := by rw [h, zero_add]
  have hσu : σ (t + σ t) = t + σ t := by
    rw [map_add, hσ]
    exact add_comm _ _
  refine ⟨(t * (t + σ t)⁻¹) • x, ?_⟩
  rw [involTrace_apply, hs, hx, map_mul, map_inv₀, hσu, ← add_smul, ← add_mul,
    mul_inv_cancel₀ hu, one_smul]

theorem card_fix_sq_of_semilinear_involution {K C : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup C] [Module K C] [Finite C] (σ : K →+* K) (hσ : ∀ c, σ (σ c) = c)
    (hσne : ∃ c, σ c ≠ c) (s : C ≃+ C) (hs : ∀ (c : K) (x : C), s (c • x) = σ c • s x)
    (hss : ∀ x, s (s x) = x) :
    Nat.card {x : C // s x = x} ^ 2 = Nat.card C := by
  have hch : ∀ x : C, x + x = 0 := fun x => add_self_eq_zero_of_charP_two (K := K) (C := C) x
  have hker : ∀ x, x ∈ (involTrace s).ker ↔ s x = x := fun x => by
    rw [AddMonoidHom.mem_ker]
    exact involTrace_eq_zero_iff s hch x
  have hrange : ∀ x, x ∈ (involTrace s).range ↔ s x = x := fun x => by
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact involTrace_map_fix s hss y
    · intro hx
      exact exists_involTrace_eq_of_fix σ hσ hσne s hs x hx
  have hker_card : Nat.card (involTrace s).ker = Nat.card {x : C // s x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight hker)
  have hrange_card : Nat.card (involTrace s).range = Nat.card {x : C // s x = x} :=
    Nat.card_congr (Equiv.subtypeEquivRight hrange)
  have hindex : Nat.card (involTrace s).ker * Nat.card (involTrace s).range = Nat.card C :=
    AddSubgroup.card_ker_mul_card_range (involTrace s)
  rw [← hindex, hker_card, hrange_card, sq]

lemma eq_of_mul_self_eq_one_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  by_contra hab
  have hsub : ({1, a, b} : Finset G) ⊆ Finset.univ.filter (fun x : G => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ x, ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · rw [sq]
      exact ha
    · rw [sq]
      exact hb
  have h3 : ({1, a, b} : Finset G).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, a, b, ha1.symm, hb1.symm, hab, rfl⟩
  have hle : (Finset.univ.filter (fun x : G => x ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have := Finset.card_le_card hsub
  omega

theorem ringAut_involution_unique {F : Type*} [Field F] [Finite F]
    (θ₁ θ₂ : F ≃+* F) (h₁ : ∀ x, θ₁ (θ₁ x) = x) (h₂ : ∀ x, θ₂ (θ₂ x) = x)
    (h₁ne : ∃ x, θ₁ x ≠ x) (h₂ne : ∃ x, θ₂ x ≠ x) : θ₁ = θ₂ := by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F (ringChar F)⟩
  letI : Algebra (ZMod (ringChar F)) F := ZMod.algebra F (ringChar F)
  have hfix : ∀ θ : F ≃+* F, ∀ x : ZMod (ringChar F),
      θ (algebraMap (ZMod (ringChar F)) F x) = algebraMap (ZMod (ringChar F)) F x := by
    intro θ x
    have h := RingHom.ext_zmod ((θ : F →+* F).comp (algebraMap (ZMod (ringChar F)) F))
      (algebraMap (ZMod (ringChar F)) F)
    exact congrArg (fun f : ZMod (ringChar F) →+* F => f x) h
  let toAlg : (F ≃+* F) → (F ≃ₐ[ZMod (ringChar F)] F) := fun θ =>
    AlgEquiv.ofRingEquiv (R := ZMod (ringChar F)) (f := θ) (hfix θ)
  have happ : ∀ θ : F ≃+* F, ∀ x, toAlg θ x = θ x := fun θ x => rfl
  have hsq : ∀ θ : F ≃+* F, (∀ x, θ (θ x) = x) → toAlg θ * toAlg θ = 1 := by
    intro θ hθ
    ext x
    simp only [AlgEquiv.mul_apply, AlgEquiv.one_apply, happ]
    exact hθ x
  have hne : ∀ θ : F ≃+* F, (∃ x, θ x ≠ x) → toAlg θ ≠ 1 := by
    rintro θ ⟨x, hx⟩ h
    apply hx
    have := congrArg (fun τ : F ≃ₐ[ZMod (ringChar F)] F => τ x) h
    simpa [happ] using this
  haveI : Finite (F ≃ₐ[ZMod (ringChar F)] F) :=
    Finite.of_injective (DFunLike.coe : (F ≃ₐ[ZMod (ringChar F)] F) → (F → F))
      DFunLike.coe_injective
  have key := eq_of_mul_self_eq_one_of_isCyclic (hsq θ₁ h₁) (hsq θ₂ h₂) (hne θ₁ h₁ne)
    (hne θ₂ h₂ne)
  ext x
  have := congrArg (fun τ : F ≃ₐ[ZMod (ringChar F)] F => τ x) key
  simpa [happ] using this

end CFSG.LocalAnalysis.RankThreeUC
