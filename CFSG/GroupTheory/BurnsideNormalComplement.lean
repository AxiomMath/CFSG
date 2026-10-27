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
public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
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

open scoped Classical

namespace CFSG.GroupTheory

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem le_of_normal_coprime_of_isPGroup_quotient (K H : Subgroup G) [K.Normal]
    (hq : IsPGroup p (G ⧸ K)) (hH : ¬ p ∣ Nat.card H) : H ≤ K := by
  have himage : IsPGroup p (H.map (QuotientGroup.mk' K)) := hq.to_subgroup _
  have hcard : Nat.card (H.map (QuotientGroup.mk' K)) ∣ Nat.card H :=
    Subgroup.card_map_dvd H (QuotientGroup.mk' K)
  have htriv : H.map (QuotientGroup.mk' K) = ⊥ := by
    obtain ⟨n, hn⟩ := himage.exists_card_eq
    cases n with
    | zero =>
      rw [pow_zero] at hn
      exact Subgroup.card_eq_one.mp hn
    | succ n =>
      exfalso
      apply hH
      rw [hn] at hcard
      exact (dvd_pow_self p n.succ_ne_zero).trans hcard
  intro h hh
  have : QuotientGroup.mk' K h = 1 := by
    have hmem : QuotientGroup.mk' K h ∈ H.map (QuotientGroup.mk' K) := ⟨h, hh, rfl⟩
    rw [htriv] at hmem
    exact hmem
  exact (QuotientGroup.eq_one_iff h).mp this

theorem burnside_normal_complement (P : Sylow p G)
    (hP : Subgroup.normalizer (P : Set G) ≤ Subgroup.centralizer (P : Set G)) :
    ∃ (K : Subgroup G) (_ : K.Normal), ¬ p ∣ Nat.card K ∧ K.index = Nat.card P ∧
      (∀ K' : Subgroup G, K'.Normal → ¬ p ∣ Nat.card K' → K'.index = Nat.card P → K' = K) ∧
      K.Characteristic ∧ Subgroup.IsComplement' K P ∧ K ⊔ (P : Subgroup G) = ⊤ ∧
      K ⊓ (P : Subgroup G) = ⊥ ∧
      (∃ e : (P : Subgroup G) ≃* G ⧸ K, ∀ x : (P : Subgroup G), e x = ((x : G) : G ⧸ K)) ∧
      ∀ a b : G ⧸ K, a * b = b * a := by
  set K := (MonoidHom.transferSylow P hP).ker with hKdef
  have hcomp : Subgroup.IsComplement' K P := MonoidHom.ker_transferSylow_isComplement' P hP
  have hKp : ¬ p ∣ Nat.card K := MonoidHom.not_dvd_card_ker_transferSylow P hP
  have hindex : K.index = Nat.card P := hcomp.symm.index_eq_card
  have hsup : K ⊔ (P : Subgroup G) = ⊤ := hcomp.sup_eq_top
  have hinf : K ⊓ (P : Subgroup G) = ⊥ := hcomp.disjoint.eq_bot
  have hPcomm : ∀ a b : (P : Subgroup G), a * b = b * a := by
    intro a b
    apply Subtype.ext
    have hb : (b : G) ∈ Subgroup.centralizer (P : Set G) := hP (Subgroup.le_normalizer b.2)
    exact Subgroup.mem_centralizer_iff.mp hb a a.2
  let f : (P : Subgroup G) →* G ⧸ K := (QuotientGroup.mk' K).comp (P : Subgroup G).subtype
  have hf : Function.Bijective f := by
    constructor
    · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff (x : G)).mp hx
      have : (x : G) ∈ K ⊓ (P : Subgroup G) := ⟨hxK, x.2⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact (Subgroup.mem_bot).mpr (Subtype.ext this)
    · intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨⟨k, x⟩, hkx⟩ := hcomp.existsUnique g |>.exists
      refine ⟨x, ?_⟩
      change ((x : G) : G ⧸ K) = (g : G ⧸ K)
      rw [← hkx, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (k : G)).mpr k.2, one_mul]
  let e : (P : Subgroup G) ≃* G ⧸ K := MulEquiv.ofBijective f hf
  have hpq : IsPGroup p (G ⧸ K) := by
    obtain ⟨n, hn⟩ := P.2.exists_card_eq
    refine IsPGroup.of_card (n := n) ?_
    rw [← Subgroup.index_eq_card, hindex, hn]
  have huniq : ∀ K' : Subgroup G, K'.Normal → ¬ p ∣ Nat.card K' → K'.index = Nat.card P →
      K' = K := by
    intro K' _ hK'p hK'index
    have hle := le_of_normal_coprime_of_isPGroup_quotient K K' hpq hK'p
    apply Subgroup.eq_of_le_of_card_ge hle
    have h1 := Subgroup.card_mul_index K
    have h2 := Subgroup.card_mul_index K'
    rw [hindex] at h1
    rw [hK'index] at h2
    have hpos : 0 < Nat.card P := Nat.card_pos
    exact (Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)).le
  refine ⟨K, inferInstance, hKp, hindex, huniq, ?_, hcomp, hsup, hinf, ⟨e, fun x => rfl⟩, ?_⟩
  ·
    constructor
    intro φ
    apply huniq
    · exact Subgroup.Normal.comap inferInstance _
    · have hcard : Nat.card (K.comap φ.toMonoidHom) = Nat.card K := by
        refine Nat.card_congr (Equiv.ofBijective (fun x => (⟨φ x, x.2⟩ : K)) ⟨?_, ?_⟩)
        · intro x y hxy
          apply Subtype.ext
          apply φ.injective
          exact congrArg Subtype.val hxy
        · intro y
          refine ⟨⟨φ.symm y, ?_⟩, Subtype.ext ?_⟩
          · change φ (φ.symm y) ∈ K
            rw [MulEquiv.apply_symm_apply]
            exact y.2
          · exact φ.apply_symm_apply y
      rw [hcard]
      exact hKp
    · rw [Subgroup.index_comap_of_surjective _ φ.surjective, hindex]
  · intro a b
    obtain ⟨x, rfl⟩ := e.surjective a
    obtain ⟨y, rfl⟩ := e.surjective b
    rw [← map_mul, ← map_mul, hPcomm]

end CFSG.GroupTheory
