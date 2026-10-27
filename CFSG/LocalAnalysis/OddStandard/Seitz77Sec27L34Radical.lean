module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.FeitThompson.OddOrderTheorem
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Transfer
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

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG

theorem card_mulAut_le_of_elementaryAbelian {p k : ℕ} [Fact p.Prime] {Q : Type} [Group Q]
    [Finite Q] [IsElementaryAbelian p Q] (hcard : Nat.card Q = p ^ k) :
    Nat.card (MulAut Q) ≤ (p ^ k) ^ k := by
  open scoped IsMulCommutative in
  have : Finite (Additive Q) := inferInstanceAs (Finite Q)
  have : Module.Finite (ZMod p) (Additive Q) := inferInstance
  have hrank : Module.finrank (ZMod p) (Additive Q) = k := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive Q)
    rw [Nat.card_zmod] at h1
    have h2 : Nat.card (Additive Q) = p ^ k := hcard
    rw [h2] at h1
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm
  let b := Module.finBasisOfFinrankEq (ZMod p) (Additive Q) hrank
  let F : MulAut Q → (Fin k → Q) := fun φ i => φ (Additive.toMul (b i))
  have hF : Function.Injective F := by
    intro φ ψ h
    have key : (MonoidHom.toAdditive φ.toMonoidHom).toZModLinearMap p =
        (MonoidHom.toAdditive ψ.toMonoidHom).toZModLinearMap p := by
      apply b.ext
      intro i
      exact congrArg Additive.ofMul (congrFun h i)
    ext x
    exact congrArg Additive.toMul (LinearMap.congr_fun key (Additive.ofMul x))
  calc Nat.card (MulAut Q) ≤ Nat.card (Fin k → Q) := Nat.card_le_card_of_injective F hF
    _ = (p ^ k) ^ k := by simp [Nat.card_fun, hcard]

theorem pow_index_eq_one_of_perfect_central {K : Type*} [Group K] [Finite K]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) {z : K} (hz : z ∈ Subgroup.center K)
    (T : Subgroup K) (hzT : z ∈ T) {A : Type*} [CommGroup A] (c : T →* A) :
    c ⟨z, hzT⟩ ^ T.index = 1 := by
  have key : ∀ (k : ℕ) (g₀ : K), g₀⁻¹ * z ^ k * g₀ ∈ T → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have h : Commute g₀ z := Subgroup.mem_center_iff.mp hz g₀
    rw [mul_assoc, ← (h.pow_right k).eq, inv_mul_cancel_left]
  have h1 := MonoidHom.transfer_eq_pow c z key
  have h2 : MonoidHom.transfer c z = 1 := by
    have hker : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ (MonoidHom.transfer c).ker := by
      rw [Subgroup.commutator_le]
      intro g₁ _ g₂ _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)
    rw [hperf] at hker
    exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top z))
  rw [h1] at h2
  rw [← map_pow]
  exact h2

theorem false_of_central_order_three_transfer {K : Type*} [Group K] [Finite K]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) {z : K} (hz : z ∈ Subgroup.center K)
    (hz3 : orderOf z = 3) (T : Subgroup K) (hzT : z ∈ T) (hidx : ¬ 3 ∣ T.index)
    (c : T →* Multiplicative (ZMod 3)) (hc : c ⟨z, hzT⟩ = Multiplicative.ofAdd 1) : False := by
  have _ := hz3
  have h : (c ⟨z, hzT⟩) ^ T.index = 1 := pow_index_eq_one_of_perfect_central hperf hz T hzT c
  rw [hc, ← ofAdd_nsmul] at h
  have h4 : T.index • (1 : ZMod 3) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa using this
  rw [nsmul_one, ZMod.natCast_eq_zero_iff] at h4
  exact hidx h4

theorem subsingleton_of_perfect_of_solvable {H : Type*} [Group H] [Finite H] [Group.IsSolvable H]
    (hperf : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ = ⊤) : Subsingleton H := by
  by_contra h
  rw [not_subsingleton_iff_nontrivial] at h
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial H).ne (by
    rw [commutator_def]
    exact hperf)

theorem perfect_range {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤) :
    ⁅(⊤ : Subgroup f.range), (⊤ : Subgroup f.range)⁆ = ⊤ := by
  have h1 : (⊤ : Subgroup G).map f.rangeRestrict = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top_of_surjective _ f.rangeRestrict_surjective
  rw [← h1, ← Subgroup.map_commutator, hperf]

theorem normal_le_center_of_not_dvd {G : Type} [Group G] [Finite G]
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤)
    (R : Subgroup G) [R.Normal] (hodd : Odd (Nat.card R))
    (hmax : ∀ M : Subgroup G, M.Normal → R ≤ M → M = R ∨ M = ⊤)
    (Q : Subgroup G) [Q.Normal] (hnd : ¬ R.index ∣ Nat.card (MulAut Q)) :
    Q ≤ Subgroup.center G := by
  let θ : G →* MulAut Q := MulAut.conjNormal
  have hRsolv : Group.IsSolvable R := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have hCnormal : θ.ker.Normal := MonoidHom.normal_ker θ
  have hcase := hmax (R ⊔ θ.ker) inferInstance le_sup_left
  have hall : ∀ g : G, θ g = 1 := by
    rcases hcase with hRC | hRC
    ·
      exfalso
      have hCR : θ.ker ≤ R := hRC ▸ le_sup_right
      have h1 : R.index ∣ θ.ker.index := Subgroup.index_dvd_of_le hCR
      have h2 : θ.ker.index = Nat.card θ.range := Subgroup.index_ker θ
      have h3 : Nat.card θ.range ∣ Nat.card (MulAut Q) := Subgroup.card_subgroup_dvd_card _
      exact hnd (h1.trans (h2 ▸ h3))
    ·
      have hsolv : Group.IsSolvable θ.range := by
        let f : R →* θ.range := θ.rangeRestrict.comp R.subtype
        have hsurj : Function.Surjective f := by
          rintro ⟨x, g, rfl⟩
          have hg : g ∈ R ⊔ θ.ker := hRC ▸ Subgroup.mem_top g
          obtain ⟨r, hr, c, hc, hrc⟩ := Subgroup.mem_sup_of_normal_left.1 hg
          refine ⟨⟨r, hr⟩, Subtype.ext ?_⟩
          simp only [f, MonoidHom.comp_apply, Subgroup.coe_subtype]
          rw [MonoidHom.coe_rangeRestrict, ← hrc, map_mul, MonoidHom.mem_ker.1 hc, mul_one]
        exact Group.isSolvable_of_surjective hsurj
      have hsub : Subsingleton θ.range :=
        subsingleton_of_perfect_of_solvable (perfect_range θ hperf)
      intro g
      have := hsub.elim ⟨θ g, ⟨g, rfl⟩⟩ 1
      exact congrArg Subtype.val this
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro g
  have h := congrArg (fun a : MulAut Q => ((a ⟨q, hq⟩ : Q) : G)) (hall g)
  simp only [θ, MulAut.conjNormal_apply, MulAut.one_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h

theorem minimal_normal_le_center {G : Type} [Group G] [Finite G]
    (hperf : ⁅(⊤ : Subgroup G), (⊤ : Subgroup G)⁆ = ⊤)
    (R : Subgroup G) [R.Normal] (hodd : Odd (Nat.card R))
    (hmax : ∀ M : Subgroup G, M.Normal → R ≤ M → M = R ∨ M = ⊤) (hidx : 20160 ≤ R.index)
    (Q : Subgroup G) [Q.Normal] {p k : ℕ} [Fact p.Prime] [IsElementaryAbelian p Q]
    (hQ : Nat.card Q = p ^ k) (hbound : (p ^ k) ^ k < 20160) :
    Q ≤ Subgroup.center G := by
  refine normal_le_center_of_not_dvd hperf R hodd hmax Q fun hdvd => ?_
  have h4 := card_mulAut_le_of_elementaryAbelian hQ
  have hpos : 0 < Nat.card (MulAut Q) := Nat.card_pos
  have := Nat.le_of_dvd hpos hdvd
  omega

end CFSG.OddStandard.Seitz77
