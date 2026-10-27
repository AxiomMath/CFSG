module

import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GroupTheory.PStability.Quadratic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
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
public import Mathlib.GroupTheory.Frattini
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
import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryAutomorphismEnd
import CFSG.LocalAnalysis.SignalizerFunctor.FrattiniQuotientActions
import CFSG.LocalAnalysis.SignalizerFunctor.SolvableConjugatePairCore

public section

namespace CFSG

private theorem conjugatePairSubgroup_eq {G : Type*} [Group G] (a c : G) :
    SignalizerFunctor.Helpers.conjugatePairSubgroup a c =
      Subgroup.closure ({a, c * a * c⁻¹} : Set G) := by
  unfold SignalizerFunctor.Helpers.conjugatePairSubgroup
    SignalizerFunctor.Helpers.conjugateSubgroup
  rw [MonoidHom.map_zpowers, Set.insert_eq, Subgroup.closure_union,
    ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

private theorem mem_pCore_of_forall_isPGroup_closure_pair (p : ℕ) [Fact p.Prime]
    {G : Type*} [Group G] [Finite G] [Group.IsSolvable G] (a : G)
    (hpairs : ∀ g : G, IsPGroup p (Subgroup.closure ({a, g⁻¹ * a * g} : Set G))) :
    a ∈ pCore p G := by
  rw [pCore_eq_helpersPrimeSetCore Fact.out]
  refine SignalizerFunctor.Helpers.solvable_conjugate_pair_core p Fact.out a fun c => ?_
  rw [conjugatePairSubgroup_eq]
  have h := hpairs c⁻¹
  rwa [inv_inv] at h

private theorem mk_mem_pCore_of_isQuadratic (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (K V : Type*) {G : Type*} [Field K] [CharP K p] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Group G] [Finite G] [Group.IsSolvable G]
    (ρ : G →* LinearMap.GeneralLinearGroup K V) (x : G)
    (hrange : 5 ≤ p ∨ Odd (Nat.card G)) (hquad : IsQuadratic (ρ x)) :
    (QuotientGroup.mk' ρ.ker x : G ⧸ ρ.ker) ∈ pCore p (G ⧸ ρ.ker) := by
  have : Finite ρ.range := Finite.of_surjective ρ.rangeRestrict ρ.rangeRestrict_surjective
  have : Group.IsSolvable ρ.range := Group.isSolvable_of_surjective ρ.rangeRestrict_surjective
  let γ : ρ.range := ρ.rangeRestrict x
  have hpair (δ : ρ.range) :
      IsPGroup p (Subgroup.closure ({γ, δ⁻¹ * γ * δ} : Set ρ.range)) := by
    let a := ρ x
    let b := (δ : LinearMap.GeneralLinearGroup K V)⁻¹ * a * δ
    have hle : Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)) ≤ ρ.range := by
      rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact γ.property
      · exact ρ.range.mul_mem (ρ.range.mul_mem (ρ.range.inv_mem δ.2) γ.property) δ.2
    have : Finite (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) :=
      Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have : Group.IsSolvable (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V))) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have hrange' : 5 ≤ p ∨
        Odd (Nat.card (Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)))) :=
      hrange.imp_right fun hodd => hodd.of_dvd_nat
        ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_range_dvd ρ))
    have hpg := isPGroup_closure_pair_of_isQuadratic p hpodd K V a b hquad
      ((quadratic_linear_p_elements p K V a hquad).2 δ) hrange'
    have hmap : (Subgroup.closure ({γ, δ⁻¹ * γ * δ} : Set ρ.range)).map ρ.range.subtype =
        Subgroup.closure ({a, b} : Set (LinearMap.GeneralLinearGroup K V)) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      simp [γ, a, b]
    rw [← hmap] at hpg
    exact hpg.of_injective (ρ.range.subtype.subgroupMap _)
      (MonoidHom.subgroupMap_injective _ _ ρ.range.subtype_injective)
  have hcore : γ ∈ pCore p ρ.range := mem_pCore_of_forall_isPGroup_closure_pair p γ hpair
  let f : G ⧸ ρ.ker ≃* ρ.range := QuotientGroup.quotientKerEquivRange ρ
  have hthis : f (QuotientGroup.mk' ρ.ker x) ∈ (pCore p (G ⧸ ρ.ker)).map f.toMonoidHom := by
    rw [pCore_map_iso p f]
    exact hcore
  obtain ⟨y, hy, hyf⟩ := Subgroup.mem_map.mp hthis
  exact f.injective hyf ▸ hy

private theorem comap_pCore_quotient (p : ℕ) {H : Type*} [Group H] (N : Subgroup H) [N.Normal]
    (hNp : IsPGroup p N) :
    (pCore p (H ⧸ N)).comap (QuotientGroup.mk' N) = pCore p H := by
  apply le_antisymm
  · rw [show pCore p H = sSup {K : Subgroup H | K.Normal ∧ IsPGroup p K} from rfl]
    refine le_sSup ⟨(pCore_normal (G := H ⧸ N) (p := p)).comap (QuotientGroup.mk' N), ?_⟩
    refine (pCore_isPGroup (G := H ⧸ N) (p := p)).comap_of_ker_isPGroup _ ?_
    rwa [QuotientGroup.ker_mk']
  · rw [← Subgroup.map_le_iff_le_comap,
      show pCore p (H ⧸ N) = sSup {K : Subgroup (H ⧸ N) | K.Normal ∧ IsPGroup p K} from rfl]
    exact le_sSup ⟨(pCore_normal (G := H) (p := p)).map _ (QuotientGroup.mk'_surjective N),
      (pCore_isPGroup (G := H) (p := p)).map _⟩

theorem lt_normalizer_of_isPGroup
    (p : ℕ) [Fact p.Prime] (P : Type*) [Group P] [Finite P]
    (hP : IsPGroup p P) (U : Subgroup P) (hU : U < ⊤) :
    U < Subgroup.normalizer (U : Set P) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  exact Group.normalizerCondition_of_isNilpotent U hU

private noncomputable def mulAutToGL (p : ℕ) (A : Type*) [CommGroup A]
    [Module (ZMod p) (Additive A)] :
    MulAut A →* LinearMap.GeneralLinearGroup (ZMod p) (Additive A) :=
  (Units.map (SignalizerFunctor.Helpers.elementaryAutomorphismEnd p)).comp toUnits.toMonoidHom

private theorem mulAutToGL_apply_ofMul (p : ℕ) {A : Type*} [CommGroup A]
    [Module (ZMod p) (Additive A)] (a : MulAut A) (x : A) :
    ((mulAutToGL p A a).val : Additive A →ₗ[ZMod p] Additive A) (Additive.ofMul x) =
      Additive.ofMul (a x) :=
  rfl

private theorem mulAutToGL_injective (p : ℕ) (A : Type*) [CommGroup A]
    [Module (ZMod p) (Additive A)] : Function.Injective (mulAutToGL p A) := fun _ _ h =>
  SignalizerFunctor.Helpers.elementary_automorphism_end_injective p (congrArg Units.val h)

open scoped IsMulCommutative in
private theorem mem_pCore_of_faithful (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    {H P : Type*} [Group H] [Finite H] [Group.IsSolvable H] [Group P] [Finite P]
    (hP : IsPGroup p P) (ρ : H →* MulAut P) (hρ : Function.Injective ρ) (x : H)
    (hrange : 5 ≤ p ∨ Odd (Nat.card H))
    (hquad : ∀ u : P, (ρ x) (u⁻¹ * (ρ x) u) = u⁻¹ * (ρ x) u) :
    x ∈ pCore p H := by
  classical
  obtain ⟨hchar, hEA⟩ := frattini_elementary_quotient p P hP
  let φ : H →* MulAut (P ⧸ frattini P) :=
    (SignalizerFunctor.Helpers.frattiniQuotientAutomorphism P).comp ρ
  let ψ : H →* LinearMap.GeneralLinearGroup (ZMod p) (Additive (P ⧸ frattini P)) :=
    (mulAutToGL p (P ⧸ frattini P)).comp φ
  have hNp : IsPGroup p ψ.ker := by
    have hker : ψ.ker = φ.ker := by
      ext h
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact (mulAutToGL_injective p _).eq_iff' (map_one _)
    rw [hker]
    exact SignalizerFunctor.Helpers.faithful_frattini_action_kernel_pgroup p Fact.out hP ρ hρ
  have hquadψ : IsQuadratic (ψ x) := by
    have hαN (u : P) : u ∈ frattini P ↔ (ρ x) u ∈ frattini P :=
      (SetLike.ext_iff.mp (hchar.fixed (ρ x)) u).symm
    refine quadratic_elementary_quotient p P (frattini P) (ρ x) hαN (ψ x) (fun u => ?_) hquad
    change (mulAutToGL p (P ⧸ frattini P) (φ x)).val
        (Additive.ofMul (QuotientGroup.mk' (frattini P) u)) =
      Additive.ofMul (QuotientGroup.mk' (frattini P) ((ρ x) u))
    rw [mulAutToGL_apply_ofMul]
    exact congrArg Additive.ofMul
      (SignalizerFunctor.Helpers.frattini_quotient_automorphism_equivariant (ρ x) u)
  have hlin := mk_mem_pCore_of_isQuadratic p hpodd (ZMod p) (Additive (P ⧸ frattini P)) ψ x
    hrange hquadψ
  rw [← comap_pCore_quotient p ψ.ker hNp]
  exact hlin

theorem solvable_action_p_stability
    (p : ℕ) [Fact p.Prime] (hpodd : Odd p)
    (G P : Type*) [Group G] [Finite G] [Group.IsSolvable G]
    [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : G →* MulAut P) (x : G)
    (hrange : 5 ≤ p ∨ Odd (Nat.card G))
    (hquad : ∀ u : P, (ρ x) (u⁻¹ * (ρ x) u) = u⁻¹ * (ρ x) u) :
    (QuotientGroup.mk' ρ.ker x : G ⧸ ρ.ker) ∈ pCore p (G ⧸ ρ.ker) := by
  refine mem_pCore_of_faithful p hpodd hP (QuotientGroup.lift ρ.ker ρ le_rfl)
    ((QuotientGroup.injective_lift_iff (N := ρ.ker) ρ le_rfl).mpr rfl) _
    (hrange.imp_right fun hodd => hodd.of_dvd_nat ?_) hquad
  rw [← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_card ρ.ker

end CFSG
