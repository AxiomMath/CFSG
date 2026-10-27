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
public import Mathlib.GroupTheory.SchurZassenhaus
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

namespace CFSG.ComponentClassification.CatFC.DS81

universe u v

theorem exists_hom_section_of_coprime_card {G : Type u} {Q : Type v} [Group G] [Finite G]
    [Group Q] (π : G →* Q) (hπ : Function.Surjective π) (P : Subgroup Q)
    (hcop : Nat.Coprime (Nat.card π.ker) (Nat.card P)) :
    ∃ σ : P →* G, ∀ p : P, π (σ p) = p := by
  classical
  haveI : Finite Q := Finite.of_surjective π hπ
  let P' : Subgroup G := P.comap π
  let ψ : P' →* P := (π.domRestrict P').codRestrict P (fun a => a.2)
  have hψπ : ∀ a : P', ((ψ a : P) : Q) = π a := fun a => rfl
  have hψ : Function.Surjective ψ := by
    intro p
    obtain ⟨a, ha⟩ := hπ p
    exact ⟨⟨a, by rw [Subgroup.mem_comap, ha]; exact p.2⟩, Subtype.ext ha⟩
  have hcard : Nat.card ψ.ker = Nat.card π.ker :=
    Nat.card_congr
      { toFun := fun a => ⟨(a : P').1, by
          have h := a.2
          rw [MonoidHom.mem_ker] at h ⊢
          have := congrArg Subtype.val h
          simpa [hψπ] using this⟩
        invFun := fun k => ⟨⟨k.1, by
          rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp k.2]; exact P.one_mem⟩, by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext (by simpa [hψπ] using MonoidHom.mem_ker.mp k.2)⟩
        left_inv := fun a => rfl
        right_inv := fun k => rfl }
  have hidx : ψ.ker.index = Nat.card P := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top]
  have hcop' : Nat.Coprime (Nat.card ψ.ker) ψ.ker.index := by
    rw [hcard, hidx]
    exact hcop
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  let e1 : P' ⧸ ψ.ker ≃* P := QuotientGroup.quotientKerEquivOfSurjective ψ hψ
  let e2 : P' ⧸ ψ.ker ≃* K := hK.symm.QuotientMulEquiv
  refine ⟨P'.subtype.comp (K.subtype.comp (e2.toMonoidHom.comp e1.symm.toMonoidHom)), fun p => ?_⟩
  have h2 : (QuotientGroup.mk ((e2 (e1.symm p) : K) : P') : P' ⧸ ψ.ker) = e1.symm p :=
    Subgroup.IsComplement.quotientGroupMk_leftQuotientEquiv hK.symm (e1.symm p)
  have h3 : ψ ((e2 (e1.symm p) : K) : P') = p := by
    have h5 : e1 (QuotientGroup.mk ((e2 (e1.symm p) : K) : P')) = ψ ((e2 (e1.symm p) : K) : P') :=
      QuotientGroup.kerLift_mk ψ _
    rw [← h5, h2, MulEquiv.apply_symm_apply]
  have h4 : ((ψ ((e2 (e1.symm p) : K) : P') : P) : Q) = π (((e2 (e1.symm p) : K) : P') : G) :=
    hψπ _
  rw [h3] at h4
  exact h4.symm

end CFSG.ComponentClassification.CatFC.DS81
