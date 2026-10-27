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
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
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

namespace CFSG.OddStandard.AltNoHe

open Subgroup Equiv Equiv.Perm

section Quasisimple

variable {L A : Type*} [Group L] [Group A]

theorem ker_eq_top_of_forall_comm (hperf : commutator L = ⊤) (φ : L →* A)
    (h : ∀ a b : L, φ a * φ b = φ b * φ a) : φ.ker = ⊤ := by
  rw [eq_top_iff, ← hperf, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def, h a b]
  simp

theorem center_eq_ker_of_surjective (hperf : commutator L = ⊤)
    [hs : IsSimpleGroup (L ⧸ center L)] [hA : IsSimpleGroup A]
    (φ : L →* A) (hφ : Function.Surjective φ) : center L = φ.ker := by
  have hker_ne : φ.ker ≠ ⊤ := by
    intro h
    obtain ⟨a, b, hab⟩ := exists_pair_ne A
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    exact hab ((MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x)).trans
      (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top y)).symm)
  have hZ : center L ≤ φ.ker := by
    have hnorm : ((center L).map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
    have := hnorm
    rcases hA.eq_bot_or_eq_top_of_normal ((center L).map φ) with hbot | htop
    · exact (Subgroup.map_eq_bot_iff _).1 hbot
    · exfalso
      refine hker_ne (ker_eq_top_of_forall_comm hperf φ fun a b => ?_)
      have ha : φ a ∈ (center L).map φ := htop ▸ Subgroup.mem_top _
      obtain ⟨z, hz, hza⟩ := ha
      rw [← hza, ← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz b]
  refine le_antisymm hZ ?_
  have hnorm : (φ.ker.map (QuotientGroup.mk' (center L))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  have := hnorm
  rcases hs.eq_bot_or_eq_top_of_normal (φ.ker.map (QuotientGroup.mk' (center L))) with hbot | htop
  · simpa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hbot
  · exfalso
    refine hker_ne (eq_top_iff.2 fun l _ => ?_)
    have hl : QuotientGroup.mk' (center L) l ∈ φ.ker.map (QuotientGroup.mk' (center L)) :=
      htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkl⟩ := hl
    have : k⁻¹ * l ∈ center L := by
      rw [← QuotientGroup.ker_mk' (center L), MonoidHom.mem_ker, map_mul, map_inv, hkl,
        inv_mul_cancel]
    have := hZ this
    simpa using φ.ker.mul_mem hk this

theorem mulEquiv_of_surjective (hperf : commutator L = ⊤)
    [hs : IsSimpleGroup (L ⧸ center L)] [hA : IsSimpleGroup A]
    (φ : L →* A) (hφ : Function.Surjective φ) : Nonempty ((L ⧸ center L) ≃* A) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_eq_ker_of_surjective hperf φ hφ)).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

end Quasisimple

section PermImage

variable {L : Type*} [Group L] {X : Type*} [Fintype X] [DecidableEq X]

theorem five_le_card_and_range_eq (hperf : commutator L = ⊤) (π : L →* Perm X)
    (hnorm : π.range.Normal) (hne : π.range ≠ ⊥) :
    5 ≤ Nat.card X ∧ π.range = alternatingGroup X := by
  have hQ : π.range = ⁅π.range, π.range⁆ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hperf]
  have h5 : 5 ≤ Nat.card X := by
    by_contra h
    have := Equiv.Perm.isSolvable (α := X) (by omega)
    exact (Group.IsSolvable.commutator_lt_of_ne_bot hne).ne hQ.symm
  refine ⟨h5, le_antisymm ?_ ?_⟩
  · rw [hQ]
    exact (Subgroup.commutator_mono le_top le_top).trans
      (by rw [← commutator_def]; exact alternatingGroup.commutator_perm_le)
  · have : Nontrivial π.range := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    exact Equiv.Perm.alternatingGroup_le_of_normal h5 this

theorem card_ge_five_and_mulEquiv_alternatingGroup (hperf : commutator L = ⊤)
    [hs : IsSimpleGroup (L ⧸ center L)] (π : L →* Perm X)
    (hnorm : π.range.Normal) (hne : π.range ≠ ⊥) :
    5 ≤ Nat.card X ∧ Nonempty ((L ⧸ center L) ≃* alternatingGroup X) := by
  obtain ⟨h5, hrange⟩ := five_le_card_and_range_eq hperf π hnorm hne
  have := alternatingGroup.isSimpleGroup h5
  let φ : L →* alternatingGroup X :=
    π.codRestrict (alternatingGroup X) fun l => by rw [← hrange]; exact ⟨l, rfl⟩
  have hφ : Function.Surjective φ := fun a => by
    have ha : (a : Perm X) ∈ π.range := by rw [hrange]; exact a.2
    obtain ⟨l, hl⟩ := ha
    exact ⟨l, Subtype.ext hl⟩
  exact ⟨h5, mulEquiv_of_surjective hperf φ hφ⟩

end PermImage

section TwoImages

variable {L : Type*} [Group L] {X₁ X₂ : Type*} [Fintype X₁] [DecidableEq X₁] [Fintype X₂]
  [DecidableEq X₂]

theorem exists_card_ge_five_and_mulEquiv_alternatingGroup (hperf : commutator L = ⊤)
    [hs : IsSimpleGroup (L ⧸ center L)] (π₁ : L →* Perm X₁) (π₂ : L →* Perm X₂)
    (hn₁ : π₁.range.Normal) (hn₂ : π₂.range.Normal)
    (hcomm : ∀ a b : L, π₁ a = 1 → π₂ a = 1 → π₁ b = 1 → π₂ b = 1 → a * b = b * a) :
    (5 ≤ Nat.card X₁ ∧ Nonempty ((L ⧸ center L) ≃* alternatingGroup X₁)) ∨
      (5 ≤ Nat.card X₂ ∧ Nonempty ((L ⧸ center L) ≃* alternatingGroup X₂)) := by
  by_cases h₁ : π₁.range = ⊥
  · by_cases h₂ : π₂.range = ⊥
    · exfalso
      have e₁ : ∀ a, π₁ a = 1 := fun a => by
        have : π₁ a ∈ π₁.range := ⟨a, rfl⟩
        rw [h₁] at this
        exact this
      have e₂ : ∀ a, π₂ a = 1 := fun a => by
        have : π₂ a ∈ π₂.range := ⟨a, rfl⟩
        rw [h₂] at this
        exact this
      have hab : ∀ a b : L, a * b = b * a := fun a b => hcomm a b (e₁ a) (e₂ a) (e₁ b) (e₂ b)
      have hker := ker_eq_top_of_forall_comm hperf (MonoidHom.id L) hab
      have h1 : ∀ l : L, l = 1 := fun l => MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_top l)
      obtain ⟨x, y, hxy⟩ := exists_pair_ne (L ⧸ center L)
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      exact hxy (by rw [h1 a, h1 b])
    · exact .inr (card_ge_five_and_mulEquiv_alternatingGroup hperf π₂ hn₂ h₂)
  · exact .inl (card_ge_five_and_mulEquiv_alternatingGroup hperf π₁ hn₁ h₁)

end TwoImages

theorem exists_mulEquiv_alternatingGroup_fin {L : Type*} [Group L] {X : Type*} [Fintype X]
    [DecidableEq X] (h5 : 5 ≤ Nat.card X) (f : L ≃* alternatingGroup X) :
    ∃ m : ℕ, 5 ≤ m ∧ Nonempty (L ≃* alternatingGroup (Fin m)) :=
  ⟨Fintype.card X, by rwa [← Nat.card_eq_fintype_card],
    ⟨f.trans (Equiv.altCongrHom (Fintype.equivFin X))⟩⟩

end CFSG.OddStandard.AltNoHe
