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

namespace CFSG.Quasithin

namespace B69K

@[expose] def ParabolicPair {C : Type} [Group C] (U : Subgroup C) : Prop :=
  ∃ P₀ P₁ : Subgroup C, U ≤ P₀ ∧ U ≤ P₁ ∧ P₀ ≠ ⊤ ∧ P₁ ≠ ⊤ ∧ P₀ ⊔ P₁ = ⊤ ∧
    ∀ α : MulAut C, U.map α.toMonoidHom = U →
      P₀.map α.toMonoidHom = P₀ ∧ P₁.map α.toMonoidHom = P₁

section Coatoms

variable {C : Type} [Group C] {U : Subgroup C} {Ps : Set (Subgroup C)}

theorem map_mem_of_cover (hco : ∀ P ∈ Ps, IsCoatom P ∧ U ≤ P)
    (hcov : ∀ A : Subgroup C, U ≤ A → A ≠ ⊤ → ∃ P ∈ Ps, A ≤ P)
    {α : MulAut C} (hα : U.map α.toMonoidHom = U) {P : Subgroup C} (hP : P ∈ Ps) :
    P.map α.toMonoidHom ∈ Ps := by
  obtain ⟨hc, hUP⟩ := hco P hP
  have hc' : IsCoatom (P.map α.toMonoidHom) := ((MulEquiv.mapSubgroup α).isCoatom_iff P).mpr hc
  have hU' : U ≤ P.map α.toMonoidHom := by
    rw [← hα]
    exact Subgroup.map_mono hUP
  obtain ⟨P', hP', hle⟩ := hcov _ hU' hc'.1
  have h' : P' = P.map α.toMonoidHom := (hc'.le_iff.mp hle).resolve_left (hco P' hP').1.1
  exact h' ▸ hP'

theorem index_map_aut (α : MulAut C) (P : Subgroup C) : (P.map α.toMonoidHom).index = P.index :=
  Subgroup.index_map_equiv P α

theorem map_inv_eq_of_map_eq {α : MulAut C} (hα : U.map α.toMonoidHom = U) :
    U.map α⁻¹.toMonoidHom = U := by
  conv_lhs => rw [← hα]
  rw [Subgroup.map_map]
  have : (α⁻¹.toMonoidHom).comp α.toMonoidHom = MonoidHom.id C := by
    ext x
    simp
  rw [this, Subgroup.map_id]

theorem map_sInf_eq {S : Set (Subgroup C)}
    (hS : ∀ α : MulAut C, U.map α.toMonoidHom = U → ∀ P ∈ S, P.map α.toMonoidHom ∈ S)
    {α : MulAut C} (hα : U.map α.toMonoidHom = U) :
    (sInf S).map α.toMonoidHom = sInf S := by
  have key : ∀ β : MulAut C, U.map β.toMonoidHom = U → (sInf S).map β.toMonoidHom ≤ sInf S := by
    intro β hβ x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_sInf] at hy ⊢
    intro P hP
    have hP' := hS β⁻¹ (map_inv_eq_of_map_eq hβ) P hP
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hy _ hP')
    have : β y = z := by
      rw [← hzy]
      simp
    exact this ▸ hz
  refine le_antisymm (key α hα) ?_
  intro x hx
  refine Subgroup.mem_map.mpr ⟨α⁻¹ x, key α⁻¹ (map_inv_eq_of_map_eq hα)
    (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), ?_⟩
  simp

theorem parabolicPair_of_coatoms [Finite C] (hco : ∀ P ∈ Ps, IsCoatom P ∧ U ≤ P)
    (hcov : ∀ A : Subgroup C, U ≤ A → A ≠ ⊤ → ∃ P ∈ Ps, A ≤ P)
    (hind : ∀ P ∈ Ps, ∃ g : C, g ∉ P ∧ ∀ P' ∈ Ps, P' ≠ P → g ∈ P')
    (hidx : ∃ P ∈ Ps, ∃ P' ∈ Ps, P.index ≠ P'.index) : ParabolicPair U := by
  classical
  obtain ⟨P₁, hP₁, P₂, hP₂, hne⟩ := hidx
  have hex : ∃ n, ∃ P ∈ Ps, P.index = n := ⟨P₁.index, P₁, hP₁, rfl⟩
  obtain ⟨Pm, hPm, hPmi⟩ := Nat.find_spec hex
  set m := Nat.find hex with hm
  have hmin : ∀ P ∈ Ps, m ≤ P.index := fun P hP => Nat.find_min' hex ⟨P, hP, rfl⟩
  set C₁ : Set (Subgroup C) := {P | P ∈ Ps ∧ P.index = m} with hC₁
  set C₂ : Set (Subgroup C) := {P | P ∈ Ps ∧ P.index ≠ m} with hC₂
  have hC₂ne : ∃ P ∈ C₂, True := by
    by_cases h1 : P₁.index = m
    · exact ⟨P₂, ⟨hP₂, fun h2 => hne (h1.trans h2.symm)⟩, trivial⟩
    · exact ⟨P₁, ⟨hP₁, h1⟩, trivial⟩
  obtain ⟨Pn, hPn, -⟩ := hC₂ne
  have hUle : ∀ S : Set (Subgroup C), S ⊆ Ps → U ≤ sInf S := fun S hS =>
    le_sInf fun P hP => (hco P (hS hP)).2
  have hsub₁ : C₁ ⊆ Ps := fun P hP => hP.1
  have hsub₂ : C₂ ⊆ Ps := fun P hP => hP.1
  have hne₁ : sInf C₁ ≠ ⊤ := by
    intro h
    have : sInf C₁ ≤ Pm := sInf_le ⟨hPm, hPmi⟩
    exact (hco Pm hPm).1.1 (top_le_iff.mp (h ▸ this))
  have hne₂ : sInf C₂ ≠ ⊤ := by
    intro h
    have : sInf C₂ ≤ Pn := sInf_le hPn
    exact (hco Pn hPn.1).1.1 (top_le_iff.mp (h ▸ this))
  have hcl₁ : ∀ α : MulAut C, U.map α.toMonoidHom = U → ∀ P ∈ C₁, P.map α.toMonoidHom ∈ C₁ :=
    fun α hα P hP =>
      ⟨map_mem_of_cover hco hcov hα hP.1, (index_map_aut α P).trans hP.2⟩
  have hcl₂ : ∀ α : MulAut C, U.map α.toMonoidHom = U → ∀ P ∈ C₂, P.map α.toMonoidHom ∈ C₂ :=
    fun α hα P hP =>
      ⟨map_mem_of_cover hco hcov hα hP.1, fun h => hP.2 ((index_map_aut α P).symm.trans h)⟩
  refine ⟨sInf C₁, sInf C₂, hUle _ hsub₁, hUle _ hsub₂, hne₁, hne₂, ?_,
    fun α hα => ⟨map_sInf_eq hcl₁ hα, map_sInf_eq hcl₂ hα⟩⟩
  by_contra hgen
  obtain ⟨P₀, hP₀, hle⟩ := hcov _ (le_sup_of_le_left (hUle _ hsub₁)) hgen
  obtain ⟨g, hg0, hgall⟩ := hind P₀ hP₀
  by_cases h0 : P₀.index = m
  ·
    have hg : g ∈ sInf C₂ := by
      rw [Subgroup.mem_sInf]
      intro P hP
      exact hgall P hP.1 fun h => hP.2 (h ▸ h0)
    exact hg0 (hle (Subgroup.mem_sup_right hg))
  ·
    have hg : g ∈ sInf C₁ := by
      rw [Subgroup.mem_sInf]
      intro P hP
      exact hgall P hP.1 fun h => h0 (h ▸ hP.2)
    exact hg0 (hle (Subgroup.mem_sup_left hg))

end Coatoms

end B69K

end CFSG.Quasithin
