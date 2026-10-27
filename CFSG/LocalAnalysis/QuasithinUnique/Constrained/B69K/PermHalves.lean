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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

namespace CFSG.Quasithin.B69K

open Equiv Equiv.Perm

lemma evenb_inv_apply_self {m : ℕ} (f : Perm (Fin m)) (x : Fin m) : f⁻¹ (f x) = x := by
  rw [Equiv.Perm.inv_def]
  exact f.symm_apply_apply x

lemma evenb_apply_inv_self {m : ℕ} (f : Perm (Fin m)) (x : Fin m) : f (f⁻¹ x) = x := by
  rw [Equiv.Perm.inv_def]
  exact f.apply_symm_apply x

lemma evenb_inv_mul_mem_of_index_two {G : Type*} [Group G] {K : Subgroup G}
    (hK : K.index = 2) {g τ : G} (hg : g ∉ K) (hτ : τ ∉ K) : g⁻¹ * τ ∈ K := by
  obtain ⟨a, -, hab⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.1 hK
  have h1 : a * g ∈ K := (hab g).resolve_right hg
  have h2 : a * τ ∈ K := (hab τ).resolve_right hτ
  have h3 := K.mul_mem (K.inv_mem h1) h2
  have e : (a * g)⁻¹ * (a * τ) = g⁻¹ * τ := by group
  rwa [e] at h3

theorem exists_invariant_halves {m : ℕ} (hm : 2 ≤ m) (T' : Subgroup (Perm (Fin m)))
    (hT' : IsPGroup 2 T') (htrans : ∀ x y : Fin m, ∃ τ ∈ T', τ x = y) :
    ∃ B : Set (Fin m), 2 * B.ncard = m ∧
      ∀ τ ∈ T', ((τ : Perm (Fin m)) '' B = B ∨ (τ : Perm (Fin m)) '' B = Bᶜ) := by
  obtain ⟨x₀, y₁, hne⟩ : ∃ x₀ y₁ : Fin m, x₀ ≠ y₁ :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp [Fin.ext_iff]⟩
  haveI : Finite ↥T' := inferInstance
  haveI : Group.IsNilpotent ↥T' := IsPGroup.isNilpotent hT'
  haveI : Finite (Subgroup ↥T') :=
    Finite.of_injective (fun H : Subgroup ↥T' => (H : Set ↥T')) SetLike.coe_injective
  haveI : IsCoatomic (Subgroup ↥T') := Finite.to_isCoatomic
  have hstab_ne_top : MulAction.stabilizer ↥T' x₀ ≠ ⊤ := by
    intro htop
    obtain ⟨τ, hτ, hτx⟩ := htrans x₀ y₁
    have hmem : (⟨τ, hτ⟩ : ↥T') ∈ MulAction.stabilizer ↥T' x₀ := by
      rw [htop]
      exact Subgroup.mem_top _
    have hfix : τ x₀ = x₀ := MulAction.mem_stabilizer_iff.1 hmem
    exact hne (hfix.symm.trans hτx)
  obtain ⟨K, hKc, hstabK⟩ : ∃ K : Subgroup ↥T', IsCoatom K ∧ MulAction.stabilizer ↥T' x₀ ≤ K :=
    (eq_top_or_exists_le_coatom (MulAction.stabilizer ↥T' x₀)).resolve_left hstab_ne_top
  have hKidx : K.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hT').1 hKc
  have hstab : ∀ h : ↥T', (h : Perm (Fin m)) x₀ = x₀ → h ∈ K := fun h hh =>
    hstabK (MulAction.mem_stabilizer_iff.2 hh)
  obtain ⟨B, hB⟩ : ∃ B : Set (Fin m),
      ∀ y, y ∈ B ↔ ∃ k : ↥T', k ∈ K ∧ (k : Perm (Fin m)) x₀ = y :=
    ⟨{y | ∃ k : ↥T', k ∈ K ∧ (k : Perm (Fin m)) x₀ = y}, fun y => Iff.rfl⟩
  have memB : ∀ τ : ↥T', (τ : Perm (Fin m)) x₀ ∈ B ↔ τ ∈ K := by
    intro τ
    rw [hB]
    constructor
    · rintro ⟨k, hk, hkx⟩
      have hkτ : k⁻¹ * τ ∈ K := by
        apply hstab
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, ← hkx,
          evenb_inv_apply_self]
      have h := K.mul_mem hk hkτ
      rwa [mul_inv_cancel_left] at h
    · intro hτ
      exact ⟨τ, hτ, rfl⟩
  have memImage : ∀ σ τ : ↥T',
      (τ : Perm (Fin m)) x₀ ∈ (σ : Perm (Fin m)) '' B ↔ σ⁻¹ * τ ∈ K := by
    intro σ τ
    constructor
    · rintro ⟨z, hz, hzτ⟩
      have hz' : z = ((σ⁻¹ * τ : ↥T') : Perm (Fin m)) x₀ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, ← hzτ,
          evenb_inv_apply_self]
      rw [hz'] at hz
      exact (memB _).1 hz
    · intro hστ
      refine ⟨((σ⁻¹ * τ : ↥T') : Perm (Fin m)) x₀, (memB _).2 hστ, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply, evenb_apply_inv_self]
  have hsetK : ∀ σ : ↥T', σ ∈ K → (σ : Perm (Fin m)) '' B = B := by
    intro σ hσ
    ext y
    obtain ⟨τ, hτT, rfl⟩ := htrans x₀ y
    have key : σ⁻¹ * (⟨τ, hτT⟩ : ↥T') ∈ K ↔ (⟨τ, hτT⟩ : ↥T') ∈ K := by
      constructor
      · intro h
        have h' := K.mul_mem hσ h
        rwa [mul_inv_cancel_left] at h'
      · intro h
        exact K.mul_mem (K.inv_mem hσ) h
    exact (memImage σ ⟨τ, hτT⟩).trans (key.trans (memB ⟨τ, hτT⟩).symm)
  have hsetc : ∀ σ : ↥T', σ ∉ K → (σ : Perm (Fin m)) '' B = Bᶜ := by
    intro σ hσ
    ext y
    obtain ⟨τ, hτT, rfl⟩ := htrans x₀ y
    have key : σ⁻¹ * (⟨τ, hτT⟩ : ↥T') ∈ K ↔ (⟨τ, hτT⟩ : ↥T') ∉ K := by
      constructor
      · intro h hτK
        apply hσ
        have h' := K.mul_mem hτK (K.inv_mem h)
        simpa using h'
      · intro h
        exact evenb_inv_mul_mem_of_index_two hKidx hσ h
    rw [Set.mem_compl_iff]
    exact (memImage σ ⟨τ, hτT⟩).trans (key.trans (not_congr (memB ⟨τ, hτT⟩)).symm)
  obtain ⟨a, haK, -⟩ := Subgroup.index_eq_two_iff_exists_notMem_and'.1 hKidx
  have hcard : 2 * B.ncard = m := by
    have h1 : ((a : Perm (Fin m)) '' B).ncard = B.ncard :=
      Set.ncard_image_of_injective B (Equiv.injective (a : Perm (Fin m)))
    rw [hsetc a haK] at h1
    have h2 := Set.ncard_add_ncard_compl B
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at h2
    omega
  refine ⟨B, hcard, fun τ hτ => ?_⟩
  by_cases hτK : (⟨τ, hτ⟩ : ↥T') ∈ K
  · exact Or.inl (hsetK ⟨τ, hτ⟩ hτK)
  · exact Or.inr (hsetc ⟨τ, hτ⟩ hτK)

end CFSG.Quasithin.B69K
