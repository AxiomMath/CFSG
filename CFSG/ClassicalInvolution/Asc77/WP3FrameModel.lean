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

namespace CFSG.ClassicalInvolution.Asc77

section ChainPair

variable {K K' : Type*} [Group K] [Group K']

structure ChainPairData (𝓕 : Set (Subgroup K)) (R₁ R₂ : Subgroup K) (τ₁ τ₂ ν₁ ν₂ : K) : Prop where
  mem₁ : τ₁ ∈ R₁
  mem₂ : τ₂ ∈ R₂
  center₁ : ∀ c ∈ R₁, (∀ r ∈ R₁, c * r = r * c) → c = 1 ∨ c = τ₁
  center₂ : ∀ c ∈ R₂, (∀ r ∈ R₂, c * r = r * c) → c = 1 ∨ c = τ₂
  sq₁ : τ₁ * τ₁ = 1
  sq₂ : τ₂ * τ₂ = 1
  comm : τ₁ * τ₂ = τ₂ * τ₁
  prod_not_central : τ₁ * τ₂ ∉ Subgroup.center K
  not_central : ∃ r ∈ R₂, τ₁ * r * τ₁⁻¹ * r⁻¹ ∉ Subgroup.center K
  swap₁ : ν₁ * τ₁ * ν₁⁻¹ = τ₂
  swap₁' : ν₁ * τ₂ * ν₁⁻¹ = τ₁
  swap₂ : ν₂ * τ₁ * ν₂⁻¹ = τ₁ * τ₂
  swap₂' : ν₂ * τ₂ * ν₂⁻¹ = τ₂
  gen : (⊤ : Subgroup K) ≤ ⨆ R ∈ 𝓕,
    ⨆ (_ : R ≤ Subgroup.centralizer ({τ₁} : Set K) ∨ R ≤ Subgroup.centralizer ({τ₂} : Set K) ∨
      R ≤ Subgroup.centralizer ({τ₁ * τ₂} : Set K)), R

@[expose] def ChainPair (𝓕 : Set (Subgroup K)) : Prop :=
  ∃ R₁ ∈ 𝓕, ∃ R₂ ∈ 𝓕, ∃ τ₁ τ₂ ν₁ ν₂ : K, ChainPairData 𝓕 R₁ R₂ τ₁ τ₂ ν₁ ν₂

theorem ChainPairData.map {𝓕 : Set (Subgroup K)} {𝓕' : Set (Subgroup K')} (e : K ≃* K')
    (he : ∀ R : Subgroup K, R ∈ 𝓕 ↔ R.map e.toMonoidHom ∈ 𝓕') {R₁ R₂ : Subgroup K}
    {τ₁ τ₂ ν₁ ν₂ : K} (h : ChainPairData 𝓕 R₁ R₂ τ₁ τ₂ ν₁ ν₂) :
    ChainPairData 𝓕' (R₁.map e.toMonoidHom) (R₂.map e.toMonoidHom) (e τ₁) (e τ₂) (e ν₁) (e ν₂) := by
  have hcenter : ∀ x : K, x ∈ Subgroup.center K ↔ e x ∈ Subgroup.center K' := fun x => by
    simp only [Subgroup.mem_center_iff]
    constructor
    · intro hx y
      have := hx (e.symm y)
      simpa using congrArg e this
    · intro hx y
      exact e.injective (by simpa using hx (e y))
  have hmapmem : ∀ (R : Subgroup K) (x : K), x ∈ R ↔ e x ∈ R.map e.toMonoidHom := fun R x => by
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      rw [← e.injective hyx]
      exact hy
  have hcent : ∀ (R : Subgroup K) (a : K), R ≤ Subgroup.centralizer ({a} : Set K) →
      R.map e.toMonoidHom ≤ Subgroup.centralizer ({e a} : Set K') := by
    rintro R a hRa _ ⟨r, hr, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := Subgroup.mem_centralizer_singleton_iff.mp (hRa hr)
    simpa using congrArg e this
  refine ⟨(hmapmem R₁ τ₁).mp h.mem₁, (hmapmem R₂ τ₂).mp h.mem₂, ?_, ?_,
    by rw [← map_mul, h.sq₁, map_one], by rw [← map_mul, h.sq₂, map_one],
    by rw [← map_mul, ← map_mul, h.comm],
    fun hx => h.prod_not_central ((hcenter (τ₁ * τ₂)).mpr (by rwa [map_mul])), ?_, ?_, ?_, ?_, ?_,
    ?_⟩
  · rintro _ ⟨c, hc, rfl⟩ hcc
    have hcc' : ∀ r ∈ R₁, c * r = r * c := fun r hr' => e.injective (by
      rw [map_mul, map_mul]
      exact hcc _ ⟨r, hr', rfl⟩)
    rcases h.center₁ c hc hcc' with rfl | rfl
    · exact Or.inl (map_one e)
    · exact Or.inr rfl
  · rintro _ ⟨c, hc, rfl⟩ hcc
    have hcc' : ∀ r ∈ R₂, c * r = r * c := fun r hr' => e.injective (by
      rw [map_mul, map_mul]
      exact hcc _ ⟨r, hr', rfl⟩)
    rcases h.center₂ c hc hcc' with rfl | rfl
    · exact Or.inl (map_one e)
    · exact Or.inr rfl
  · obtain ⟨r, hr', hrc⟩ := h.not_central
    refine ⟨e r, (hmapmem R₂ r).mp hr', fun hx => hrc ((hcenter _).mpr ?_)⟩
    simpa [map_mul, map_inv] using hx
  · simpa [map_mul, map_inv] using congrArg e h.swap₁
  · simpa [map_mul, map_inv] using congrArg e h.swap₁'
  · simpa [map_mul, map_inv] using congrArg e h.swap₂
  · simpa [map_mul, map_inv] using congrArg e h.swap₂'
  · intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    have hx := h.gen (Subgroup.mem_top x)
    have hmem : e x ∈ (⨆ R ∈ 𝓕, ⨆ (_ : R ≤ Subgroup.centralizer ({τ₁} : Set K) ∨
        R ≤ Subgroup.centralizer ({τ₂} : Set K) ∨
        R ≤ Subgroup.centralizer ({τ₁ * τ₂} : Set K)), R).map e.toMonoidHom := ⟨x, hx, rfl⟩
    refine (?_ : _ ≤ ⨆ R' ∈ 𝓕', ⨆ (_ : R' ≤ Subgroup.centralizer ({e τ₁} : Set K') ∨
        R' ≤ Subgroup.centralizer ({e τ₂} : Set K') ∨
        R' ≤ Subgroup.centralizer ({e τ₁ * e τ₂} : Set K')), R') hmem
    simp only [Subgroup.map_iSup]
    refine iSup_le fun R => iSup_le fun hR => iSup_le fun hcond => ?_
    refine le_iSup₂_of_le (R.map e.toMonoidHom) ((he R).mp hR) (le_iSup_of_le ?_ le_rfl)
    rcases hcond with h' | h' | h'
    · exact Or.inl (hcent R τ₁ h')
    · exact Or.inr (Or.inl (hcent R τ₂ h'))
    · exact Or.inr (Or.inr (by rw [← map_mul]; exact hcent R (τ₁ * τ₂) h'))

theorem ChainPair.of_mulEquiv {𝓕 : Set (Subgroup K)} {𝓕' : Set (Subgroup K')} (e : K ≃* K')
    (he : ∀ R : Subgroup K, R ∈ 𝓕 ↔ R.map e.toMonoidHom ∈ 𝓕') (h : ChainPair 𝓕) :
    ChainPair 𝓕' := by
  obtain ⟨R₁, hR₁, R₂, hR₂, τ₁, τ₂, ν₁, ν₂, hd⟩ := h
  exact ⟨R₁.map e.toMonoidHom, (he R₁).mp hR₁, R₂.map e.toMonoidHom, (he R₂).mp hR₂, e τ₁, e τ₂,
    e ν₁, e ν₂, hd.map e he⟩

end ChainPair

end CFSG.ClassicalInvolution.Asc77
