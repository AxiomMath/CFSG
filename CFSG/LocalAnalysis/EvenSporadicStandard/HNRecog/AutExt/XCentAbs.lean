module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XAutDefs
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.DerivedOf

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Subgroup CFSG.EvenSporadicStandard.HNRecog.Section3

theorem xAutCent_of_data {X : Type*} [Group X] {A T : X} (hM1 : XAutInner X A)
    (hAT : A * T = T * A)
    (hii : ∀ g : X, (∀ x ∈ commutator X, x * T = T * x → g * x = x * g) →
      ∃ z₀ ∈ commutator X, (∀ x ∈ commutator X, z₀ * x = x * z₀) ∧ (g = z₀ ∨ g = z₀ * T))
    (ha1 : ∀ y : X, ∃ n ∈ commutator X, ∃ c : X, c * T = T * c ∧ y = n * c) :
    XAutCent X T := by
  intro σ hfix
  obtain ⟨g, hg⟩ := hM1 σ (hfix A hAT)
  have hgcent : ∀ x ∈ commutator X, x * T = T * x → g * x = x * g := by
    intro x hx hxT
    have h2 : g * x * g⁻¹ = x := by rw [← hg x hx, hfix x hxT]
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [h2]
  obtain ⟨z₀, hz₀mem, hz₀cent, hgz⟩ := hii g hgcent
  rcases hgz with hg_eq | hg_eq
  · subst g
    left
    intro y
    obtain ⟨n, hn, c, hcT, rfl⟩ := ha1 y
    have hσn : σ n = n := by
      rw [hg n hn, hz₀cent n hn]
      group
    rw [map_mul, hσn, hfix c hcT]
  · subst g
    right
    intro y
    obtain ⟨n, hn, c, hcT, rfl⟩ := ha1 y
    have hTn : T * n * T⁻¹ ∈ commutator X :=
      (inferInstance : (commutator X).Normal).conj_mem n hn T
    have hσn : σ n = T * n * T⁻¹ := by
      rw [hg n hn,
        show (z₀ * T) * n * (z₀ * T)⁻¹ = z₀ * (T * n * T⁻¹) * z₀⁻¹ by group,
        hz₀cent (T * n * T⁻¹) hTn]
      group
    have hTc : T * c * T⁻¹ = c := by rw [← hcT]; group
    have hc' : c * T⁻¹ = T⁻¹ * c := by
      have h := congrArg (fun u => T⁻¹ * u) hTc
      simpa only [← mul_assoc, inv_mul_cancel, one_mul] using h
    rw [map_mul, hσn, hfix c hcT]
    rw [show T * (n * c) * T⁻¹ = T * n * T⁻¹ * c by
      rw [← mul_assoc T n c, mul_assoc (T * n) c T⁻¹, hc', ← mul_assoc (T * n) T⁻¹ c]]

theorem xAutCent_of_ambient {Γ : Type} [Group Γ] (X : Subgroup Γ) {A T : Γ} (hA : A ∈ X)
    (hT : T ∈ X) (hM1 : XAutInner ↥X ⟨A, hA⟩) (hAT : A * T = T * A)
    (hii : ∀ g ∈ X, (∀ x ∈ derivedOf X, x * T = T * x → g * x = x * g) →
      ∃ z₀ ∈ derivedOf X, (∀ x ∈ derivedOf X, z₀ * x = x * z₀) ∧ (g = z₀ ∨ g = z₀ * T))
    (ha1 : ∀ y ∈ X, ∃ n ∈ derivedOf X, ∃ c ∈ X, c * T = T * c ∧ y = n * c) :
    XAutCent ↥X ⟨T, hT⟩ := by
  refine xAutCent_of_data (X := ↥X) (A := ⟨A, hA⟩) (T := ⟨T, hT⟩) hM1 ?_ ?_ ?_
  · exact Subtype.ext (by simpa using hAT)
  · intro g hgc
    have hgamb : ∀ x ∈ derivedOf X, x * T = T * x → (g : Γ) * x = x * g := by
      intro x hx hxT
      have hxX : x ∈ X := derivedOf_le X hx
      have hmem : (⟨x, hxX⟩ : ↥X) ∈ commutator ↥X := (mem_derivedOf_iff.mp hx).2
      have hxT' : (⟨x, hxX⟩ : ↥X) * ⟨T, hT⟩ = ⟨T, hT⟩ * ⟨x, hxX⟩ :=
        Subtype.ext (by simpa using hxT)
      simpa using Subtype.ext_iff.mp (hgc ⟨x, hxX⟩ hmem hxT')
    obtain ⟨z₀, hz₀mem, hz₀cent, hgz⟩ := hii g g.2 hgamb
    obtain ⟨hzd, hzc⟩ := mem_derivedOf_iff.mp hz₀mem
    refine ⟨⟨z₀, hzd⟩, hzc, ?_, ?_⟩
    · intro x hx
      exact Subtype.ext (by simpa using hz₀cent x (mem_derivedOf_iff.mpr ⟨x.2, hx⟩))
    · rcases hgz with h | h
      · left
        exact Subtype.ext h
      · right
        exact Subtype.ext (by simpa using h)
  · intro y
    obtain ⟨n, hn, c, hcX, hcT, hy⟩ := ha1 y y.2
    obtain ⟨hnd, hnc⟩ := mem_derivedOf_iff.mp hn
    exact ⟨⟨n, hnd⟩, hnc, ⟨c, hcX⟩, Subtype.ext (by simpa using hcT),
      Subtype.ext (by simpa using hy)⟩

end CFSG.EvenSporadicStandard.HNRecog.Section4
