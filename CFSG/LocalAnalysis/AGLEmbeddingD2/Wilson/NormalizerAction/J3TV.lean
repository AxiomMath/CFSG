module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res3ProofJ3K

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.Asc83Table Subgroup
open scoped Matrix

theorem tv_necessary {L : Type*} [Group L] {n : ℕ} {B : Subgroup L}
    (f : Multiplicative (Fin n → ZMod 3) ≃* B) (g : normalizer (B : Set L))
    (hT : IsTransvectionOn (normalizerMonoidHom B g)) :
    (∀ v, (conjMat f g - 1) *ᵥ ((conjMat f g - 1) *ᵥ v) = 0) ∧
      ∃ v, (conjMat f g - 1) *ᵥ v ≠ 0 := by
  set φ : MulAut B := normalizerMonoidHom B g with hφ
  set ψ : MulAut (Multiplicative (Fin n → ZMod 3)) := f.trans (φ.trans f.symm) with hψ
  have hψT : IsTransvectionOn ψ :=
    Item2113Res3Proof.isTransvectionOn_of_bijective f.symm.toMonoidHom f.symm.bijective
      (fun a => by simp [hψ] <;> rfl) hT
  set A := conjAdd f g with hA
  have hψv : ∀ v, ψ (Multiplicative.ofAdd v) = Multiplicative.ofAdd (A v) := by
    intro v
    rw [hA, conjAdd_apply, ofAdd_toAdd]
    simp [hψ] <;> rfl
  have hMA : ∀ v, conjMat f g *ᵥ v = A v := by
    intro v
    rw [conjMat, LinearMap.toMatrix'_mulVec]
    rfl
  have hN : ∀ v, (conjMat f g - 1) *ᵥ v = A v - v := by
    intro v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hMA]
  have hcomm : ∀ v, (Multiplicative.ofAdd v)⁻¹ * ψ (Multiplicative.ofAdd v) ∈ commOf ψ :=
    fun v => Subgroup.subset_closure ⟨Multiplicative.ofAdd v, rfl⟩
  have hexp : ∀ v, (Multiplicative.ofAdd v)⁻¹ * ψ (Multiplicative.ofAdd v) =
      Multiplicative.ofAdd (A v - v) := by
    intro v
    rw [hψv, ← ofAdd_neg, ← ofAdd_add]
    congr 1
    abel
  refine ⟨fun v => ?_, ?_⟩
  · have hfix := (mem_fixedSubgroupOf ψ _).1 (hψT.2 (hcomm v))
    rw [hexp, hψv] at hfix
    have h1 : A (A v - v) = A v - v := Multiplicative.ofAdd.injective hfix
    rw [hN, hN, h1, sub_self]
  · by_contra hall
    push Not at hall
    have h1 : ∀ a : Multiplicative (Fin n → ZMod 3), a⁻¹ * ψ a = 1 := by
      intro a
      have h2 := hexp (Multiplicative.toAdd a)
      rw [ofAdd_toAdd] at h2
      rw [h2]
      have := hall (Multiplicative.toAdd a)
      rw [hN, sub_eq_zero] at this
      rw [this, sub_self]
      rfl
    have hbot : commOf ψ = ⊥ := by
      rw [commOf, eq_bot_iff, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      show a⁻¹ * ψ a ∈ (⊥ : Subgroup _)
      rw [h1 a]
      exact one_mem _
    have := hψT.1
    rw [hbot, Subgroup.card_bot] at this
    omega

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
