module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.A8CentPerm
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.IsoOn
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3

open Equiv

variable {G : Type} [Group G]

theorem aut_eq_id_or_conj_of_fix {A : Subgroup G} (e : alternatingGroup (Fin 8) ≃* ↥A)
    {s₈ : alternatingGroup (Fin 8)} (hs2 : s₈ ^ 2 = 1) (hs1 : s₈ ≠ 1) {η : G → G}
    (hη : IsIsoOn A A η)
    (hfix : ∀ g ∈ A, g * ((e s₈ : A) : G) = ((e s₈ : A) : G) * g → η g = g) :
    (∀ x ∈ A, η x = x) ∨ ∀ x ∈ A, η x = ((e s₈ : A) : G) * x * ((e s₈ : A) : G)⁻¹ := by
  classical
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)
  let φ : MulAut (alternatingGroup (Fin 8)) := (e.trans hη.toMulEquiv).trans e.symm
  have heφ : ∀ y : alternatingGroup (Fin 8),
      ((e (φ y) : A) : G) = η ((e y : A) : G) := by
    intro y
    have h : e (φ y) = hη.toMulEquiv (e y) := by simp [φ]
    rw [h]
    exact IsIsoOn.toMulEquiv_apply hη (e y)
  obtain ⟨σ, hσ⟩ := hbij.2 φ
  have hs2' : (s₈ : Perm (Fin 8)) ^ 2 = 1 := by
    simpa using congrArg (fun z : alternatingGroup (Fin 8) => (z : Perm (Fin 8))) hs2
  have hs1' : (s₈ : Perm (Fin 8)) ≠ 1 := by
    intro h
    exact hs1 (Subtype.ext (by simpa using h))
  have hσ' : ∀ g ∈ alternatingGroup (Fin 8),
      g * (s₈ : Perm (Fin 8)) = (s₈ : Perm (Fin 8)) * g → σ * g = g * σ := by
    intro g hg hgs
    let g' : alternatingGroup (Fin 8) := ⟨g, hg⟩
    have hg's : g' * s₈ = s₈ * g' := by
      apply Subtype.ext
      simpa [g'] using hgs
    have he_comm : e g' * e s₈ = e s₈ * e g' := by
      have h := congrArg e hg's
      rwa [map_mul, map_mul] at h
    have hG_comm : ((e g' : A) : G) * ((e s₈ : A) : G) =
        ((e s₈ : A) : G) * ((e g' : A) : G) := by
      simpa using congrArg (fun z : ↥A => (z : G)) he_comm
    have hφg : φ g' = g' := by
      apply e.injective
      apply Subtype.ext
      rw [heφ g']
      exact hfix ((e g' : A) : G) (e g').2 hG_comm
    have hconj : σ * g * σ⁻¹ = g := by
      have h1 : MulAut.conjNormal σ g' = g' := by rw [hσ, hφg]
      have h2 := congrArg (fun z : alternatingGroup (Fin 8) => (z : Perm (Fin 8))) h1
      simpa [g'] using h2
    exact mul_inv_eq_iff_eq_mul.mp hconj
  rcases perm_cent_alt_eight s₈.2 hs2' hs1' hσ' with hσ1 | hs_s
  · left
    intro x hx
    let gx : alternatingGroup (Fin 8) := e.symm ⟨x, hx⟩
    have hx_val : ((e gx : A) : G) = x := by simp [gx]
    have hηx : η x = ((e (φ gx) : A) : G) := by
      rw [← hx_val]
      exact (heφ gx).symm
    have hφg : φ gx = gx := by
      rw [← hσ, hσ1]
      apply Subtype.ext
      simp
    rw [hηx, hφg, hx_val]
  · right
    intro x hx
    let gx : alternatingGroup (Fin 8) := e.symm ⟨x, hx⟩
    have hx_val : ((e gx : A) : G) = x := by simp [gx]
    have hηx : η x = ((e (φ gx) : A) : G) := by
      rw [← hx_val]
      exact (heφ gx).symm
    have hconj : φ gx = s₈ * gx * s₈⁻¹ := by
      rw [← hσ, hs_s]
      apply Subtype.ext
      simp [MulAut.conjNormal_apply]
    have he_conj : e (φ gx) = e s₈ * e gx * (e s₈)⁻¹ := by
      rw [hconj, map_mul, map_mul, map_inv]
    rw [hηx, he_conj]
    simp [hx_val]

end CFSG.EvenSporadicStandard.HNRecog.Section4
