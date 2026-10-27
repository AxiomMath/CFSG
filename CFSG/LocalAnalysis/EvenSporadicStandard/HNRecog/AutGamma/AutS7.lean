module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Classes

public section

namespace CFSG.EvenSporadicStandard.HNRecog.AutGamma

open Equiv CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type} [Group G]

theorem exists_inner_of_normalizes {S : Subgroup G} (hS : IsShapeSym 7 ↥S) {g : G}
    (hg : ∀ t ∈ S, g * t * g⁻¹ ∈ S) :
    ∃ s ∈ S, ∀ t ∈ S, g * t * g⁻¹ = s * t * s⁻¹ := by
  classical
  obtain ⟨φ⟩ := hS
  haveI : Finite ↥S := (φ.toEquiv.finite_iff).2 inferInstance
  let cH : ↥S →* ↥S :=
    { toFun := fun t => ⟨g * (t : G) * g⁻¹, hg t t.2⟩
      map_one' := Subtype.ext (by
        show g * (1 : G) * g⁻¹ = 1
        group)
      map_mul' := fun a b => Subtype.ext (by
        show g * ((a : G) * (b : G)) * g⁻¹ =
          (g * (a : G) * g⁻¹) * (g * (b : G) * g⁻¹)
        group) }
  have hcHinj : Function.Injective cH := by
    intro a b h
    apply Subtype.ext
    have h' : g * (a : G) * g⁻¹ = g * (b : G) * g⁻¹ := congrArg Subtype.val h
    exact mul_left_cancel (mul_right_cancel h')
  let c : ↥S ≃* ↥S := MulEquiv.ofBijective cH (Finite.injective_iff_bijective.mp hcHinj)
  have hc_apply : ∀ t : ↥S, (c t : G) = g * (t : G) * g⁻¹ := fun t => rfl
  let F : MulAut (Perm (Fin 7)) := φ.symm.trans (c.trans φ)
  have hF_apply : ∀ t : ↥S, F (φ t) = φ (c t) := by
    intro t
    show (φ.symm.trans (c.trans φ)) (φ t) = φ (c t)
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  let f' : MulAut (alternatingGroup (Fin 7)) :=
    MulAut.characteristic (alternatingGroup (Fin 7)) F
  obtain ⟨σ, hσ⟩ :=
    CFSG.Milestones.alternating_automorphism_permutation (n := 7) (Or.inr (by norm_num)) f'
  let f₂ : MulAut (Perm (Fin 7)) := (MulAut.conj σ)⁻¹ * F
  have hf2_apply : ∀ τ : Perm (Fin 7), f₂ τ = σ⁻¹ * F τ * σ := by
    intro τ
    have hf2_eq : f₂ = (MulAut.conj σ)⁻¹ * F := rfl
    rw [hf2_eq, MulAut.mul_apply, MulAut.conj_inv_apply]
  have hA : ∀ x ∈ alternatingGroup (Fin 7), f₂ x = x := by
    intro x hx
    have hFx : F x = σ * x * σ⁻¹ := by
      rw [← MulAut.characteristic_apply_apply_coe (alternatingGroup (Fin 7)) F ⟨x, hx⟩]
      exact hσ ⟨x, hx⟩
    rw [hf2_apply x, hFx]
    group
  have hcomm : ∀ (τ : Perm (Fin 7)) (x : Perm (Fin 7)), x ∈ alternatingGroup (Fin 7) →
      (τ⁻¹ * f₂ τ) * x = x * (τ⁻¹ * f₂ τ) := by
    intro τ x hx
    have hconj : τ * x * τ⁻¹ ∈ alternatingGroup (Fin 7) :=
      (inferInstance : (alternatingGroup (Fin 7)).Normal).conj_mem x hx τ
    have h1 : f₂ (τ * x * τ⁻¹) = τ * x * τ⁻¹ := hA _ hconj
    have h2 : f₂ (τ * x * τ⁻¹) = f₂ τ * f₂ x * (f₂ τ)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    have h3 : τ * x * τ⁻¹ = f₂ τ * x * (f₂ τ)⁻¹ := by
      rw [← h1, h2, hA x hx]
    have hx_eq : x = (τ⁻¹ * f₂ τ) * x * (τ⁻¹ * f₂ τ)⁻¹ := by
      calc x = τ⁻¹ * (τ * x * τ⁻¹) * τ := by group
        _ = τ⁻¹ * (f₂ τ * x * (f₂ τ)⁻¹) * τ := by rw [h3]
        _ = (τ⁻¹ * f₂ τ) * x * (τ⁻¹ * f₂ τ)⁻¹ := by group
    have h4 : x * (τ⁻¹ * f₂ τ) = (τ⁻¹ * f₂ τ) * x := by
      have h5 : ((τ⁻¹ * f₂ τ) * x * (τ⁻¹ * f₂ τ)⁻¹) * (τ⁻¹ * f₂ τ)
          = (τ⁻¹ * f₂ τ) * x := by group
      have h6 := congrArg (fun y : Perm (Fin 7) => y * (τ⁻¹ * f₂ τ)) hx_eq
      rwa [h5] at h6
    exact h4.symm
  have htriv : ∀ τ : Perm (Fin 7), f₂ τ = τ := by
    intro τ
    have h1 : τ⁻¹ * f₂ τ = 1 :=
      CFSG.GH74.GLS.IVK.GHInv.eq_one_of_commute_alternating (α := Fin 7)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
        (fun x hx => hcomm τ x hx)
    calc f₂ τ = τ * (τ⁻¹ * f₂ τ) := by group
      _ = τ := by rw [h1, mul_one]
  have hF : ∀ τ : Perm (Fin 7), F τ = σ * τ * σ⁻¹ := by
    intro τ
    have h2 : (MulAut.conj σ)⁻¹ (F τ) = τ := by
      rw [MulAut.conj_inv_apply, ← hf2_apply τ]
      exact htriv τ
    have h3 : F τ = (MulAut.conj σ) τ := by
      calc F τ = (MulAut.conj σ) ((MulAut.conj σ)⁻¹ (F τ)) :=
            (MulEquiv.apply_symm_apply _ _).symm
        _ = (MulAut.conj σ) τ := by rw [h2]
    simpa [MulAut.conj_apply] using h3
  refine ⟨φ.symm σ, (φ.symm σ).2, ?_⟩
  intro t ht
  let u : ↥S := ⟨t, ht⟩
  have hct : c u = φ.symm σ * u * (φ.symm σ)⁻¹ := by
    apply φ.injective
    rw [← hF_apply u, hF (φ u)]
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hcu : (c u : G) = g * t * g⁻¹ := by
    rw [hc_apply u]
  have hmain : g * t * g⁻¹ = (φ.symm σ : G) * t * (φ.symm σ : G)⁻¹ := by
    have h := congrArg Subtype.val hct
    rw [hcu] at h
    simpa [u] using h
  exact hmain

end CFSG.EvenSporadicStandard.HNRecog.AutGamma
