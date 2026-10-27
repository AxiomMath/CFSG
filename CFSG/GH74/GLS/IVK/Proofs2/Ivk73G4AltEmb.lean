module

public import CFSG.Milestones.AT_alternating_automorphism_permutation
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltCent

public section

namespace CFSG.GH74.GLS.IVK

open Equiv Equiv.Perm CFSG.GH74.GLS.IVK.GHInv

section Emb

variable {N : Type*} [Group N] {L : Subgroup N} [L.Normal] {n : ℕ}

theorem exists_perm_embedding (hn : 7 ≤ n)
    (hcent : ∀ x : N, (∀ l ∈ L, x * l = l * x) → x = 1)
    (e : ↥L ≃* alternatingGroup (Fin n)) :
    ∃ ι : N →* Perm (Fin n), Function.Injective ι ∧
      ∀ l : ↥L, ι (l : N) = ((e l : alternatingGroup (Fin n)) : Perm (Fin n)) := by
  classical
  let φ : N → MulAut (alternatingGroup (Fin n)) := fun x =>
    e.symm.trans ((MulAut.conjNormal x).trans e)
  have hex : ∀ x : N, ∃ σ : Perm (Fin n), ∀ g : alternatingGroup (Fin n),
      ((φ x g : alternatingGroup (Fin n)) : Perm (Fin n)) = σ * (g : Perm (Fin n)) * σ⁻¹ :=
    fun x => CFSG.Milestones.alternating_automorphism_permutation (Or.inr hn) (φ x)
  choose σ hσ using hex
  have huniq : ∀ s t : Perm (Fin n), (∀ g : alternatingGroup (Fin n),
      s * (g : Perm (Fin n)) * s⁻¹ = t * (g : Perm (Fin n)) * t⁻¹) → s = t := by
    intro s t h
    have hu : s⁻¹ * t = 1 := by
      refine eq_one_of_commute_alternating (α := Fin n)
        (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega) (fun g hg => ?_)
      have := h ⟨g, hg⟩
      simp only at this
      calc s⁻¹ * t * g = s⁻¹ * (t * g * t⁻¹) * t := by group
        _ = s⁻¹ * (s * g * s⁻¹) * t := by rw [this]
        _ = g * (s⁻¹ * t) := by group
    exact inv_mul_eq_one.1 hu
  have hmul : ∀ x y : N, σ (x * y) = σ x * σ y := by
    intro x y
    apply huniq
    intro g
    have h2 : φ (x * y) g = φ x (φ y g) := by
      simp [φ, map_mul]
    have h3 := hσ (x * y) g
    rw [h2, hσ x (φ y g), hσ y g] at h3
    rw [← h3]
    simp [mul_assoc]
  refine ⟨MonoidHom.mk' σ hmul, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    apply hcent x
    intro l hl
    have hx1 : σ x = 1 := hx
    have h1 := hσ x (e ⟨l, hl⟩)
    rw [hx1] at h1
    simp only [inv_one, one_mul, mul_one] at h1
    have h2 : (φ x (e ⟨l, hl⟩) : alternatingGroup (Fin n)) = e ⟨l, hl⟩ := Subtype.ext h1
    have h3 : ((MulAut.conjNormal x ⟨l, hl⟩ : ↥L) : N) = l := by
      have := congrArg (fun a => (e.symm a : N)) h2
      simpa [φ] using this
    rw [MulAut.conjNormal_apply] at h3
    calc x * l = x * l * x⁻¹ * x := by group
      _ = l * x := by rw [h3]
  · intro l
    show σ (l : N) = _
    apply huniq
    intro g
    rw [← hσ (l : N) g]
    have h4 : (e ((MulAut.conjNormal (l : N)) (e.symm g)) : alternatingGroup (Fin n)) =
        e l * g * (e l)⁻¹ := by
      rw [MulAut.conjNormal_val, MulAut.conj_apply, map_mul, map_mul, map_inv,
        MulEquiv.apply_symm_apply]
    simp only [φ, MulEquiv.trans_apply, h4]
    simp

end Emb

end CFSG.GH74.GLS.IVK
