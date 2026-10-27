module

public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Quasithin.SteinbergCB

variable {G : Type*} [Group G] {B : Subgroup G} {n : ℕ}

noncomputable def conjPermEquiv (hn : n = 5 ∨ 7 ≤ n) :
    Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
  MulEquiv.ofBijective (conjPerm n)
    ⟨conjPerm_injective (by omega), conjPerm_surjective hn⟩

noncomputable def actPerm (ψ : B ≃* alternatingGroup (Fin n)) (hn : n = 5 ∨ 7 ≤ n) :
    normalizer (B : Set G) →* Perm (Fin n) :=
  ((conjPermEquiv hn).symm.toMonoidHom.comp (MulAut.congr ψ).toMonoidHom).comp
    B.normalizerMonoidHom

theorem actPerm_spec (ψ : B ≃* alternatingGroup (Fin n)) (hn : n = 5 ∨ 7 ≤ n)
    (y : normalizer (B : Set G)) (b : B) :
    ((ψ ⟨(y : G) * b * (y : G)⁻¹, (mem_normalizer_iff.mp y.2 b).mp b.2⟩ :
        alternatingGroup (Fin n)) : Perm (Fin n)) =
      actPerm ψ hn y * (ψ b : Perm (Fin n)) * (actPerm ψ hn y)⁻¹ := by
  have h := conjPerm_apply n (actPerm ψ hn y) (ψ b)
  have h2 : conjPerm n (actPerm ψ hn y) = MulAut.congr ψ (B.normalizerMonoidHom y) := by
    show conjPermEquiv hn ((conjPermEquiv hn).symm _) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  rw [h2] at h
  rw [← h]
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

theorem actPerm_eq_one_iff (ψ : B ≃* alternatingGroup (Fin n)) (hn : n = 5 ∨ 7 ≤ n)
    (y : normalizer (B : Set G)) :
    actPerm ψ hn y = 1 ↔ (y : G) ∈ centralizer (B : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro b hb
    have hs := actPerm_spec ψ hn y ⟨b, hb⟩
    rw [h, one_mul, inv_one, mul_one] at hs
    have h1 := ψ.injective (Subtype.ext hs)
    have h2 : (y : G) * b * (y : G)⁻¹ = b := congrArg Subtype.val h1
    calc b * (y : G) = ((y : G) * b * (y : G)⁻¹) * y := by rw [h2]
      _ = y * b := by group
  · intro h
    apply (conjPermEquiv hn).injective
    rw [map_one]
    refine MulEquiv.ext fun a => Subtype.ext ?_
    have hb : (ψ.symm a : G) ∈ B := (ψ.symm a).2
    have hs := actPerm_spec ψ hn y (ψ.symm a)
    have hy : (y : G) * (ψ.symm a : G) * (y : G)⁻¹ = ψ.symm a := by
      rw [← (mem_centralizer_iff.mp h) _ hb, mul_inv_cancel_right]
    simp only [hy, MulEquiv.apply_symm_apply] at hs
    show ((conjPerm n (actPerm ψ hn y) a : alternatingGroup (Fin n)) : Perm (Fin n)) = a
    rw [conjPerm_apply, ← hs]
    simp

theorem actPerm_eq_of (ψ : B ≃* alternatingGroup (Fin n)) (hn : n = 5 ∨ 7 ≤ n)
    (y : normalizer (B : Set G)) (σ : Perm (Fin n))
    (h : ∀ b : B, ((ψ ⟨(y : G) * b * (y : G)⁻¹, (mem_normalizer_iff.mp y.2 b).mp b.2⟩ :
        alternatingGroup (Fin n)) : Perm (Fin n)) = σ * (ψ b : Perm (Fin n)) * σ⁻¹) :
    actPerm ψ hn y = σ := by
  apply conjPerm_injective (n := n) (by omega)
  refine MulEquiv.ext fun a => Subtype.ext ?_
  rw [conjPerm_apply, conjPerm_apply]
  have h1 := actPerm_spec ψ hn y (ψ.symm a)
  have h2 := h (ψ.symm a)
  simp only [MulEquiv.apply_symm_apply] at h1 h2
  rw [← h1, h2]

end CFSG.ComponentClassification.RankTwoAlt
