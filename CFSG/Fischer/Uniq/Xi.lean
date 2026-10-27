module

public import CFSG.Fischer.Uniq.Model
public import CFSG.Fischer.TransvectionPointsBase

public section

namespace CFSG.Fischer

open CFSG.F4.Native Matrix

attribute [local irreducible] CFSG.F4.Native.uPts ptIdx uVec

theorem tvP_mul_self (p : Fin 693) : tvP p * tvP p = 1 := by
  have h : tvSU' p * tvSU' p = 1 := by
    apply Subtype.ext
    apply Units.ext
    show tvM (uVec p) * tvM (uVec p) = 1
    exact tvM_mul_self (uVec_iso ptsFacts p.2)
  rw [tvP, ← map_mul, h, map_one]

theorem tvP_tvP (p q : Fin 693) : tvP p (tvP p q) = q := by
  rw [← Equiv.Perm.mul_apply, tvP_mul_self, Equiv.Perm.one_apply]

theorem tvP_self (p : Fin 693) : tvP p p = p := by
  apply Fin.ext
  rw [tvP, piSU_apply]
  show ptIdx (tvM (uVec p) *ᵥ uVec p) = p
  rw [tvM_mulVec, uVec_iso ptsFacts p.2, zero_smul, add_zero, ptIdx_uVec ptsFacts p.2]

theorem tvP_image_image (p : Fin 693) (O : Set (Fin 693)) : tvP p '' (tvP p '' O) = O := by
  rw [Set.image_image]
  simp only [tvP_tvP, Set.image_id']

theorem mem_tvP_image (p : Fin 693) (O : Set (Fin 693)) : p ∈ tvP p '' O ↔ p ∈ O := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    have := congrArg (tvP p) hqp
    rw [tvP_tvP, tvP_self] at this
    rwa [← this]
  · intro h
    exact ⟨p, h, tvP_self p⟩

@[expose] noncomputable def polarModel : LocalModel (Fin 693) where
  perp p q := hermStd (uVec p) (uVec q) = 0
  tv := tvP
  tv_tv := tvP_tvP
  tv_self := tvP_self

theorem polarModel_perp (p q : Fin 693) :
    polarModel.perp p q ↔ hermStd (uVec p) (uVec q) = 0 :=
  Iff.rfl

theorem polarModel_tv (p : Fin 693) : polarModel.tv p = tvP p := rfl

noncomputable abbrev xiGraph (𝒮 : Set (Set (Fin 693))) : SimpleGraph 𝒮 := polarModel.xi 𝒮

theorem xiGraph_adj (𝒮 : Set (Set (Fin 693))) (O Q : 𝒮) :
    (xiGraph 𝒮).Adj O Q ↔ O ≠ Q ∧ ∃ f, f ∉ (O : Set (Fin 693)) ∧ tvP f '' (O : Set _) = Q :=
  Iff.rfl

end CFSG.Fischer
