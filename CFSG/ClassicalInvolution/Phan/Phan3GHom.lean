module

public import CFSG.ClassicalInvolution.Phan.TitsChamber

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem
  CFSG.ClassicalInvolution.Phan.TitsChamber

variable {I C : Type*} {X : ChamberSystem I C} {𝒥 : Set I → Prop} {x : C}
  {γ γ' γ'' : List (I × C)}

theorem ElemMoveOn.append_right (h : ElemMoveOn X 𝒥 x γ γ') (δ : List (I × C)) :
    ElemMoveOn X 𝒥 x (γ ++ δ) (γ' ++ δ) := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  simpa only [List.append_assoc] using
    ElemMoveOn.mk (X := X) (x := x) γ₁ η η' (γ₂ ++ δ) J hJ hη hη' hηJ hη'J hend

theorem ElemMoveOn.append_left (α : List (I × C))
    (h : ElemMoveOn X 𝒥 (galleryEnd x α) γ γ') : ElemMoveOn X 𝒥 x (α ++ γ) (α ++ γ') := by
  obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
  rw [← galleryEnd_append x α γ₁] at hη hη' hend
  simpa only [List.append_assoc] using
    ElemMoveOn.mk (X := X) (x := x) (α ++ γ₁) η η' γ₂ J hJ hη hη' hηJ hη'J hend

@[refl] protected theorem HomotopicOn.refl (γ : List (I × C)) : HomotopicOn X 𝒥 x γ γ :=
  Relation.EqvGen.refl γ

@[symm] protected theorem HomotopicOn.symm (h : HomotopicOn X 𝒥 x γ γ') :
    HomotopicOn X 𝒥 x γ' γ :=
  Relation.EqvGen.symm _ _ h

@[trans] protected theorem HomotopicOn.trans (h : HomotopicOn X 𝒥 x γ γ')
    (h' : HomotopicOn X 𝒥 x γ' γ'') : HomotopicOn X 𝒥 x γ γ'' :=
  Relation.EqvGen.trans _ _ _ h h'

theorem HomotopicOn.append_right (h : HomotopicOn X 𝒥 x γ γ') (δ : List (I × C)) :
    HomotopicOn X 𝒥 x (γ ++ δ) (γ' ++ δ) := by
  induction h with
  | rel _ _ h => exact HomotopicOn.of_elemMoveOn (ElemMoveOn.append_right h δ)
  | refl => exact HomotopicOn.refl _
  | symm _ _ _ ih => exact HomotopicOn.symm ih
  | trans _ _ _ _ _ ih ih' => exact HomotopicOn.trans ih ih'

theorem HomotopicOn.append_left (α : List (I × C)) (h : HomotopicOn X 𝒥 (galleryEnd x α) γ γ') :
    HomotopicOn X 𝒥 x (α ++ γ) (α ++ γ') := by
  induction h with
  | rel _ _ h => exact HomotopicOn.of_elemMoveOn (ElemMoveOn.append_left α h)
  | refl => exact HomotopicOn.refl _
  | symm _ _ _ ih => exact HomotopicOn.symm ih
  | trans _ _ _ _ _ ih ih' => exact HomotopicOn.trans ih ih'

theorem HomotopicOn.append {δ δ' : List (I × C)} (h : HomotopicOn X 𝒥 x γ γ')
    (h' : HomotopicOn X 𝒥 (galleryEnd x γ) δ δ') : HomotopicOn X 𝒥 x (γ ++ δ) (γ' ++ δ') :=
  HomotopicOn.trans (HomotopicOn.append_left γ h') (HomotopicOn.append_right h δ')

theorem HomotopicOn.of_twoHomotopic (h2 : ∀ J : Set I, J.encard ≤ 2 → 𝒥 J)
    (h : X.TwoHomotopic x γ γ') : HomotopicOn X 𝒥 x γ γ' := by
  induction h with
  | rel _ _ h =>
    obtain ⟨γ₁, η, η', γ₂, J, hJ, hη, hη', hηJ, hη'J, hend⟩ := h
    exact HomotopicOn.of_elemMoveOn (.mk γ₁ η η' γ₂ J (h2 J hJ) hη hη' hηJ hη'J hend)
  | refl => exact HomotopicOn.refl _
  | symm _ _ _ ih => exact HomotopicOn.symm ih
  | trans _ _ _ _ _ ih ih' => exact HomotopicOn.trans ih ih'

end CFSG.ClassicalInvolution.Phan.Q3G
