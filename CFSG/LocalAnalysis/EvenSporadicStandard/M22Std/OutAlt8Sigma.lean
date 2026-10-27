module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup Equiv Equiv.Perm

variable {X : Type} [Group X] {E : Subgroup X} [E.Normal]

noncomputable def permOf (e : E ≃* alternatingGroup (Fin 8)) : X →* Perm (Fin 8) :=
  (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
        (by norm_num))).symm.toMonoidHom.comp
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal)

theorem conjNormal_permOf (e : E ≃* alternatingGroup (Fin 8)) (x : X) :
    MulAut.conjNormal (H := alternatingGroup (Fin 8)) (permOf e x) =
      MulAut.congr e (MulAut.conjNormal x) :=
  MulEquiv.apply_symm_apply (MulEquiv.ofBijective
    (MulAut.conjNormal (H := alternatingGroup (Fin 8)))
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
      (by norm_num))) _

theorem permOf_conj (e : E ≃* alternatingGroup (Fin 8)) (x : X) (g : alternatingGroup (Fin 8)) :
    permOf e x * (g : Perm (Fin 8)) * (permOf e x)⁻¹ =
      (e (MulAut.conjNormal x (e.symm g)) : Perm (Fin 8)) := by
  have h := congrArg (fun f : MulAut (alternatingGroup (Fin 8)) =>
    ((f g : alternatingGroup (Fin 8)) : Perm (Fin 8))) (conjNormal_permOf e x)
  exact h

theorem permOf_of_mem (e : E ≃* alternatingGroup (Fin 8)) {a : X} (ha : a ∈ E) :
    permOf e a = ((e ⟨a, ha⟩ : alternatingGroup (Fin 8)) : Perm (Fin 8)) := by
  refine (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8 (by norm_num)
    (by norm_num)).1 ?_
  apply MulEquiv.ext
  intro g
  apply Subtype.ext
  rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply, permOf_conj]
  have h : MulAut.conjNormal a (e.symm g) = ⟨a, ha⟩ * e.symm g * (⟨a, ha⟩ : E)⁻¹ :=
    Subtype.ext (by rw [MulAut.conjNormal_apply]; rfl)
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem mem_centralizer_of_permOf_eq_one (e : E ≃* alternatingGroup (Fin 8)) {x : X}
    (hx : permOf e x = 1) : x ∈ centralizer (E : Set X) := by
  rw [mem_centralizer_iff]
  intro h hh
  have hconj : MulAut.congr e (MulAut.conjNormal x) = 1 := by
    rw [← conjNormal_permOf, hx, map_one]
  have h1 : MulAut.conjNormal (H := E) x = 1 :=
    (MulAut.congr e).injective (hconj.trans (map_one (MulAut.congr e)).symm)
  have h2 := congrArg (fun f : MulAut E => ((f ⟨h, hh⟩ : E) : X)) h1
  have h3 : x * h * x⁻¹ = h := h2
  exact (mul_inv_eq_iff_eq_mul.1 h3).symm

end CFSG.EvenSporadicStandard.M22Std
