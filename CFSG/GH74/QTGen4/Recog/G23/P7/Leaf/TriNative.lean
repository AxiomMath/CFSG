module

public import CFSG.GH74.QTGen4.Recog.G23.NativeFacts
public import Certificates.Certificate320014
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.GH74.QTGen4.Recog.G23 CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem lift_mk_substTri {X : Type*} [Group X] (ρ : Fin 6 → X) (r : List (Fin 6 × Bool)) :
    FreeGroup.lift ρ (FreeGroup.mk (substTri r)) =
      FreeGroup.lift (fun i => FreeGroup.lift ρ (FreeGroup.mk (triUWord i))) (FreeGroup.mk r) := by
  induction r with
  | nil => simp [substTri]
  | cons l r ih =>
    have h1 : substTri (l :: r) = substTri [l] ++ substTri r := by simp [substTri]
    have h2 : (l :: r) = [l] ++ r := rfl
    rw [h1, ← FreeGroup.mul_mk, map_mul, ih, h2, ← FreeGroup.mul_mk, map_mul]
    congr 1
    obtain ⟨i, b⟩ := l
    cases b
    · have hs : substTri [(i, false)] = invWord (triUWord i) := by simp [substTri]
      rw [hs, lift_mk_invWord, lift_mk_single]
      simp
    · have hs : substTri [(i, true)] = triUWord i := by simp [substTri]
      rw [hs, lift_mk_single]
      simp

section Certificate


theorem triNative_rels : ∀ r ∈ triWords, evalCode (substTri r) = one14 :=
  Certificates.certificate320014.1

theorem triNative_gens : ∀ i, evalCode (substTri (triEWord i)) = eCode i :=
  Certificates.certificate320014.2

end Certificate

private noncomputable def ghatToGL : Ghat →* GL (Fin 14) (ZMod 3) :=
  MonoidHom.mk' (fun x => (adjointEquivR3 x : GL (Fin 14) (ZMod 3))) fun x y => by
    rw [map_mul]
    rfl

private theorem ghatToGL_apply (x : Ghat) :
    ghatToGL x = (adjointEquivR3 x : GL (Fin 14) (ZMod 3)) := rfl

private theorem ghatToGL_injective : Function.Injective ghatToGL :=
  Subtype.val_injective.comp adjointEquivR3.injective

theorem leafTriNative :
    LeafTriNative := by
  let e : Fin 6 → Ghat := fun i => adjointEquivR3.symm ⟨eEl i, eEl_mem i⟩
  have he : ∀ i, ghatToGL (e i) = eEl i := fun i => by simp [ghatToGL_apply, e]
  have hcomp : ghatToGL.comp (FreeGroup.lift e) = FreeGroup.lift eEl :=
    FreeGroup.ext_hom _ _ fun i => by simp [he]
  have hmat : ∀ w : List (Fin 6 × Bool),
      ((ghatToGL (FreeGroup.lift e (FreeGroup.mk w)) : GL (Fin 14) (ZMod 3)) :
        Matrix (Fin 14) (Fin 14) (ZMod 3)) = dec14 (evalCode w) := fun w => by
    have h : ghatToGL (FreeGroup.lift e (FreeGroup.mk w)) = FreeGroup.lift eEl (FreeGroup.mk w) :=
      DFunLike.congr_fun hcomp _
    rw [h, lift_mk_eq, coe_Lt_prod]
  let u : Fin 6 → Ghat := fun i => FreeGroup.lift e (FreeGroup.mk (triUWord i))
  have hu : ∀ r, FreeGroup.lift u (FreeGroup.mk r) =
      FreeGroup.lift e (FreeGroup.mk (substTri r)) := fun r => (lift_mk_substTri e r).symm
  refine ⟨u, fun r hr => ghatToGL_injective (Units.ext ?_), ?_⟩
  · rw [hu, hmat, triNative_rels r hr, dec14_one14, map_one, Units.val_one]
  ·
    have hgen : ∀ i, e i ∈ Subgroup.closure (Set.range u) := fun i => by
      have h : e i = FreeGroup.lift u (FreeGroup.mk (triEWord i)) :=
        ghatToGL_injective (Units.ext (by rw [hu, hmat, triNative_gens i, he, coe_eEl]))
      rw [h, ← FreeGroup.range_lift_eq_closure]
      exact ⟨_, rfl⟩
    rw [eq_top_iff]
    intro x _
    have hmap : (Subgroup.closure (Set.range e)).map ghatToGL =
        Subgroup.closure (Set.range eEl) := by
      rw [MonoidHom.map_closure, ← Set.range_comp, show ⇑ghatToGL ∘ e = eEl from funext he]
    have hx : ghatToGL x ∈ Subgroup.closure (Set.range eEl) := R3_le_closure (adjointEquivR3 x).2
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hy' : y ∈ Subgroup.closure (Set.range u) :=
      (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hgen i) hy
    exact (ghatToGL_injective hyx) ▸ hy'

end CFSG.GH74.QTGen4.Recog.G23.P7
