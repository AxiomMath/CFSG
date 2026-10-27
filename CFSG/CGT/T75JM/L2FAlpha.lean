module

public import CFSG.CGT.T75JM.L2FTab
public import Certificates.Certificate14984

public section

namespace CFSG.CGT.T75JM

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

@[expose] def alphaGen (i : Fin 6) : N0 := n0 (alphaImg i)

theorem alpha_lift (w : W6) : FreeGroup.lift alphaGen (FreeGroup.mk w) = n0 (substWord w) := by
  induction w with
  | nil => simp [substWord, n0_nil, FreeGroup.lift_mk]
  | cons p w ih =>
    have h1 : FreeGroup.lift alphaGen (FreeGroup.mk (p :: w)) =
        (cond p.2 (alphaGen p.1) (alphaGen p.1)⁻¹) * FreeGroup.lift alphaGen (FreeGroup.mk w) := by
      rw [FreeGroup.lift_mk, FreeGroup.lift_mk, List.map_cons, List.prod_cons]
    have h2 : substWord (p :: w) =
        (if p.2 then alphaImg p.1 else invWord (alphaImg p.1)) ++ substWord w := by
      simp [substWord]
    rw [h1, ih, h2, n0_append]
    obtain ⟨i, b⟩ := p
    cases b <;> simp [alphaGen, n0_invWord]

@[expose] def AlphaInj : Prop :=
  ∀ w w' : W6, n0 (substWord w) = n0 (substWord w') → n0 w = n0 w'

section Alpha



theorem alpha_rel (h : alphaRelCheck = true) :
    ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ rels6.map FreeGroup.mk}, FreeGroup.lift alphaGen r = 1 := by
  intro r hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  rw [alpha_lift]
  simp only [alphaRelCheck, List.all_eq_true, beq_iff_eq] at h
  rw [← n0_nil]
  exact n0_eq_of_tab_eq (h w hw)

@[expose] noncomputable def alphaHom (h : alphaRelCheck = true) : N0 →* N0 :=
  PresentedGroup.toGroup (alpha_rel h)

theorem alphaHom_mk (h : alphaRelCheck = true) (w : W6) :
    alphaHom h (n0 w) = n0 (substWord w) := by
  have hcomp : (alphaHom h).comp (PresentedGroup.mk _) = FreeGroup.lift alphaGen := by
    apply FreeGroup.ext_hom
    intro i
    simp only [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    exact PresentedGroup.toGroup.of _
  rw [← alpha_lift]
  exact congrArg (fun f => f (FreeGroup.mk w)) hcomp

theorem alphaHom_injective (h : alphaRelCheck = true) (hi : AlphaInj) :
    Function.Injective (alphaHom h) := by
  intro x y hxy
  obtain ⟨i, rfl⟩ := isTab_surj x
  obtain ⟨j, rfl⟩ := isTab_surj y
  rw [alphaHom_mk, alphaHom_mk] at hxy
  exact hi _ _ hxy

instance : Finite N0 := Certificates.certificate14984.2.2.1.1

@[expose] noncomputable def alphaEquiv (h : alphaRelCheck = true) (hi : AlphaInj) :
    N0 ≃* N0 :=
  MulEquiv.ofBijective (alphaHom h)
    ⟨alphaHom_injective h hi, Finite.injective_iff_surjective.1 (alphaHom_injective h hi)⟩

theorem alphaEquiv_apply (h : alphaRelCheck = true) (hi : AlphaInj) (x : N0) :
    alphaEquiv h hi x = alphaHom h x :=
  rfl

theorem alpha_map_T (h : alphaRelCheck = true) (hi : AlphaInj)
    (ht : tCheck = true) (hT : alphaTCheck = true) :
    n0T.map (alphaEquiv h hi).toMonoidHom = n0T := by
  have hle : n0T.map (alphaEquiv h hi).toMonoidHom ≤ n0T := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨k, hk, rfl⟩ := (mem_n0T_iff ht y).1 hy
    simp only [alphaTCheck, List.all_eq_true, List.mem_range] at hT
    have h2 := hT k hk
    have h3 : IsTab (n0Tab (substWord (tw k))) (n0 (substWord (tw k))) := IsTab.ofWord _
    have h4 := (tTabs_contains_iff ht h3).1 h2
    simpa [alphaEquiv_apply, alphaHom_mk] using h4
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact (Subgroup.card_map_of_injective (alphaEquiv h hi).injective).ge

end Alpha

end CFSG.CGT.T75JM
