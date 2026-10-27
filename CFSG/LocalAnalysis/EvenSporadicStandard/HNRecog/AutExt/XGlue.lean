module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.XCentAmbient
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3Model.SubModel
public import Certificates.Certificate441899

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Section3 Section3Model

theorem exists_mulEquiv_Gx_XP {H : Type} [Group H] (Ψ : H ≃* ↥P1408) {x : H} (hx : Ψ x = pZ) :
    ∃ f : ↥(Gx x) ≃* ↥XModel.XP, ∀ y : ↥(Gx x),
      ((f y : ↥XModel.XP) : Equiv.Perm (Fin 1408)) =
        ((Ψ (y : H) : ↥P1408) : Equiv.Perm (Fin 1408)) := by
  have key : ∀ g : H, g ∈ Gx x ↔ ((Ψ g : ↥P1408) : Equiv.Perm (Fin 1408)) * elemZ =
      elemZ * ((Ψ g : ↥P1408) : Equiv.Perm (Fin 1408)) := by
    intro g
    rw [mem_Gx]
    constructor
    · intro hg
      have h1 : Ψ x * Ψ g = Ψ g * Ψ x := by rw [← map_mul, ← map_mul, hg]
      rw [hx] at h1
      exact (congrArg Subtype.val h1).symm
    · intro h
      apply Ψ.injective
      rw [map_mul, map_mul, hx]
      exact Subtype.ext h.symm
  have inv_mem : ∀ g : ↥XModel.XP,
      Ψ.symm ⟨(g : Equiv.Perm (Fin 1408)), (XModel.mem_XP_iff.1 g.2).1⟩ ∈ Gx x := by
    intro g
    rw [key, MulEquiv.apply_symm_apply]
    exact (XModel.mem_XP_iff.1 g.2).2
  refine ⟨{
    toFun := fun y => ⟨((Ψ (y : H) : ↥P1408) : Equiv.Perm (Fin 1408)),
      XModel.mem_XP_iff.2 ⟨(Ψ y).2, (key y).1 y.2⟩⟩
    invFun := fun g => ⟨Ψ.symm ⟨g.1, (XModel.mem_XP_iff.1 g.2).1⟩, inv_mem g⟩
    left_inv := fun y => Subtype.ext (by simp)
    right_inv := fun g => Subtype.ext (by simp)
    map_mul' := fun y y' => Subtype.ext (by simp) }, fun y => rfl⟩

section Cert


theorem xInnerFacts_of_check : XInnerFacts := by
  intro H _ E hE a z b z₁ hf hd x hx A hA
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover hE.toIsHSCover)
  obtain ⟨Ψ, hΨ, hΨx⟩ := exists_labelled_iso_at_z hE hf hd hx
  obtain ⟨f, hf'⟩ := exists_mulEquiv_Gx_XP Ψ hΨx
  have hfA : ((f A : ↥XModel.XP) : Equiv.Perm (Fin 1408)) = elemA := by
    rw [hf', hA, hΨ.a_eq]
    rfl
  have h1 := (XModel.xInner_of_facts (Certificates.certificate441899 hP) (f A) hfA).map
    f.symm
  rwa [MulEquiv.symm_apply_apply] at h1

theorem xCentFacts_of_check :
    XCentFacts := by
  intro H _ E hE a z b z₁ hf hd x hx T hT2 hcard
  have hP : Nat.card ↥P1408 = 177408000 := card_P1408 (hsCtx_of_isHSCover hE.toIsHSCover)
  obtain ⟨Ψ, hΨ, hΨx⟩ := exists_labelled_iso_at_z hE hf hd hx
  obtain ⟨f, hf'⟩ := exists_mulEquiv_Gx_XP Ψ hΨx
  have hT2' : f T * f T = 1 := by rw [← map_mul, hT2, map_one]
  have hcard' : Nat.card ↥(Subgroup.centralizer ({f T} : Set ↥XModel.XP)) = 768 ∨
      Nat.card ↥(Subgroup.centralizer ({f T} : Set ↥XModel.XP)) = 384 := by
    rw [card_centralizer_eq_of_mulEquiv f T]
    exact hcard
  have h1 := (XModel.xCent_ambient (Certificates.certificate441899 hP) hP (f T) hT2'
    hcard').map f.symm
  rwa [MulEquiv.symm_apply_apply] at h1

end Cert

end CFSG.EvenSporadicStandard.HNRecog.Section4
