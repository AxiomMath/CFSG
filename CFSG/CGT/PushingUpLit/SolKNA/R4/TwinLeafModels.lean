module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafMain
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicM22Model
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ3

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall

theorem noQ16Q16_mulAut_of_autModel {X₀ : Type} [Group X₀] {W : Type} [Group W] {X : Subgroup W}
    (hW : CFSG.ComponentClassification.RankTwoSporadic.AutModel X₀ W X) {F : Type} [Group F]
    (e : F ≃* X₀) (h : NoQ16Q16 W) : NoQ16Q16 (MulAut F) := by
  obtain ⟨ε⟩ := hW.nonempty_mulEquiv
  haveI := hW.normal
  let c : W →* MulAut ↥X := MulAut.conjNormal
  have hinj : Function.Injective c := by
    rw [injective_iff_map_eq_one]
    intro w hw
    have h1 : w ∈ Subgroup.centralizer (X : Set W) := by
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have := congrArg (fun α : MulAut ↥X => ((α ⟨m, hm⟩ : ↥X) : W)) hw
      simp only [c, MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc m * w = (w * m * w⁻¹) * w := by rw [this]
        _ = w * m := by group
    rw [hW.centralizer_eq_bot, Subgroup.mem_bot] at h1
    exact h1
  have hsurj : Function.Surjective c := by
    intro α
    obtain ⟨w, hw⟩ := hW.exists_conj α
    exact ⟨w, MulEquiv.ext fun x => Subtype.ext (hw x).symm⟩
  let g : MulAut F ≃* MulAut ↥X := MulAut.congr (e.trans ε.symm)
  let φ : MulAut ↥X ≃* W := (MulEquiv.ofBijective c ⟨hinj, hsurj⟩).symm
  exact NoQ16Q16.of_injective (φ.toMonoidHom.comp g.toMonoidHom)
    (φ.injective.comp g.injective) h

open CFSG.ComponentClassification.PSL3Four in
theorem autL34NoQ16Q16_of_model
    (h : NoQ16Q16 ↥CFSG.ComponentClassification.PSL3Four.R) : AutL34NoQ16Q16 := by
  intro F _ hF
  rcases hF with ⟨-, hF⟩ | ⟨hF, -⟩ | ⟨hF, -⟩ | ⟨hF, -⟩
  · obtain ⟨φ⟩ := CFSG.ComponentClassification.PSL3Four.nonempty_equiv_of_stated F hF
    obtain ⟨E, -, -⟩ := CFSG.ComponentClassification.PSL3Four.full_automorphism_action
    exact NoQ16Q16.of_injective
      (E.symm.toMonoidHom.comp (MulAut.congr φ).toMonoidHom)
      (E.symm.injective.comp (MulAut.congr φ).injective) h
  all_goals exact absurd hF (by norm_num)

theorem autM22NoQ16Q16_of_model
    (h : NoQ16Q16 ↥CFSG.Monster.B.TwoA.Ppair) : AutM22NoQ16Q16 := by
  intro F _ hF
  obtain ⟨e⟩ := hF
  exact noQ16Q16_mulAut_of_autModel
    CFSG.ComponentClassification.RankTwoSporadic.M22.m22AutModel e h

theorem autJ2NoQ16Q16_of_model
    (h : NoQ16Q16 ↥CFSG.ComponentClassification.J2Cover.R) : AutJ2NoQ16Q16 := by
  intro F _ hF
  obtain ⟨e⟩ := hF
  exact noQ16Q16_mulAut_of_autModel
    CFSG.ComponentClassification.RankTwoSporadic.J2.j2AutModel e h

theorem autJ3NoQ16Q16_of_model
    (h : NoQ16Q16 ↥CFSG.Sporadic.SmallOddCore.j3R) : AutJ3NoQ16Q16 := by
  intro F _ hF
  obtain ⟨e⟩ := hF
  exact noQ16Q16_mulAut_of_autModel
    CFSG.ComponentClassification.RankTwoSporadic.J3.j3AutModel e h

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
