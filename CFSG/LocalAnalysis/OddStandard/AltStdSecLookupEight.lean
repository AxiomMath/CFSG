module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupCons
public import CFSG.LocalAnalysis.SeitzReduction.SporadicRefineAltEight
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDetOuter
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatEvenInner
public import CFSG.LocalAnalysis.SeitzReduction.CrossCharInputs

public section

namespace CFSG.OddStandard.AltStdSec

open CFSG Subgroup CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.ComponentClassification.CatLeaf
open CFSG.Sporadic.Schreier (fixSub)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.SeitzReduction.LinearPilot (FixedCentralizerTwoSmall)
open CFSG.SeitzReduction.F4Pilot (FixedCentralizerTwoFree)

@[expose] def HSOutcome {X : Type} [Group X] (t : X) : Prop :=
  ∃ W : Subgroup X, W.Normal ∧ centralizer (W : Set X) = ⊥ ∧ t ∉ W ∧
    Nonempty (W ≃* NativeSporadic.HS)

@[expose] def L44Outcome {X : Type} [Group X] (t : X) : Prop :=
  ∃ W : Subgroup X, W.Normal ∧ centralizer (W : Set X) = ⊥ ∧ t ∉ W ∧ LieModel W .PSL 4 2 2

section Fixed

variable {X : Type} [Group X] [Finite X] {t : X} {A W : Subgroup X} [W.Normal]

omit [Finite X] in
theorem le_fixedSubgroup_and_isComponent (hAW : A ≤ W)
    (hcomp : CFSG.Assembly.IsComponentOf A (centralizer ({t} : Set X))) :
    A.subgroupOf W ≤ fixedSubgroup (MulAut.conjNormal t : MulAut W) ∧
      IsComponent ((A.subgroupOf W).subgroupOf
        (fixedSubgroup (MulAut.conjNormal t : MulAut W))) := by
  have hfix : fixSub (MulAut.conjNormal t : MulAut W) = fixedSubgroup (MulAut.conjNormal t) := by
    ext x
    exact Iff.rfl
  have hLX : CFSG.Assembly.IsComponentOf A (W ⊓ centralizer ({t} : Set X)) :=
    LocalAnalysis.ComponentInitial.isComponentOf_of_le hcomp (le_inf hAW hcomp.1) inf_le_right
  have hLX' : CFSG.Assembly.IsComponentOf ((A.subgroupOf W).map W.subtype)
      ((fixedSubgroup (MulAut.conjNormal t : MulAut W)).map W.subtype) := by
    rw [map_subgroupOf_eq_of_le hAW, ← hfix, map_fixSub_conjNormal]
    exact hLX
  have h1 := (LocalAnalysis.ComponentInitial.isComponentOf_map_iff W.subtype_injective).1 hLX'
  exact ⟨h1.1, (LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h1.1).1 h1⟩

omit [Finite X] in
theorem map_le_zpowers_of_exactShape {m : ℕ} (h : ExactShape t A m) (hAW : A ≤ W)
    {U : Subgroup W} (hUc : U ≤ centralizer ((A.subgroupOf W : Subgroup W) : Set W))
    (hUf : U ≤ fixedSubgroup (MulAut.conjNormal t : MulAut W)) :
    U.map W.subtype ≤ zpowers t := by
  rw [← h.cent_cent]
  rintro _ ⟨u, hu, rfl⟩
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (mem_centralizer_iff.1 (hUc hu) ⟨a, hAW ha⟩ ha)
  · rw [mem_centralizer_singleton_iff]
    have h1 : (MulAut.conjNormal t : MulAut W) u = u := hUf hu
    have h2 := congrArg Subtype.val h1
    simp only [MulAut.conjNormal_apply] at h2
    calc (u : X) * t = t * u * t⁻¹ * t := by rw [h2]
      _ = t * u := by group

theorem twoSmall_of_exactShape {m : ℕ} (h : ExactShape t A m) (hAW : A ≤ W)
    (hle : A.subgroupOf W ≤ fixedSubgroup (MulAut.conjNormal t : MulAut W)) :
    FixedCentralizerTwoSmall (MulAut.conjNormal t : MulAut W)
      ((A.subgroupOf W).subgroupOf (fixedSubgroup (MulAut.conjNormal t : MulAut W))) := by
  intro U _ hUc hUf
  rw [map_subgroupOf_eq_of_le hle] at hUc
  have h2 := Subgroup.card_le_of_le (map_le_zpowers_of_exactShape h hAW hUc hUf)
  rwa [Subgroup.card_map_of_injective W.subtype_injective, Nat.card_zpowers, h.order] at h2

omit [Finite X] in
theorem twoFree_of_exactShape {m : ℕ} (h : ExactShape t A m) (hAW : A ≤ W) (htW : t ∉ W)
    (hle : A.subgroupOf W ≤ fixedSubgroup (MulAut.conjNormal t : MulAut W)) :
    FixedCentralizerTwoFree (MulAut.conjNormal t : MulAut W)
      ((A.subgroupOf W).subgroupOf (fixedSubgroup (MulAut.conjNormal t : MulAut W))) := by
  intro U _ hUc hUf
  rw [map_subgroupOf_eq_of_le hle] at hUc
  have h1 := map_le_zpowers_of_exactShape h hAW hUc hUf
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [h.order, sq] at this
  rw [eq_bot_iff]
  intro u hu
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 (h1 ⟨u, hu, rfl⟩)
  rcases lookup_zpow_eq_one_or_self ht2 k with h3 | h3
  · exact (Subgroup.mem_bot).2 (Subtype.ext (hk.symm.trans h3))
  · exact absurd ((hk.symm.trans h3) ▸ u.2) htW

end Fixed


theorem exactShape_almostSimple_eight (hGLS : GLS3OddLieAutComponentsInput)
    (hO : LieOrderFormulasInput) {X : Type} [Group X] [Finite X] {t : X} {A : Subgroup X}
    (hK : CFSG.SectionRank.IsKGroupCat X) (hOX : CFSG.oddCore X = ⊥) (h : ExactShape t A 8)
    (hF : AlmostSimple X) : SymOutcome t 8 ∨ HSOutcome t ∨ L44Outcome t := by
  obtain ⟨W, hWN, hWs, hWnab, hCW, hcat, hAW, hcomp⟩ := almostSimple_setup hK hOX h (by norm_num) hF
  have := hWN
  obtain ⟨eA⟩ := h.iso
  set σ : MulAut W := MulAut.conjNormal t with hσ
  have hσ2 : σ * σ = 1 := conjNormal_mul_self h.order
  have hσ1 : σ ≠ 1 := by
    intro h1
    have h2 : t ∈ centralizer (W : Set X) := by
      rw [mem_centralizer_iff]
      intro w hw
      have h3 := congrArg (fun φ : MulAut W => ((φ ⟨w, hw⟩ : W) : X)) h1
      simp only [hσ, MulAut.conjNormal_apply, MulAut.one_apply] at h3
      calc w * t = t * w * t⁻¹ * t := by rw [h3]
        _ = t * w := by group
    rw [hCW, mem_bot] at h2
    have h4 := h.order
    rw [h2, orderOf_one] at h4
    omega
  have hσo : orderOf σ = 2 := orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  obtain ⟨hle, hD⟩ := le_fixedSubgroup_and_isComponent hAW hcomp
  set D := (A.subgroupOf W).subgroupOf (fixedSubgroup σ) with hDdef
  have eD : D ≃* alternatingGroup (Fin 8) :=
    ((subgroupOfEquivOfLe hle).trans (subgroupOfEquivOfLe hAW)).trans eA
  have hZ : center D = ⊥ := center_eq_bot_of_alt (by norm_num) eD
  have hDm : LieModel (D ⧸ center D) .PSL 4 2 1 :=
    (ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff _).2
      ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eD⟩
  have hinner : t ∈ W → σ ∈ (MulAut.conj : W →* MulAut W).range := fun htW =>
    ⟨⟨t, htW⟩, by
      ext w
      simp [hσ, MulAut.conjNormal_apply, MulAut.conj_apply]⟩
  have houter : t ∉ W → σ ∉ (MulAut.conj : W →* MulAut W).range := fun htW =>
    conjNormal_not_mem_inner hCW htW
  have hfree : t ∉ W → FixedCentralizerTwoFree σ D := fun htW =>
    twoFree_of_exactShape h hAW htW hle
  have hsmall : FixedCentralizerTwoSmall σ D := twoSmall_of_exactShape h hAW hle
  rcases (Milestones.ct_catalog_nonabelian_type_partition W hWnab).mp hcat with
    ⟨n, -, ⟨eW⟩⟩ | hodd | heven | hsp
  · exact Or.inl (symOutcome_of_alt h (by norm_num) hAW hCW hcomp eW).1
  · exfalso
    have h1 := CFSG.SeitzReduction.CrossChar.catSLmOddLieAt_of_lieOrderFormulas hO hGLS (m := 4)
      (by norm_num) W hWs hWnab hodd σ hσo 1 D hD hDm
    omega
  · by_cases htW : t ∈ W
    · exact (CFSG.SeitzReduction.LinearPilot.catSLmEvenInner W hWs hWnab heven σ hσo
        (hinner htW) 4 1 D hD hDm).elim
    · exact Or.inr (Or.inr ⟨W, hWN, hCW, htW,
        CFSG.SeitzReduction.LinearPilot.catSLmEvenOuterAt_of_three_le (m := 4) (by norm_num) W hWs
          hWnab heven σ hσo (houter htW) 1 D hD hDm (hfree htW)⟩)
  · have h2 : (σ ∈ (MulAut.conj : W →* MulAut W).range ∧ FixedCentralizerTwoSmall σ D) ∨
        FixedCentralizerTwoFree σ D := by
      by_cases htW : t ∈ W
      · exact Or.inl ⟨hinner htW, hsmall⟩
      · exact Or.inr (hfree htW)
    obtain ⟨hout, ⟨eHS⟩⟩ := CFSG.SeitzReduction.SporadicRefine.sporadic_alt_eight_component hWs
      hWnab hsp hσo hD eD h2
    exact Or.inr (Or.inl ⟨W, hWN, hCW, fun htW => hout (hinner htW), ⟨eHS⟩⟩)

end CFSG.OddStandard.AltStdSec
