module

public import CFSG.CGT.PushingUpLit.BHS5.AmbientConj
public import CFSG.CGT.PushingUpLit.BHS5.FiveFiveOrbit

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS

variable {Γ : Type} [Group Γ]

theorem autOn_ne_bot_of_not_le_centralizer {V A : Subgroup Γ}
    (hAN : A ≤ Subgroup.normalizer (V : Set Γ)) (hA : ¬ A ≤ Subgroup.centralizer (V : Set Γ)) :
    autOn A V ≠ ⊥ := by
  intro hbot
  apply hA
  intro a ha
  have h1 : conjAct V ⟨a, hAN ha⟩ ∈ autOn A V := mem_autOn_iff.2 ⟨⟨a, hAN ha⟩, ha, rfl⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact (conjAct_eq_one_iff V ⟨a, hAN ha⟩).1 h1

variable [Finite Γ] {G T M V : Subgroup Γ} (hv : VHyp G T M V)

include hv

theorem VHyp.autOn_thompsonJ_le (hsym : BHSSymType) :
    autOn (thompsonJ G) V ≤ @genD ↥V (commGroupOfElemAbelian hv.elem) (autOn G V) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hv.elem
  have hGN : G ≤ Subgroup.normalizer (V : Set Γ) := hv.normalized
  have h51 := hv.hyp51
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hv.elem.2 v v.2)
  have hsylT : IsSylowTwoOf T G := hv.minpar.syl
  have hYP : genD (autOn G V) ≤ autOn G V := genD_le h51 hV2
  have hJ : ∀ A, IsMaxElemAbelian T A → autOn A V ≤ genD (autOn G V) := by
    intro A hA
    refine jPart hsym h51 hV2 (fun X => ∃ A, IsMaxElemAbelian T A ∧ X = autOn A V) ?_ ?_ ?_ _
      ⟨A, hA, rfl⟩
    · rintro X ⟨A', hA', rfl⟩
      exact autOn_le_autOn V (hA'.1.trans hv.minpar.T_le)
    · rintro X ⟨A', hA', rfl⟩ hne
      exact hv.family_off hA' hne
    · rintro X ⟨A', hA', rfl⟩ Y hYX hw
      obtain ⟨A'', hA'', hA''Y⟩ := hv.family_sub hA' Y hYX hw
      exact ⟨A'', hA'', hA''Y.symm⟩
  have hlift : thompsonJ G ≤ liftSub V G (genD (autOn G V)) := by
    refine iSup₂_le fun A hA => ?_
    obtain ⟨g, hgG, hgA⟩ := exists_conj_isMaxElemAbelian hsylT hA
    have hgN : g⁻¹ ∈ Subgroup.normalizer (V : Set Γ) := hGN (G.inv_mem hgG)
    have h1 : autOn A V = conjSub (conjAct V ⟨g⁻¹, hgN⟩) (autOn (cjSub g A) V) := by
      have := autOn_conjSub (V := V) hgN (X := cjSub g A)
      rwa [show conjSub g⁻¹ (cjSub g A) = A from cjSub_inv_cjSub g A] at this
    have hτ : conjAct V ⟨g⁻¹, hgN⟩ ∈ autOn G V :=
      mem_autOn_iff.2 ⟨⟨g⁻¹, hgN⟩, G.inv_mem hgG, rfl⟩
    have hτY : conjSub (conjAct V ⟨g⁻¹, hgN⟩) (genD (autOn G V)) = genD (autOn G V) :=
      conjSub_eq_of_mem_normalizer' (le_normalizer_genD h51 hV2 hτ)
    have hAY : autOn A V ≤ genD (autOn G V) := by
      rw [h1]
      calc conjSub (conjAct V ⟨g⁻¹, hgN⟩) (autOn (cjSub g A) V)
          ≤ conjSub (conjAct V ⟨g⁻¹, hgN⟩) (genD (autOn G V)) := conjSub_mono _ (hJ _ hgA)
        _ = genD (autOn G V) := hτY
    intro x hx
    have hxN : x ∈ Subgroup.normalizer (V : Set Γ) := hGN (hA.1 hx)
    exact mem_liftSub_iff.2 ⟨hA.1 hx, hxN, hAY (mem_autOn_iff.2 ⟨⟨x, hxN⟩, hx, rfl⟩)⟩
  calc autOn (thompsonJ G) V ≤ autOn (liftSub V G (genD (autOn G V))) V :=
        autOn_le_autOn V hlift
    _ = genD (autOn G V) := autOn_liftSub hYP

theorem VHyp.genD_le_autOn_thompsonJ (hsym : BHSSymType) :
    @genD ↥V (commGroupOfElemAbelian hv.elem) (autOn G V) ≤ autOn (thompsonJ G) V := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hv.elem
  have hTN : T ≤ Subgroup.normalizer (V : Set Γ) := hv.minpar.T_le.trans hv.normalized
  have h51 := hv.hyp51
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hv.elem.2 v v.2)
  have hsylT : IsSylowTwoOf T G := hv.minpar.syl
  have hF := five_five hsym h51 hV2
  obtain ⟨A, hA, hne⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (V : Set Γ) := by
    by_contra hcon
    push Not at hcon
    exact hv.J_not_le (iSup₂_le fun A hA => hcon A hA)
  have hAN : A ≤ Subgroup.normalizer (V : Set Γ) := hA.1.trans hTN
  obtain ⟨hoff, hw⟩ := hv.family_off hA (autOn_ne_bot_of_not_le_centralizer hAN hne)
  obtain ⟨B₀, hB₀, hB₀A⟩ := exists_offSet_le h51 hV2
    (autOn_le_autOn V (hA.1.trans hv.minpar.T_le)) hoff hw
  refine iSup₂_le fun B hB => ?_
  obtain ⟨g, hg, hgB⟩ := hF.exists_conj_offSet h51 hV2 hB₀ hB
  obtain ⟨a, haG, rfl⟩ := mem_autOn_iff.1 hg
  have hmax : IsMaxElemAbelian G (conjSub (a : Γ) A) :=
    isMaxElemAbelian_cjSub (Subgroup.le_normalizer haG) (isMaxElemAbelian_of_isSylowTwoOf hsylT hA)
  have hle : conjSub (a : Γ) A ≤ thompsonJ G := le_iSup₂_of_le (conjSub (a : Γ) A) hmax le_rfl
  calc B = conjSub (conjAct V a) B₀ := hgB.symm
    _ ≤ conjSub (conjAct V a) (autOn A V) := conjSub_mono _ hB₀A
    _ = autOn (conjSub (a : Γ) A) V := (autOn_conjSub a.2).symm
    _ ≤ autOn (thompsonJ G) V := autOn_le_autOn V hle

end CFSG.CGT.PushingUpLit.BHS5
