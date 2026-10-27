module

public import CFSG.CGT.PushingUpLit.BHS7.SevenThirteenQ4
public import CFSG.CGT.PushingUpLit.BHS7.SevenEleven
public import CFSG.CGT.PushingUpLit.BHS7.SevenSix

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] def Seven12QSub (G T : Subgroup Γ) : Prop :=
  ⁅vSub G T, zSub T⁆ = ⊥ → ∀ F E : Subgroup Γ, IsBTBlock G T F → ¬ F ≤ cStarIn G T →
    (∀ x ∈ qSub (vSub G T) T, ∀ f ∈ F, ⁅x, f⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ)) →
    E ∈ bStarT G T → F ≤ E → F ≠ E →
    ∀ x ∈ qSub (vSub G T) T, ∀ e ∈ E, ⁅x, e⁆ ∈ Subgroup.centralizer (vSub G T : Set Γ)

section Finite

variable [Finite Γ] {G T : Subgroup Γ}

theorem exists_isBTBlock_notC_le_of_lSet (h : MinCex G T) {X : Subgroup Γ} (hX : X ∈ lSet G T) :
    ∃ F : Subgroup Γ, IsBTBlock G T F ∧ ¬ F ≤ cStarIn G T ∧ F ≤ X := by
  have hT : IsSylowTwoOf T G := h.sylow
  have hb0 : baum T ≠ ⊥ := fun h0 => h.ne (cStarIn_eq_of_baum_eq_bot h0)
  obtain ⟨hXG, hBX, hXC⟩ := hX
  obtain ⟨S, hS, hBS⟩ := B6.exists_isSylowTwoOf_ge (hT.2.1.to_le inf_le_left) hBX
  obtain ⟨-, -, 𝒢, hblock, -, -, hc, -⟩ := seven_three h hT ⟨hXG, hBX, hXC⟩ hS
  have hSX : baum S = baum T :=
    baum_eq_of_isPGroup_of_baum_le hT hS.2.1 (hS.1.trans hXG.le) hBS
  by_contra hall
  push Not at hall
  apply hXC
  rw [← hc]
  refine sup_le (two_three_d hT hb0 hXG.le hS hBS) (iSup₂_le fun F hF => ?_)
  by_contra hFC
  exact hall F (isBTBlock_of_sub (hblock F hF) hXG.le hSX hFC) hFC (hblock F hF).le

theorem seven_twelve_q_of_sub (h : MinCex G T) (h5 : Seven5 G T) (hsub : Seven12QSub G T) :
    Seven12Q G T := by
  intro hZ
  have hT : IsSylowTwoOf T G := h.sylow
  have h5' : ¬ IsMinParabolic2 T G := h5
  obtain ⟨X, hTX, hXG, hXC⟩ := exists_not_le_cStarIn_of_not_isMinParabolic2 hT h.ne h5'
  have hXL : X ∈ lSet G T := ⟨hXG, (C1GN.baum_le T).trans hTX, hXC⟩
  obtain ⟨F, hF, hFC, hFX⟩ := exists_isBTBlock_notC_le_of_lSet h hXL
  obtain ⟨E, hE, hFE⟩ := (seven_six h h5').2 F hF hFC
  have hFT : ∀ x ∈ qSub (vSub G T) T, ∀ f ∈ F, ⁅x, f⁆ ∈
      Subgroup.centralizer (vSub G T : Set Γ) := by
    have := seven_eleven h hF hFC hXL hFX (tZero_le.trans hTX)
    rw [tZero_of_eq hZ] at this
    exact this
  refine ⟨E, hE, ?_⟩
  by_cases hFEeq : F = E
  · subst hFEeq
    exact hFT
  · exact hsub hZ F E hF hFC hFT hE hFE hFEeq

end Finite

end CFSG.CGT.PushingUpLit.BHS7
