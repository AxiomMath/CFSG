module

public import CFSG.CGT.PushingUpLit.BHS5.AmbientConj
public import CFSG.CGT.PushingUpLit.BHS6.BlockStructure

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.QuasithinUnique CFSG.RankThree.PartOne
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5 CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

variable {Γ : Type} [Group Γ] [Finite Γ] {T V : Subgroup Γ}

@[expose] def jFamily (T V : Subgroup Γ) : Set (Subgroup (MulAut ↥V)) :=
  {B | ∃ A, IsMaxElemAbelian T A ∧ B = autOn A V ∧ B ≠ ⊥}

omit [Finite Γ] in
theorem autOn_thompsonJ_eq_iSup (hTN : T ≤ Subgroup.normalizer (V : Set Γ)) :
    autOn (thompsonJ T) V = ⨆ B ∈ jFamily T V, B := by
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJN : thompsonJ T ≤ Subgroup.normalizer (V : Set Γ) := hJT.trans hTN
  refine le_antisymm ?_ (iSup₂_le fun B hB => ?_)
  · refine autOn_iSup_le (P := fun A => IsMaxElemAbelian T A) (fun A hA => ?_) fun A hA => ?_
    · exact (B6.le_thompsonJ hA).trans hJN
    · by_cases hbot : autOn A V = ⊥
      · rw [hbot]
        exact bot_le
      · exact le_iSup₂_of_le (autOn A V) ⟨A, hA, rfl, hbot⟩ le_rfl
  · obtain ⟨A, hA, rfl, -⟩ := hB
    exact autOn_le_autOn V (B6.le_thompsonJ hA)

theorem jFamily_isOff (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hTN : T ≤ Subgroup.normalizer (V : Set Γ)) :
    ∀ B ∈ jFamily T V, @IsOff ↥V (commGroupOfElemAbelian hV) B := by
  rintro B ⟨A, hA, rfl, hne⟩
  have hAN : A ≤ Subgroup.normalizer (V : Set Γ) := hA.1.trans hTN
  have hnc : ¬ A ≤ Subgroup.centralizer (V : Set Γ) := fun hc =>
    hne (CFSG.CGT.PushingUpLit.BHS.autOn_eq_bot_of_le_centralizer hc)
  exact (isOffG_iff_isOff_autOn hV hAN).mp (isOffG_of_isMaxElemAbelian hV hVT hTN hA hnc)

theorem fixV_autOn_thompsonJ_le (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hTN : T ≤ Subgroup.normalizer (V : Set Γ)) :
    @fixV ↥V (commGroupOfElemAbelian hV) (autOn (thompsonJ T) V) ≤
      @fixV ↥V (commGroupOfElemAbelian hV) (autOn (baum T) V) := by
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJN : thompsonJ T ≤ Subgroup.normalizer (V : Set Γ) := hJT.trans hTN
  intro w hw b hb
  obtain ⟨x, hxB, rfl⟩ := mem_autOn_iff.mp hb
  have hwJ : (w : Γ) ∈ Subgroup.centralizer ((thompsonJ T : Subgroup Γ) : Set Γ) :=
    (mem_fixV_autOn_iff hV hJN w).1 hw
  have hwΩ : (w : Γ) ∈ omegaOneCenterOf (thompsonJ T) :=
    mem_omegaOneCenter_thompsonJ_of_centralizes (hVT w.2) (hV.2 w w.2) fun A hA a ha =>
      Subgroup.mem_centralizer_iff.mp hwJ a (B6.le_thompsonJ hA ha)
  have hxw : (w : Γ) * (x : Γ) = (x : Γ) * (w : Γ) :=
    Subgroup.mem_centralizer_iff.mp hxB.2 w hwΩ
  apply Subtype.ext
  rw [conjAct_apply']
  calc (x : Γ) * (w : Γ) * (x : Γ)⁻¹ = ((w : Γ) * x) * (x : Γ)⁻¹ := by rw [hxw]
    _ = w := by group

end CFSG.CGT.PushingUpLit.BHS7
