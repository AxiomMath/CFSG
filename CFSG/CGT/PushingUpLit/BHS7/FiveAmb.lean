module

public import CFSG.CGT.PushingUpLit.BHS7.FiveBaum
public import CFSG.CGT.PushingUpLit.BHS5.AmbientJ
public import CFSG.CGT.PushingUpLit.BHS6.BlockStructure
public import CFSG.CGT.PushingUpLit.BHS.FourSymI

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits
  CFSG.QuasithinUnique CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS5
  CFSG.CGT.PushingUpLit.BHS6

variable {Γ : Type} [Group Γ] [Finite Γ] {G T M V : Subgroup Γ}

theorem autOn_baum_le_autOn_thompsonJ (hv : VHyp G T M V) :
    autOn (baum T) V ≤ autOn (thompsonJ G) V := by
  classical
  let _ : CommGroup ↥V := commGroupOfElemAbelian hv.elem
  have hsym := bhsSymType
  have hGN : G ≤ Subgroup.normalizer (V : Set Γ) := hv.normalized
  have hTG : T ≤ G := hv.minpar.T_le
  have hTN : T ≤ Subgroup.normalizer (V : Set Γ) := hTG.trans hGN
  have hsylT : IsSylowTwoOf T G := hv.minpar.syl
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hv.elem.2 v v.2)
  have h51 := hv.hyp51
  have hF := five_five hsym h51 hV2
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJN : thompsonJ T ≤ Subgroup.normalizer (V : Set Γ) := hJT.trans hTN
  have hBT : baum T ≤ T := inf_le_left
  have hBN : baum T ≤ Subgroup.normalizer (V : Set Γ) := hBT.trans hTN
  have hT2 : IsPGroup 2 ↥T := hsylT.2.1
  let 𝒜 : Set (Subgroup (MulAut ↥V)) :=
    {B | ∃ A, IsMaxElemAbelian T A ∧ B = autOn A V ∧ B ≠ ⊥}
  have hXdef : autOn (thompsonJ T) V = ⨆ B ∈ 𝒜, B := by
    refine le_antisymm ?_ (iSup₂_le fun B hB => ?_)
    · refine autOn_iSup_le (P := fun A => IsMaxElemAbelian T A) (fun A hA => ?_) fun A hA => ?_
      · exact (B6.le_thompsonJ hA).trans hJN
      · by_cases hbot : autOn A V = ⊥
        · rw [hbot]
          exact bot_le
        · exact le_iSup₂_of_le (autOn A V) ⟨A, hA, rfl, hbot⟩ le_rfl
    · obtain ⟨A, hA, rfl, -⟩ := hB
      exact autOn_le_autOn V (B6.le_thompsonJ hA)
  have hoff : ∀ B ∈ 𝒜, @IsOff ↥V _ B := by
    rintro B ⟨A, hA, rfl, hne⟩
    exact (hv.family_off hA hne).1
  have hX2 : IsPGroup 2 ↥(autOn (thompsonJ T) V) := isPGroup_autOn (hT2.to_le hJT) hJN
  have hJG : thompsonJ T ≤ thompsonJ G := iSup₂_le fun A hA =>
    le_iSup₂_of_le A (isMaxElemAbelian_of_isSylowTwoOf hsylT hA) le_rfl
  have hJeq : autOn (thompsonJ G) V = genD (autOn G V) :=
    le_antisymm (hv.autOn_thompsonJ_le hsym) (hv.genD_le_autOn_thompsonJ hsym)
  have hXle : autOn (thompsonJ T) V ≤ genD (autOn G V) :=
    hJeq ▸ autOn_le_autOn V hJG
  have hXne : autOn (thompsonJ T) V ≠ ⊥ :=
    CFSG.CGT.PushingUpLit.BHS5.autOn_ne_bot_of_not_le_centralizer hJN hv.J_not_le
  have hXT : ∀ t ∈ autOn T V, conjSub t (autOn (thompsonJ T) V) = autOn (thompsonJ T) V := by
    intro t ht
    obtain ⟨a, haT, rfl⟩ := mem_autOn_iff.1 ht
    have haN : (a : Γ) ∈ Subgroup.normalizer (V : Set Γ) := a.2
    rw [← autOn_conjSub haN, conjSub_eq_of_mem_normalizer']
    exact normalizer_le_normalizer_thompsonJ T (Subgroup.le_normalizer haT)
  have hQ2 : IsPGroup 2 ↥(autOn (baum T) V) := isPGroup_autOn (hT2.to_le hBT) hBN
  have hQP : autOn (baum T) V ≤ autOn G V := autOn_le_autOn V (hBT.trans hTG)
  have hXQ : autOn (thompsonJ T) V ≤ autOn (baum T) V :=
    autOn_le_autOn V (B6.thompsonJ_le_baum T)
  have hfix : fixV (autOn (thompsonJ T) V) ≤ fixV (autOn (baum T) V) := by
    intro w hw b hb
    obtain ⟨x, hxB, rfl⟩ := mem_autOn_iff.mp hb
    rw [← fixOn, fixOn_eq hv.elem hJN] at hw
    have hwJ : ∀ j ∈ thompsonJ T, j * (w : Γ) = (w : Γ) * j := fun j hj =>
      Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hw) j hj
    have hwΩ : (w : Γ) ∈ omegaOneCenterOf (thompsonJ T) :=
      mem_omegaOneCenter_thompsonJ_of_centralizes (hv.le_T w.2) (hv.elem.2 w w.2)
        fun A hA a ha => hwJ a (B6.le_thompsonJ hA ha)
    have hxw : (w : Γ) * (x : Γ) = (x : Γ) * (w : Γ) :=
      Subgroup.mem_centralizer_iff.mp hxB.2 w hwΩ
    apply Subtype.ext
    rw [conjAct_apply']
    calc (x : Γ) * (w : Γ) * (x : Γ)⁻¹ = ((w : Γ) * x) * (x : Γ)⁻¹ := by rw [hxw]
      _ = w := by group
  have := baum_le_genD hV2 hF hXdef hoff hX2 hXle hXne hXT hQ2 hQP hXQ hfix
  rw [hJeq]
  exact this

end CFSG.CGT.PushingUpLit.BHS7
