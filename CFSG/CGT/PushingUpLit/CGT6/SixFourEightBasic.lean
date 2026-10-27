module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourSixStep
public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoJ
public import CFSG.CGT.PushingUpLit.CGT6.SixTwoType

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure EightCtx (Y : Subgroup G) (T : Sylow 2 G) (R : Subgroup G) : Prop where
  hchar : IsCharacteristicP 2 G
  hY : InClassX ↥Y
  hYT : Y = ⁅jIn (T : Subgroup G), Y⁆
  hR : IsSylowOf 2 R (centralizerModCore Y)
  hRP : oTwoIn (Subgroup.normalizer (R : Set G)) = R
  hRn : R.Normal
  hC : Subgroup.centralizer (omegaOneCenterIn R : Set G) = R

omit [Finite G] in
theorem isElemAbelian_omegaOneCenterIn (R : Subgroup G) :
    CFSG.Open.IsElemAbelian 2 (omegaOneCenterIn R) := by
  refine isElemAbelian_of_forall' (fun a ha b hb => ?_) (fun x hx => ?_)
  · exact (mem_omegaOneCenterIn_iff.mp hb).2.1 a (mem_omegaOneCenterIn_iff.mp ha).1
  · exact (mem_omegaOneCenterIn_iff.mp hx).2.2

namespace EightCtx

variable {Y R : Subgroup G} {T : Sylow 2 G}

theorem hR2 (h : EightCtx Y T R) : IsPGroup 2 R := h.hR.2.1

theorem R_le_centralizerModCore (h : EightCtx Y T R) : R ≤ centralizerModCore Y := h.hR.1

theorem R_le_normalizer_Y (h : EightCtx Y T R) : R ≤ Subgroup.normalizer (Y : Set G) :=
  fun _ hr => (h.hR.1 hr).1

theorem hNo (h : EightCtx Y T R) : SubTwo.NoTwoQuotient Y :=
  SubTwo.noTwoQuotient_of_oResidualTwo h.hY.1.residual_eq

theorem R_le_T (h : EightCtx Y T R) : R ≤ (T : Subgroup G) := by
  have : R.Normal := h.hRn
  have hTtop : IsSylowOf 2 (T : Subgroup G) ⊤ :=
    ⟨le_top, T.isPGroup', by simpa [Subgroup.relIndex_top_right] using T.not_dvd_index⟩
  exact Nine.le_of_isSylowOf_of_normal hTtop h.hR2 le_top
    (Subgroup.normalizer_eq_top R).ge

theorem jIn_le_normalizer (h : EightCtx Y T R) :
    jIn (T : Subgroup G) ≤ Subgroup.normalizer (Y : Set G) :=
  le_normalizer_of_commutator_eq h.hYT.symm

theorem V_normal (h : EightCtx Y T R) : (omegaOneCenterIn R).Normal := by
  have := h.hRn
  infer_instance

theorem le_R_of_le_centralizerModCore (h : EightCtx Y T R) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPC : P ≤ centralizerModCore Y) : P ≤ R := by
  have hRn := h.hRn
  have hP2 : IsPGroup 2 (R ⊔ P : Subgroup G) := h.hR2.to_sup_of_normal_left hP
  exact le_sup_right.trans (Nine.le_of_isSylowOf_of_le h.hR hP2 le_sup_left
    (sup_le h.hR.1 hPC))

theorem V_le_T (h : EightCtx Y T R) : omegaOneCenterIn R ≤ (T : Subgroup G) :=
  (omegaOneCenterIn_le R).trans h.R_le_T

theorem blockU_le_V (h : EightCtx Y T R) : blockU Y ≤ omegaOneCenterIn R := by
  have hRn := h.hRn
  have hchar : Subgroup.centralizer (R : Set G) ≤ R := (normal_setting_facts h.hchar h.hRP).2
  exact (step_two h.hY.1 h.hR2 hchar h.R_le_centralizerModCore).2.2.1

theorem blockU_isElemAbelian (h : EightCtx Y T R) : CFSG.Open.IsElemAbelian 2 (blockU Y) :=
  isElemAbelian_mono' (isElemAbelian_omegaOneCenterIn R) h.blockU_le_V

theorem exists_isMax_not_le (h : EightCtx Y T R) :
    ∃ A : Subgroup G, IsMaxElemAbelian (T : Subgroup G) A ∧ ¬ A ≤ centralizerModCore Y := by
  by_contra hcon
  push Not at hcon
  have hJ : jIn (T : Subgroup G) ≤ centralizerModCore Y := by
    rw [jIn_eq_thompsonJ]
    unfold thompsonJ
    exact iSup₂_le fun A hA => hcon A hA
  have hle : ⁅jIn (T : Subgroup G), Y⁆ ≤ oTwoIn Y :=
    Subgroup.commutator_le.mpr fun j hj y hy => (hJ hj).2 y hy
  rw [← h.hYT] at hle
  exact inClassX_not_le_oTwoIn h.hY hle

theorem le_normalizer_of_isMax (h : EightCtx Y T R) {A : Subgroup G}
    (hA : IsMaxElemAbelian (T : Subgroup G) A) : A ≤ Subgroup.normalizer (Y : Set G) := by
  refine le_trans ?_ h.jIn_le_normalizer
  rw [jIn_eq_thompsonJ]
  exact le_iSup₂ (f := fun (A : Subgroup G) (_ : IsMaxElemAbelian (T : Subgroup G) A) => A) A hA

theorem not_le_centralizer_V (h : EightCtx Y T R) {A : Subgroup G}
    (hA : ¬ A ≤ centralizerModCore Y) :
    ¬ A ≤ Subgroup.centralizer (omegaOneCenterIn R : Set G) := by
  rw [h.hC]
  exact fun hAR => hA (hAR.trans h.R_le_centralizerModCore)

theorem isOffG (h : EightCtx Y T R) {A : Subgroup G} (hA : IsMaxElemAbelian (T : Subgroup G) A)
    (hnot : ¬ A ≤ centralizerModCore Y) : IsOffG (omegaOneCenterIn R) A := by
  have hV := h.V_normal
  exact isOffG_of_isMaxElemAbelian (isElemAbelian_omegaOneCenterIn R) h.V_le_T
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hA (h.not_le_centralizer_V hnot)

omit [Finite G] in
theorem mem_centralizerModCore_of_centralizer_blockU
    (hCU : Y ⊓ Subgroup.centralizer (blockU Y : Set G) = oTwoIn Y) {g : G}
    (hgN : g ∈ Subgroup.normalizer (Y : Set G))
    (hgU : g ∈ Subgroup.centralizer (blockU Y : Set G)) : g ∈ centralizerModCore Y := by
  refine ⟨hgN, fun x hx => ?_⟩
  have hxg : g * x * g⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
  set z : G := x⁻¹ * (g * x * g⁻¹) with hz
  have hzY : z ∈ Y := Y.mul_mem (Y.inv_mem hx) hxg
  have hzU : z ∈ Subgroup.centralizer (blockU Y : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : g⁻¹ * u * g = u := by
      have := Subgroup.mem_centralizer_iff.mp hgU u hu
      calc g⁻¹ * u * g = g⁻¹ * (u * g) := by group
        _ = g⁻¹ * (g * u) := by rw [this]
        _ = u := by group
    have h2 : x * u * x⁻¹ ∈ blockU Y :=
      conj_mem_blockU (Subgroup.le_normalizer hx) hu
    have h3 : g * (x * u * x⁻¹) * g⁻¹ = x * u * x⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp hgU _ h2
      calc g * (x * u * x⁻¹) * g⁻¹ = (g * (x * u * x⁻¹)) * g⁻¹ := by group
        _ = ((x * u * x⁻¹) * g) * g⁻¹ := by rw [this]
        _ = x * u * x⁻¹ := by group
    have h4 : g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ = x * u * x⁻¹ := by
      calc g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹ = g * x * (g⁻¹ * u * g) * x⁻¹ * g⁻¹ := by group
        _ = g * (x * u * x⁻¹) * g⁻¹ := by rw [h1]; group
        _ = x * u * x⁻¹ := h3
    calc u * z = u * (x⁻¹ * (g * x * g⁻¹)) := rfl
      _ = x⁻¹ * (x * u * x⁻¹) * (g * x * g⁻¹) := by group
      _ = x⁻¹ * (g * x * g⁻¹ * u * (g * x * g⁻¹)⁻¹) * (g * x * g⁻¹) := by rw [h4]
      _ = z * u := by rw [hz]; group
  have hzO : z ∈ oTwoIn Y := by
    rw [← hCU]
    exact ⟨hzY, hzU⟩
  have : g * x * g⁻¹ * x⁻¹ = x * z * x⁻¹ := by rw [hz]; group
  rw [this]
  exact conj_mem_oTwoIn (Subgroup.le_normalizer hx) hzO

end EightCtx

end CFSG.CGT.PushingUpLit.CGT6
