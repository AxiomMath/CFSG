module

public import CFSG.LocalAnalysis.RankThreeUC.GN15ParaDich
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.Quasithin.Background.A4V
import CFSG.Quasithin.EmptyFaithful.S1412

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

section Strong

variable {X : Type} [Group X] [Finite X] {T : Subgroup X}

omit [Finite X] in
private theorem baum_le_centralizer_of_le_omegaOneCenterOf {D : Subgroup X}
    (hDB : D ≤ omegaOneCenterOf (baum T)) : baum T ≤ Subgroup.centralizer (D : Set X) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hdc : d ∈ centerOf (baum T) := A4.omegaOneCenterOf_le_centerOf _ (hDB hd)
  exact (Subgroup.mem_centralizer_iff.mp hdc.2 b hb).symm

theorem isC118WeakPair_inf_centralizer {R D T₂ : Subgroup X} (hBR : baum T ≤ R) (hRT : R ≤ T)
    (hD0 : D ≠ ⊥) (hDB : D ≤ omegaOneCenterOf (baum T)) (hT₂0 : T₂ ≠ ⊥) (hT₂B : T₂ ≤ baum T)
    (hT₂c : (T₂.subgroupOf (baum T)).Characteristic) (hU : C118Univ (baum T) D T₂) :
    IsC118WeakPair (R ⊓ Subgroup.centralizer (D : Set X)) D T₂ := by
  set R' : Subgroup X := R ⊓ Subgroup.centralizer (D : Set X) with hR'
  have hBR' : baum T ≤ R' := le_inf hBR (baum_le_centralizer_of_le_omegaOneCenterOf hDB)
  have hR'T : R' ≤ T := inf_le_left.trans hRT
  have hb : baum R' = baum T := (baum_eq_of_le hBR' hR'T).symm
  have hDR' : D ≤ omegaOneCenterOf R' := by
    intro x hx
    have hcent : x ∈ Subgroup.centralizer (R' : Set X) :=
      Subgroup.mem_centralizer_iff.mpr fun r hr => (Subgroup.mem_centralizer_iff.mp hr.2 x hx).symm
    exact Subgroup.subset_closure ⟨⟨hBR' ((A4.omegaOneCenterOf_le_centerOf _ (hDB hx)).1), hcent⟩,
      A4.sq_eq_one_of_mem_omegaOneCenterOf (hDB hx)⟩
  refine ⟨hD0, hDR', hT₂0, hb ▸ hT₂B, ?_, ?_⟩
  · rw [hb]; exact hT₂c
  · rw [hb]; exact hU

theorem threeElement_dichotomy_strong (hX : GNSetting X T) {D T₂ : Subgroup X}
    (hD0 : D ≠ ⊥) (hDB : D ≤ omegaOneCenterOf (baum T)) (hDV : D ≤ gnV T)
    (hT₂0 : T₂ ≠ ⊥) (hT₂B : T₂ ≤ baum T) (hT₂c : (T₂.subgroupOf (baum T)).Characteristic)
    (hU : C118Univ (baum T) D T₂) {R : Subgroup X} (hBR : baum T ≤ R) (hRT : R ≤ T)
    (hCR : T ⊓ gnC T ≤ R) {c : X ⧸ gnC T} (hc3 : orderOf c = 3)
    (hnorm : gnImg T R ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (X ⧸ gnC T)))
    (hnotB : ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (gnImg T (baum T) : Set (X ⧸ gnC T))) :
    c ∈ gnImg T (Subgroup.centralizer (D : Set X)) ∨
      c ∈ gnImg T (Subgroup.normalizer (T₂ : Set X)) ∨
      ∃ H Kb : Subgroup X, pCoreOf 2 (⊤ : Subgroup X) ≤ H ∧ IsBlock2 H Kb ∧ IsAltType Kb 3 ∧
        ¬ Kb ≤ gnC T ∧ gnImg T Kb = Subgroup.zpowers c := by
  set R' : Subgroup X := R ⊓ Subgroup.centralizer (D : Set X) with hR'
  have hW : IsC118WeakPair R' D T₂ :=
    isC118WeakPair_inf_centralizer hBR hRT hD0 hDB hT₂0 hT₂B hT₂c hU
  have hCD : gnC T ≤ Subgroup.centralizer (D : Set X) := Subgroup.centralizer_le hDV
  have hBR' : baum T ≤ R' := le_inf hBR (baum_le_centralizer_of_le_omegaOneCenterOf hDB)
  have hCR' : T ⊓ gnC T ≤ R' := le_inf hCR (inf_le_right.trans hCD)
  have hQR' : pCoreOf 2 (⊤ : Subgroup X) ≤ R' :=
    (le_inf (B6.pCoreOf_two_le_of_isSylowTwoOf hX.sylow) (pCoreOf_le_gnC hX)).trans hCR'
  have hRsp : IsPGroup 2 (gnImg T R') :=
    (hX.sylow.2.1.to_le (inf_le_left.trans hRT)).map (QuotientGroup.mk' (gnC T))
  have hnorm' : gnImg T R' ≤ Subgroup.normalizer (Subgroup.zpowers c : Set (X ⧸ gnC T)) :=
    (Subgroup.map_mono inf_le_left).trans hnorm
  have hnot' : ¬ Subgroup.zpowers c ≤ Subgroup.normalizer (gnImg T R' : Set (X ⧸ gnC T)) :=
    not_zpowers_le_normalizer_of_le hRsp hc3 hnorm' (Subgroup.map_mono hBR') hnotB
  exact threeElement_dichotomy_of_weak hX hW (inf_le_left.trans hRT) hCR' hQR' hc3 hnorm' hnot'

end Strong

section Invariance

variable {X : Type} [Group X] {T : Subgroup X}

theorem conj_mem_gnImg_centralizer {D : Subgroup X} {b : X}
    (hb : b ∈ Subgroup.normalizer (D : Set X)) {c : X ⧸ gnC T}
    (hc : c ∈ gnImg T (Subgroup.centralizer (D : Set X))) :
    QuotientGroup.mk' (gnC T) b * c * (QuotientGroup.mk' (gnC T) b)⁻¹ ∈
      gnImg T (Subgroup.centralizer (D : Set X)) := by
  obtain ⟨k, hk, rfl⟩ := hc
  have hk' : k ∈ Subgroup.centralizer (D : Set X) := hk
  refine ⟨b * k * b⁻¹, ?_, by simp⟩
  show b * k * b⁻¹ ∈ Subgroup.centralizer (D : Set X)
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  have hd' : b⁻¹ * d * b ∈ D := by
    have h1 : b * (b⁻¹ * d * b) * b⁻¹ = d := by group
    exact (Subgroup.mem_normalizer_iff.mp hb (b⁻¹ * d * b)).mpr (by rw [h1]; exact hd)
  have hkc := Subgroup.mem_centralizer_iff.mp hk' _ hd'
  calc d * (b * k * b⁻¹) = b * ((b⁻¹ * d * b) * k) * b⁻¹ := by group
    _ = b * (k * (b⁻¹ * d * b)) * b⁻¹ := by rw [hkc]
    _ = (b * k * b⁻¹) * d := by group

theorem conj_mem_gnImg_normalizer {T₂ : Subgroup X} {b : X}
    (hb : b ∈ Subgroup.normalizer (T₂ : Set X)) {c : X ⧸ gnC T}
    (hc : c ∈ gnImg T (Subgroup.normalizer (T₂ : Set X))) :
    QuotientGroup.mk' (gnC T) b * c * (QuotientGroup.mk' (gnC T) b)⁻¹ ∈
      gnImg T (Subgroup.normalizer (T₂ : Set X)) := by
  obtain ⟨k, hk, rfl⟩ := hc
  exact ⟨b * k * b⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hb hk) (Subgroup.inv_mem _ hb),
    by simp⟩

theorem normalizer_baum_le_normalizer_inf_gnV {C : Subgroup X} (hCB : C ≤ baum T)
    (hCc : (C.subgroupOf (baum T)).Characteristic) :
    Subgroup.normalizer (baum T : Set X) ≤ Subgroup.normalizer ((C ⊓ gnV T : Subgroup X) : Set X) :=
  fun _ hb => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨normalizer_le_normalizer_of_characteristic_subgroupOf hCB hCc hb,
      (Subgroup.normalizer_eq_top_iff.mpr (Subgroup.normalClosure_normal
        (s := (omegaOneCenterOf T : Set X)))).symm ▸ Subgroup.mem_top _⟩

end Invariance

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
