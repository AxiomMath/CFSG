module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step33Syl
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3G2V
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec3Step33

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.ComponentClassification.RankTwoExceptional
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard
open scoped Pointwise

namespace G2

variable {K : Type} [Field K] [CharP K 2]

local notation "X" => pinnedX Tag.G2 K

theorem commutator_g2ShortParabolicRadical_g2TorusR
    [Finite K] (hK : Nat.card K = 4) :
    ⁅g2ShortParabolicRadical K, g2TorusR K⁆ = g2ShortParabolicRadical K := by
  have hHN : g2TorusR K ≤ normalizer (g2ShortParabolicRadical K : Set (ModGL .G2 K)) :=
    le_sup_right.trans g2Para_le_normalizer
  apply le_antisymm
  · rw [commutator_le]
    intro d hd h hh
    have h1 := (mem_normalizer_iff.mp (hHN hh) d⁻¹).mp (inv_mem hd)
    rw [commutatorElement_def, show d * h * d⁻¹ * h⁻¹ = d * (h * d⁻¹ * h⁻¹) by group]
    exact mul_mem hd h1
  · have hV : g2V K ≤ ⁅g2ShortParabolicRadical K, g2TorusR K⁆ := by
      rw [← commutator_g2V0_g2TorusR hK]
      exact commutator_mono g2V0_le_g2ShortParabolicRadical le_rfl
    obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one hK
    have hω := sq_add_self_add_one_of_ne hK hω0 hω1
    have hω4 := pow_four_eq_self hK ω
    set t : Kˣ := Units.mk0 ω hω0 with ht
    have hr : ∀ A : K, X g2r A ∈ ⁅g2ShortParabolicRadical K, g2TorusR K⁆ := by
      intro A
      have hXr : X g2r (ω ^ 2 * A) ∈ g2ShortParabolicRadical K := by
        rw [pinnedX_r_eq_g2N]
        exact g2N_mem_g2ShortParabolicRadical _ 0 0 0 0
      have hht : torusElt .G2 K g2ir t ∈ g2TorusR K := ⟨t, rfl⟩
      have h := commutator_mem_commutator hXr hht
      rw [commutatorElement_def] at h
      rw [show X g2r (ω ^ 2 * A) * torusElt .G2 K g2ir t * (X g2r (ω ^ 2 * A))⁻¹ *
          (torusElt .G2 K g2ir t)⁻¹ = X g2r (ω ^ 2 * A) * (torusElt .G2 K g2ir t *
            X g2r (ω ^ 2 * A) * (torusElt .G2 K g2ir t)⁻¹)⁻¹ by group,
        torus_r_conj t isRoot_g2r 2 (by decide), pinnedX_inv_eq, ← pinnedX_add] at h
      convert h using 2
      rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Units.val_pow_eq_pow_val,
        Units.val_mk0]
      linear_combination (norm := char2_ring) -A * hω - A * hω4
    have hu : ∀ C : K, X g2u C ∈ ⁅g2ShortParabolicRadical K, g2TorusR K⁆ := fun C =>
      hV ⟨C, 0, 0, by rw [pinnedX_u_eq_g2N]⟩
    have hv : ∀ D : K, X g2v D ∈ ⁅g2ShortParabolicRadical K, g2TorusR K⁆ := fun D =>
      hV ⟨0, D, 0, by rw [pinnedX_v_eq_g2N]⟩
    have hc : ∀ F : K, X g2c F ∈ ⁅g2ShortParabolicRadical K, g2TorusR K⁆ := fun F =>
      hV ⟨0, 0, F, by rw [pinnedX_c_eq_g2N]⟩
    have hb : ∀ E : K, X g2b E ∈ ⁅g2ShortParabolicRadical K, g2TorusR K⁆ := by
      intro E
      have h := mul_mem (mul_mem (mul_mem (hr 1) (hv E)) (inv_mem (hr 1))) (inv_mem (hv E))
      rwa [← commutatorElement_def, comm_r_v, one_mul] at h
    rintro _ ⟨A, C, D, E, F, rfl⟩
    rw [show g2N A 0 C D E F = X g2r A * X g2a 0 * X g2u C * X g2v D * X g2b E * X g2c F from
      rfl, pinnedX_zero, mul_one]
    exact mul_mem (mul_mem (mul_mem (mul_mem (hr A) (hu C)) (hv D)) (hb E)) (hc F)

end G2

section Step34

variable {G : Type} [Group G] [Finite G] {A A₁ R : Subgroup G} {g : G} {E F : Subgroup G} {x : G}
  {Zs P T Q B₀ : Subgroup G} {z y : G} {D J U : Subgroup G}

theorem D_eq_commutator
    (hD : Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U) : D = ⁅D, zpowers x⁆ := by
  have hS := hD.suz.setting
  obtain ⟨K, _, _, _, hK, f, hM⟩ := exists_sec3Model hS
  have hD₀C : g2ShortParabolicRadical K ≤ adjointGroup .G2 K :=
    G2.g2ShortParabolicRadical_le_adjointGroup
  have hHrC : g2TorusR K ≤ adjointGroup .G2 K := G2.g2TorusR_le_adjointGroup
  have hPC : G2.g2Para K ≤ adjointGroup .G2 K :=
    sup_le (sup_le hD₀C (g2RankOne_le_adjointGroup g2ia)) hHrC
  have hDf : D = ((g2ShortParabolicRadical K).subgroupOf (adjointGroup .G2 K)).map f := by
    rw [hD.D_eq, hM.I_eq, Sec3.tr_pCoreOf hM.inj hPC, G2.pCoreOf_g2Para hK]
  rw [hDf, ← hM.x_eq, ← Sec3.tr_commutator hD₀C hHrC,
    G2.commutator_g2ShortParabolicRadical_g2TorusR hK]

theorem P_le_normalizer_D
    (hD : Sec3D G A A₁ R g E F x Zs P T Q B₀ z y D J U) :
    P ≤ normalizer (D : Set G) := by
  have hSz := hD.suz
  have hS := hSz.setting
  obtain ⟨-, -, -, hN⟩ := DR_facts hD
  obtain ⟨hDxA, -, -⟩ := sec3D_model hD
  have hRA : R ≤ centralizer (A : Set G) := hS.sylowR.le
  have hxA : x ∈ A := (hDxA (mem_sup_right (mem_zpowers x))).1
  have hDA : D ≤ A := (le_sup_left.trans hDxA).trans inf_le_left
  have hDR : D = ⁅D ⊔ R, zpowers x⁆ := by
    refine le_antisymm ((D_eq_commutator hD).le.trans (commutator_mono le_sup_left le_rfl)) ?_
    rw [commutator_le]
    intro v hv w hw
    have hv' : v ∈ (D : Set G) * (R : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ fun r hr => centralizer_le_normalizer _
        (mem_centralizer_iff.mpr fun d hd => mem_centralizer_iff.mp (hRA hr) d (hDA hd))]
      exact hv
    obtain ⟨d, hd, r, hr, hdr⟩ := hv'
    have hdr' : v = d * r := hdr.symm
    subst hdr'
    rw [commutatorElement_def]
    have hwA : w ∈ A := zpowers_le.mpr hxA hw
    have hrw : r * w = w * r := (mem_centralizer_iff.mp (hRA hr) w hwA).symm
    rw [show d * r * w * (d * r)⁻¹ * w⁻¹ = d * (r * w) * r⁻¹ * d⁻¹ * w⁻¹ by group, hrw,
      show d * (w * r) * r⁻¹ * d⁻¹ * w⁻¹ = d * w * d⁻¹ * w⁻¹ by group, D_eq_commutator hD]
    exact commutator_mem_commutator hd hw
  intro p hp
  have hpDR : p ∈ normalizer ((D ⊔ R : Subgroup G) : Set G) :=
    hN ((P_le_X hSz) hp).1
  have hpx : p ∈ normalizer ((zpowers x : Subgroup G) : Set G) := ((P_le_X hSz) hp).2
  rw [mem_normalizer_iff_map_conj_eq] at hpDR hpx ⊢
  rw [hDR, map_commutator, hpDR, hpx]

end Step34

end CFSG.ComponentClassification.AS81
