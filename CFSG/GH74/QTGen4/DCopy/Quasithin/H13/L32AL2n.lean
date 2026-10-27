module

public import CFSG.Quasithin.H13.L32AL2n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk8
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2m

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K : Subgroup G}

theorem caseOne_of_red_F4 (hD36 : D36) (hD37 : D37)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4) (h33 : Lemma14_7_33_F4)
    (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (R : L2Red G T L V K)
    (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) : L2CaseOne G T L V := by
  have hall := dγ_lt_uγ_of_red_F4 hA37 hA38 h29 h1222 h1332 h1334 h76 h33 h36 hlist R hF
  refine ⟨hall, ?_⟩
  have : IsMulCommutative ↥(conjClosure V (A6.g1 T V)) := hF.F911_3.1
  obtain ⟨t₀, C⟩ := exists_ctxL2_of_red hA37 hA38 R
  obtain ⟨W, hW⟩ := exists_topW R.S hF
  have X : TopCtx T L V K W t₀ := ⟨R, C, hW⟩
  obtain ⟨γ₀, γ₀', g₀, s₀⟩ := hF.exists_F8Setup
  obtain ⟨γ, γ', g, s, hpos, hle, -⟩ := hF.lemma_14_5_18_four s₀ (hall _ _ _ s₀)
  have hUp : IsPGroup 2 ↥(conjClosure V (A6.g1 T V)) := F7.isPGroup_of_isElemAbelian hF.F911_3
  have hUγp : IsPGroup 2 ↥(F8.Uγ V (A6.g1 T V) (g : G)) :=
    F7.isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have h4 := X.card_img_lt_four_F4 hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334 s
    hpos hle
  have hcard : Nat.card (X.img (F8.Uγ V (A6.g1 T V) (g : G))) =
      (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex (F8.Uγ V (A6.g1 T V) (g : G)) := by
    rw [X.card_img_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 (hF.Uγ_le_H s),
      hF.Dγ_eq_inf_pCoreOf s]
  have hm1 : mIdx (F8.Uγ V (A6.g1 T V) (g : G)) (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)) = 1 := by
    have h1 : 2 ^ mIdx (F8.Uγ V (A6.g1 T V) (g : G)) (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)) <
        2 ^ 2 := by
      rw [← HypF98.relIndex_eq_two_pow_mIdx hUγp, ← hcard]
      exact h4
    have h2 := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h1
    omega
  have hγ2 : (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex
      (F8.Uγ V (A6.g1 T V) (g : G)) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUγp, hm1, pow_one]

  have hDHlt : F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G) < conjClosure V (A6.g1 T V) := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hDHU => ?_
    obtain ⟨δ, δ', k, y, sk, -, -, eU, -, -, eDγ⟩ :=
      hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s (hall γ γ' g s))
    have := hall δ δ' k sk
    rw [eDγ, hDHU, ← eU] at this
    exact lt_irrefl _ this
  have hH2 : (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex (conjClosure V (A6.g1 T V)) =
      2 := by
    have h1 : mIdx (conjClosure V (A6.g1 T V)) (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)) ≤ 1 :=
      hle.trans hm1.le
    have h2 : (F8.DH V (fsuV1 T V) (A6.g1 T V) (g : G)).relIndex (conjClosure V (A6.g1 T V)) ≠
        1 := fun h =>
      hDHlt.ne ((Subgroup.relIndex_eq_one.mp h).antisymm (centralizerMod_le_left _ _ _)).symm
    rw [HypF98.relIndex_eq_two_pow_mIdx hUp] at h2 ⊢
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h0 | h0
    · rw [h0, pow_zero] at h2
      exact absurd rfl h2
    · rw [h0, pow_one]

  have hnt : ∀ y : ↥(A6.g1 T V), ¬ IsTransvection (C1Pack.rhoH hF.toHypF91 y) := fun y =>
    not_isTransvection_red_F4 hA37 hA38 h29 h1222 h1332 h1334 h76 h33 h36 hlist R hF
      (QuotientGroup.mk y)
  have hA1 := A₁_le_of_relIndex hF s hγ2 hH2 hnt

  have hV1 : fsuV1 T V ≤ F8.Uγ V (A6.g1 T V) (g : G) := by
    obtain ⟨δ, δ', k, y, sk, -, hyδ, eU, eB, eDH, eDγ⟩ :=
      hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s (hall γ γ' g s))
    have hky : ((k : G))⁻¹ * (y : G) ∈ A6.g1 T V := by
      have h1 : (k⁻¹ * y) • F8.γ₁ T L (A6.g1 T V) = F8.γ₁ T L (A6.g1 T V) := by
        rw [mul_smul, hyδ, ← sk.edge₁, inv_smul_smul]
      have := mem_stab_of_smul_eq h1
      rw [stab_γ₁ hF.amalgamHypV.le₂] at this
      simpa using this
    have eA : F8.A₁ (fsuV1 T V) (k : G) = Quasithin.conjSub (y : G) (fsuV1 T V) := by
      have e : (y : G) = (k : G) * ((k : G)⁻¹ * (y : G)) := by group
      rw [F8.A₁, e, Quasithin.conjSub_mul, F7.conjSub_eq_of_mem_normalizer
        (hF.toHypF91.H_normalizes_V₁ hky)]
    have hγ2k : (F8.Dγ V (fsuV1 T V) (A6.g1 T V) (k : G)).relIndex
        (F8.Uγ V (A6.g1 T V) (k : G)) = 2 := by
      rw [eDγ, eU, F9.relIndex_conjSub]
      exact hH2
    have hH2k : (F8.DH V (fsuV1 T V) (A6.g1 T V) (k : G)).relIndex
        (conjClosure V (A6.g1 T V)) = 2 := by
      rw [eDH, ← eB, F9.relIndex_conjSub]
      exact hγ2
    have h := A₁_le_of_relIndex hF sk hγ2k hH2k hnt
    rw [eA, ← eB] at h
    have := conjSub_mono ((y : G))⁻¹ h
    rwa [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
  refine ⟨γ, γ', g, s, ?_, hH2, hV1, hA1⟩
  have hc : Nat.card ↥(modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G))) =
      Nat.card (X.img (F8.Uγ V (A6.g1 T V) (g : G))) := by
    rw [TopCtx.img_eq_map, Subgroup.card_map_of_injective
      (X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334)]
  rw [hc, hcard, hγ2]

theorem lemma14_7_32_L2_mod_of_F4
    (hD36 : D36) (hD37 : D37) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4)
    (h33 : Lemma14_7_33_F4) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29_F4)
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) :
    Lemma14_7_32_L2_mod_F4 := by
  intro G _ _ T L V K R
  exact caseOne_of_red_F4 hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334 R
    (Setting147.hypF98_F4 R.S (stmt13_3_2_two_of_F4 h1332) (stmtL32NModule_of_inputs_F4 h1332 h1334) h1222)

end CFSG.Quasithin.H13.L32A.L2
