module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84GTab
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F1Defs
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F0
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F9Nk
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84F9Tk
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G1Par
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G2K
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G3AU
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G4Gam
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G5UY
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84G6Ule
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Basic

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Step84GamK_of (F : Sec8T84Base) (hI : Asc82Step84IK) (h811 : Asc82Lemma811K)
    (hSw : Sec8T84OuterSwaps) (hP : Sec8T84FactP) (hTw : Sec8T84FactTwist)
    (hGi : Sec8T84FactGamInner) (hO5 : Sec8T84FactOm5Out) (hS4 : Sec8T84FactS4) :
    Asc82Step84GamK := by
  intro G _ _ hKP t L S z g B E hE
  have hctx : Sec8Ctx G t L S z g B := hE.ctx
  have hS : IsSylow2Of S (centralizer ({t} : Set G)) := hctx.sylow
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hctx.involution]
    exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htS : t ∈ S := sec4_t_mem_S hS hctx.involution
  obtain ⟨E1, hE1, hgood⟩ := sec8_goodE F.h36 F.hM F.h8A hE
  obtain ⟨B', E', T, γ0, hE', hgood', hT, hST, hγ0, hγ0T, hout0, hgen0⟩ :=
    sec8t84f_NK_of F hI h811 hSw hP (sec8t84f_TK_of F hI h811 hSw hP) G hKP t L S z g B E1 hE1
      hgood
  have htN : t ∈ normalizer (E' : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro e
    constructor
    · intro he
      exact hE'.t_norm e he
    · intro he
      have h := hE'.t_norm (t * e * t⁻¹) he
      have hkey : t * (t * e * t⁻¹) * t⁻¹ = e := by
        rw [htinv]
        calc t * (t * e * t) * t = (t * t) * e * (t * t) := by group
          _ = e := by rw [ht2]; group
      rwa [hkey] at h
  have htT : t ∈ T := hST ⟨htS, htN⟩
  obtain ⟨Y1, Y2, hXO⟩ := h811 G hKP t L S z g B' E' hE'
  obtain ⟨F1, D⟩ := sec8t84_tdata_of hP ht2 hE'.elem hXO hT htT
  have hset : Sec8T84GSet G t E' Y1 Y2 T (T ⊓ Y1) (T ⊓ Y2) (E' ⊓ Y1) (E' ⊓ Y2) F1
      (F1.map (MulAut.conj t).toMonoidHom) := ⟨hE'.elem, hXO, hT, D, rfl, rfl, rfl, rfl⟩
  have hγ0S : γ0 ∈ S := hγ0.1
  have hγ0comm : γ0 * t = t * γ0 :=
    Subgroup.mem_centralizer_singleton_iff.mp (hS.1 hγ0S)
  have hsq : γ0 * γ0 ∈ zpowers t := sec8t84_gamma_sq F hctx hγ0S hout0
  have hγ0p : IsPGroup 2 ↥(zpowers γ0) := hS.2.1.to_le (Subgroup.zpowers_le.mpr hγ0S)
  obtain ⟨γ1, hγ1eq, hγ1N, hγ1T, hγ1sq, -, hE_1, hE0_1, hE1_1, -⟩ :=
    sec8t84g_gamma_fp D hE'.elem hT hγ0.2 hγ0p hγ0T hsq hγ0comm
  have hLt : L ≤ centralizer ({t} : Set G) := hctx.toSec3SettingLB.component.le
  have htcent : t ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLt hl)
  have hγ1S : γ1 ∈ S := by
    rcases hγ1eq with rfl | rfl
    · exact hγ0S
    · exact S.mul_mem hγ0S htS
  have hout1 : InducesOutsideGStar L 6 (-1) γ1 := by
    rcases hγ1eq with rfl | rfl
    · exact hout0
    · exact sec8t84g4_outer_mul_cent hout0 htcent
  have hgen1 : S = zpowers t ⊔ zpowers γ1 ⊔ (S ⊓ L) := by
    apply le_antisymm
    · calc S = zpowers t ⊔ zpowers γ0 ⊔ (S ⊓ L) := hgen0
        _ ≤ zpowers t ⊔ zpowers γ1 ⊔ (S ⊓ L) := by
          refine sup_le (sup_le ?_ ?_) le_sup_right
          · exact le_sup_left.trans le_sup_left
          · rcases hγ1eq with rfl | rfl
            · exact le_sup_right.trans le_sup_left
            · have h1 : γ0 * t ∈ zpowers t ⊔ zpowers (γ0 * t) ⊔ (S ⊓ L) :=
                (le_sup_right.trans le_sup_left :
                  zpowers (γ0 * t) ≤ zpowers t ⊔ zpowers (γ0 * t) ⊔ (S ⊓ L))
                  (Subgroup.mem_zpowers _)
              have h2 : t ∈ zpowers t ⊔ zpowers (γ0 * t) ⊔ (S ⊓ L) :=
                (le_sup_left.trans le_sup_left :
                  zpowers t ≤ zpowers t ⊔ zpowers (γ0 * t) ⊔ (S ⊓ L)) (Subgroup.mem_zpowers _)
              rw [Subgroup.zpowers_le]
              simpa using mul_mem h1 (inv_mem h2)
    · exact sup_le (sup_le (Subgroup.zpowers_le.mpr htS) (Subgroup.zpowers_le.mpr hγ1S))
        inf_le_left
  obtain ⟨hU1, hU2, -, -, -, -⟩ := sec8t84g_gamma_U hP hS4 hset hE_1 hE0_1 hE1_1
  obtain ⟨hJ0, γ2, hγ2S, hγ2ord, hγ2out, hγ2gen, hγ2t, hE_2, hE0_2, hU1_2, hU2_2, hC1, hC2⟩ :=
    sec8t84g_gamma_two F hSw hTw hE' hgood' hset hST ⟨hγ1S, hγ1N⟩ hγ1T hγ1sq hout1 hgen1
      hE_1 hE0_1 hU1 hU2
  have hγ2sq : γ2 * γ2 = 1 := by
    rw [← pow_two, ← hγ2ord]
    exact pow_orderOf_eq_one γ2
  obtain ⟨U, y, hU, hUγ, htU, hUt, hy, hyγ, hyU, hyfix⟩ :=
    sec8t84g_U_y hP hS4 hset hγ2sq hγ2t hE_2 hE0_2 hU1_2 hU2_2 hC1 hC2 hJ0
  obtain ⟨K, hK, hKF, hK0, hKN⟩ := sec8t84g_K_exists F hctx hγ2S hγ2ord hγ2out
  have hUK : U ≤ K :=
    sec8t84g_U_le_K F hGi hO5 hctx hγ2S hγ2ord hγ2out hK hKF hK0 hKN hU hUγ htU hUt hy hyγ hyU
      hyfix
  exact ⟨γ2, K, U, ⟨hctx, hγ2S, hγ2ord, hγ2out, hγ2gen, hK, hKF, hK0, hKN, hU, hUK, htU⟩⟩

end CFSG.OddStandard.SmallF3.Omega
