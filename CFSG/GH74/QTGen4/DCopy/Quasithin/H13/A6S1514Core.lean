module

public import CFSG.Quasithin.H13.A6S1514Core
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1515

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem g22_T5_F4 (hNS : ¬ LieModel G .PSp 3 2 1)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) {H : Subgroup G} (hH : H ∈ S.Hz)
    (hle : conjClosure S.V3 H ≤ S.L1) : G22Conclusion S.V3 (fsuV1 T V) S.T5 H := by
  have hg := (S.hypF91_F4 hNS h13315 h1356two hH).almostSpecialHyp.g22
  refine ⟨hg.one, hg.two, ⟨fun u hu => ⟨hg.three.1 hu, ?_⟩, S.T5_le_T.trans hg.three.2⟩, hg.four⟩
  have huN : u ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le_L (hle hu))
  exact S.mem_fix5V.2 ⟨huN, (S.rho_L1 (g := ⟨u, huN⟩) (hle hu)).2.1⟩

theorem g248_L5_F4 (hG : StmtG248CoreProv)
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : ¬ IsHatA6 L) {x : G}
    (hx : x ∈ S.L5) (hxN : x ∉ Subgroup.normalizer (fsuV1 T V : Set G)) :
    conjClosure S.V3 H ⊔ rconj (conjClosure S.V3 H) x = S.L5 ∧ IsShort2 S.L5 ∧
      IsAltType S.L5 5 ∧ pCoreOf 2 S.L5 = V ∧ conjClosure S.V3 H = pCoreOf 2 S.L1 ∧
      IsQ8Sq ↥(conjClosure S.V3 H) := by
  have hle := S.UH_le_L1_six_F4 hNS h13315 h1356two hH hn hna
  have hA := S.toA5Sit_F4 hNS h13315 h1356two hH hna
  have hV1 : fsuV1 T V ≠ ⊥ := fun h => by
    have := S.card_V1
    rw [h, Subgroup.card_bot] at this
    omega
  have hV1U : fsuV1 T V ≤ conjClosure S.V3 H :=
    (S.V1_le_V2.trans S.V2_le_V3).trans (le_conjClosure _ _)
  have hcomm : ⁅conjClosure S.V3 H, lOne S.L5 (fsuV1 T V)⁆ ⊔ fsuV1 T V = conjClosure S.V3 H := by
    rw [S.lOne_L5, hA.commutator_UH_L1 hn]
    exact sup_eq_left.2 hV1U
  have hO2 : pCoreOf 2 (lOne S.L5 (fsuV1 T V)) ≤ pCoreOf 2 H := by
    rw [S.lOne_L5]
    exact hA.pCoreOf_L1_le hn
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hG G S.V3 (fsuV1 T V) S.L5 S.T5 H
    (F7.isElemAbelian_mono S.elemAbelian_V S.V3_le_V) hV1 (S.V1_le_V2.trans S.V2_le_V3)
    S.oTwoUpper_L5 (S.V3_le_V.trans S.V_le_T5) S.T5_le_NV1 S.T5_le_NV3 S.T5_le_normalizer_L5
    (S.isSylowTwoOf_T5 hhat) (S.H_le_NV1 hH) (S.lOne_T5_le_H hH) (S.charTwo_H hH)
    (S.isA5ModuleFor_L5 hhat) S.card_V1 (S.V3_eq_commutator_L5 hhat)
    (S.not_UH_le_pCoreOf_L5T5 hhat hna) (S.T5_le_H hH) S.isPGroup_T5
    (S.g22_T5_F4 hNS h13315 h1356two hH hle) hcomm hO2 x hx hxN
  rw [S.conjClosure_V1_L5 hhat] at h4
  rw [S.lOne_L5] at h5
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem obl_five_F4 (hG : StmtG248CoreProv)
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : ¬ IsHatA6 L)
    {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hlT : (l : G) ∉ S.L1 ⊔ T)
    (h5 : S.frame.ρ l 5 = 5) :
    S.KH H l = S.L5 ∧ IsShort2 S.L5 ∧ IsAltType S.L5 5 ∧ pCoreOf 2 S.L5 = V ∧
      conjClosure S.V3 H = pCoreOf 2 S.L1 ∧ IsQ8Sq ↥(conjClosure S.V3 H) := by
  have hs : Perm.sign (S.frame.ρ l) = 1 :=
    Perm.mem_alternatingGroup.1 ((S.frame.image_L _).1 ⟨l, hlL, rfl⟩)
  obtain ⟨x, hxL5, hρx⟩ := S.exists_L5_rho hhat h5 hs
  have hxN : (x : G) ∉ Subgroup.normalizer (fsuV1 T V : Set G) := by
    intro hxN
    have hfix := S.fix_e0123 x (S.conj_z_of_normalizes hxN)
    rw [hρx] at hfix
    exact hlT (S.mem_L1T_of_fix hhat hlL h5 (fix4_of_e0123 _ hfix h5))
  obtain ⟨hK, hsh, halt, hO2, hU, hQ8⟩ :=
    S.g248_L5_F4 hG hNS h13315 h1356two hH hn hna hhat hxL5 hxN

  have hc : S.frame.ρ (x⁻¹ * l) = 1 := by rw [map_mul, map_inv, hρx, inv_mul_cancel]
  have hcT5 : ((x⁻¹ * l : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ S.T5 :=
    S.inf_centralizer_le_T5 hhat ⟨L.mul_mem (L.inv_mem (S.L5_le_L hxL5)) hlL,
      (S.rho_eq_one_iff _).1 hc⟩
  set c : G := ((x⁻¹ * l : ↥(Subgroup.normalizer (V : Set G))) : G) with hcdef
  have hlc : (l : G) = x * c := by
    rw [hcdef]
    simp
  have hcH : c⁻¹ ∈ H := H.inv_mem (S.T5_le_H hH hcT5)
  have hUc : conjSub c⁻¹ (conjClosure S.V3 H) = conjClosure S.V3 H :=
    conjSub_eq_self_of_normalizes (le_normalizer_conjClosure _ _ hcH)
  have hL5c : conjSub c⁻¹ S.L5 = S.L5 :=
    conjSub_eq_self_of_normalizes (S.T5_le_normalizer_L5 (S.T5.inv_mem hcT5))
  have hKH : S.KH H l = S.L5 := by
    have e1 : S.KH H l = conjClosure S.V3 H ⊔ conjSub (l : G)⁻¹ (conjClosure S.V3 H) := rfl
    have e2 : rconj (conjClosure S.V3 H) x = conjSub (x : G)⁻¹ (conjClosure S.V3 H) := rfl
    rw [e2] at hK
    rw [e1, hlc, mul_inv_rev, conjSub_mul]
    nth_rewrite 1 [← hUc]
    rw [← conjSub_sup, hK, hL5c]
  exact ⟨hKH, hsh, halt, hO2, hU, hQ8⟩

theorem obl_four_F4 (hG : StmtG248CoreProv)
    (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
    {H : Subgroup G} (hH : H ∈ S.Hz) (hn : H ≤ Subgroup.normalizer (S.L1 : Set G))
    (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H)) (hhat : ¬ IsHatA6 L)
    {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hlT : (l : G) ∉ S.L1 ⊔ T)
    (h4 : S.frame.ρ l 4 = 4) :
    oTwoRes (pCoreOf 2 (L ⊔ T) ⊔ S.KH H l) = S.KH H l ∧ IsShort2 (S.KH H l) ∧
      IsAltType (S.KH H l) 5 ∧ pCoreOf 2 (S.KH H l) = V ∧
      conjClosure S.V3 H = pCoreOf 2 S.L1 ∧ IsQ8Sq ↥(conjClosure S.V3 H) := by
  obtain ⟨t, htT, hρt⟩ :=
    S.frame.DA_T _ s0145_facts.1 (Perm.mem_alternatingGroup.2 s0145_facts.2.1)
  have hl'L : ((t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (S.T_le_NL htT) l).mp hlL
  have h5 : S.frame.ρ (t * l * t⁻¹) 5 = 5 := by
    rw [map_mul, map_mul, map_inv, hρt, Perm.mul_apply, Perm.mul_apply, s0145_apply.2, h4,
      s0145_apply.1]
  have htT' : (t : G) ∈ S.L1 ⊔ T := Subgroup.mem_sup_right htT
  have hl'T : ((t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) ∉ S.L1 ⊔ T := by
    intro h
    apply hlT
    have e : (l : G) =
        (t : G)⁻¹ * ((t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * t := by
      push_cast
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ htT') h) htT'
  obtain ⟨hKH, hsh, halt, hO2, hU, hQ8⟩ :=
    S.obl_five_F4 hG hNS h13315 h1356two hH hn hna hhat hl'L hl'T h5
  have htH : (t : G) ∈ H := (le_sup_right.trans hH.1.1) htT
  have hUt : ∀ g ∈ H, conjSub g (conjClosure S.V3 H) = conjClosure S.V3 H := fun g hg =>
    conjSub_eq_self_of_normalizes (le_normalizer_conjClosure _ _ hg)
  have hconj : S.KH H (t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) =
      conjSub (t : G) (S.KH H l) := by
    have e1 : ∀ k : G, S.KH H k = conjClosure S.V3 H ⊔ conjSub k⁻¹ (conjClosure S.V3 H) :=
      fun k => rfl
    rw [e1, e1, conjSub_sup, hUt _ htH]
    congr 1
    have e2 : ((t * l * t⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ =
        (t : G) * ((l : G)⁻¹ * (t : G)⁻¹) := by
      push_cast
      group
    rw [e2, conjSub_mul, conjSub_mul, hUt _ (H.inv_mem htH)]
  rw [hconj] at hKH
  have hK : S.KH H l = conjSub (t : G)⁻¹ S.L5 := by
    rw [← hKH, conjSub_conjSub_inv]
  have htQ : conjSub (t : G)⁻¹ (pCoreOf 2 (L ⊔ T)) = pCoreOf 2 (L ⊔ T) :=
    conjSub_eq_self_of_normalizes (le_normalizer_pCoreOf 2 _
      ((le_sup_right : T ≤ L ⊔ T) (T.inv_mem htT)))
  have htV : conjSub (t : G)⁻¹ V = V :=
    conjSub_eq_self_of_normalizes (S.frame.T_le (T.inv_mem htT))
  refine ⟨?_, ?_, ?_, ?_, hU, hQ8⟩
  · rw [hK]
    nth_rewrite 1 [← htQ]
    rw [← conjSub_sup, ← conjSub_oTwoRes, S.oTwoRes_pCoreOf_sup_L5]
  · rw [hK]
    exact (Lin2.isShort2_map_equiv_iff (MulAut.conj (t : G)⁻¹) S.L5).2 hsh
  · rw [hK]
    exact L238.IsAltType.map_equiv halt (MulAut.conj (t : G)⁻¹)
  · rw [hK, pCoreOf_conjSub, hO2, htV]

end Setting4

theorem obl13_5_14Six_of_F4 (hG : StmtG248CoreProv)
    (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4) : Obl13_5_14Six_F4 := by
  intro G _ _ T L V S H l hNS hH hn hna hhat hl hlL hlT h45
  rcases h45 with h4 | h5
  · exact S.obl_four_F4 hG hNS h13315 h1356two hH hn hna hhat (l := ⟨l, hl⟩) hlL hlT h4
  · obtain ⟨hKH, hsh, halt, hO2, hU, hQ8⟩ :=
      S.obl_five_F4 hG hNS h13315 h1356two hH hn hna hhat (l := ⟨l, hl⟩) hlL hlT h5
    have hKH' : conjClosure S.V3 H ⊔ CFSG.conjugate (conjClosure S.V3 H) l = S.L5 := hKH
    rw [hKH']
    exact ⟨S.oTwoRes_pCoreOf_sup_L5, hsh, halt, hO2, hU, hQ8⟩

end CFSG.Quasithin.H13.A6
