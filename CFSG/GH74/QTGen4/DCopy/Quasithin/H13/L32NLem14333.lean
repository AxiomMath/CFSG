module

public import CFSG.Quasithin.H13.L32NLem14333
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NItems143c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem14333d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits

namespace L14333

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Ctx_F4
open CFSG.Quasithin.H13.L14333.Ctx_F4

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx_F4 G T L V V₂ K g a z b d x D)
include c

theorem fsuU_eq_pCoreOf_of_le_F4 (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V))
    (hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V)) (hTL : T ≤ L) :
    fsuU T V = pCoreOf 2 (l32nH T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, S⟩ := c.setting
  obtain ⟨-, hPcard⟩ := c.pCoreOf_eq_F4 hyp
  have hT2 := c.ctx.T2
  obtain ⟨m, hm⟩ := hT2.exists_card_eq

  have hTG := c.ctx.hyp.fsu.sylow
  have hoddL : Odd (T.relIndex L) := by
    have h := Subgroup.relIndex_mul_index hTL
    have hodd : Odd T.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hTG.2)
    rw [← h] at hodd
    exact Nat.Odd.of_mul_left hodd
  have hL := Subgroup.relIndex_mul_card T L
  rw [inf_eq_left.mpr hTL, S.card_L_F4, hPcard, hm] at hL
  have hm9 : m = 9 := by
    have h' : 2 ^ m * T.relIndex L = 2 ^ 9 * 21 :=
      calc 2 ^ m * T.relIndex L = T.relIndex L * 2 ^ m := mul_comm _ _
        _ = 168 * 64 := hL
        _ = 2 ^ 9 * 21 := by norm_num
    exact two_pow_eq_of_mul_odd hoddL (by decide) h'

  obtain ⟨q, hq⟩ := (pCoreOf_isPGroup 2 (l32nH T V)).exists_card_eq
  have hH : Nat.card ↥(l32nH T V) = Nat.card ↥(pCoreOf 2 (l32nH T V)) * 120 := by
    have h := Subgroup.card_ker_mul_card_range (imgHom D)
    rw [imgHom_ker, ← c.q_eq, MonoidHom.range_eq_top.mpr (imgHom_surjective D), Subgroup.card_top,
      card_img_l32nH c.ii] at h
    rw [← h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 _)).toEquiv]
  have hoddH : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hTS.2.2)
  have hHT := Subgroup.relIndex_mul_card T (l32nH T V)
  rw [inf_eq_left.mpr hTS.1, hm, hm9, hH, hq] at hHT
  have hq6 : q + 3 = 9 := by
    have h' : 2 ^ (q + 3) * 15 = 2 ^ 9 * T.relIndex (l32nH T V) :=
      calc 2 ^ (q + 3) * 15 = 2 ^ q * 120 := by rw [pow_add]; ring
        _ = T.relIndex (l32nH T V) * 2 ^ 9 := hHT.symm
        _ = 2 ^ 9 * T.relIndex (l32nH T V) := mul_comm _ _
    exact two_pow_eq_of_mul_odd (by decide) hoddH h'
  have hQ64 : Nat.card ↥(pCoreOf 2 (l32nH T V)) = 64 := by
    rw [hq, show q = 6 by omega]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge (fsuU_le_pCoreOf c.ctx) (by rw [hQ64, c.card_U_F4])

end Ctx_F4

end L14333

open L14333 in

theorem lemma14333_of_inputs_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h1222 : Stmt12_2_2_F4)
    (h12213 : Stmt12_2_13_F4) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h1288 : Lemma12_8_8_two_F4) (h12884 : Lemma12_8_8_four_F4) (h12810 : Lemma12_8_10_F4)
    (h12811 : Lemma12_8_11_F4) (h12811h : Lemma12_8_11_hat_F4) (h12812 : Lemma12_8_12_two_F4)
    (h12813 : Lemma12_8_13_F4) (h14323 : Lemma14323Rest_F4) (h14324 : Lemma14324One_F4)
    (h14331 : Lemma14331One_F4) (h14333 : Lemma14333MEqL_F4) (hKG22 : KGG22PointStab)
    (hKGr : KGG22Rank) (hKGq : KGSp4Quad) (hKGl : KGSp4Line) (hKGL24 : KGL24Quad) :
    Lemma14333_F4 := by
  intro G _ _ T L V h hlt
  obtain ⟨V₂, K, g, a, z, b, d, x, D, c⟩ := exists_ctx_F4 h1332 h1334 h1222 h12213 h37 h38 h39
    h1288 h12810 h12811 h12811h h12812 h12813 h14323 h14324 h14331 hKG22 hKGr hKGq
    hKGl hKGL24 h hlt
  have hyp := (h12884 G T L V 3 (fsuV1 T V) V₂ c.ctx.setting le_rfl).2
  have hK := c.eq_oTwoUpper_F4
  have hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V) :=
    h.isSylowTwoOf_l32nH_F4 (stmtL32NModule_of_inputs_F4 h1332 h1334)
  have hM := h14333 G T L V h hlt
  have hTL : T ≤ L := hM ▸ c.T_le_normL_F4
  exact ⟨(c.pCoreOf_eq_F4 hyp).1, c.isZ4Cube_F4 hyp, c.isXSectionIso₂_F4 hyp,
    by rw [← hK, c.pCoreOf_K_eq_F4 hyp], hK ▸ c.isSylowTwoOf_PU_F4 hyp, hM,
    (C1Pack12.oTwoUpper_sup_eq_of_sylow hTS).symm, c.fsuU_eq_pCoreOf_of_le_F4 hyp hTS hTL⟩

end CFSG.Quasithin.H13
