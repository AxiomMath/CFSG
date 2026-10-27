module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporHeWit
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporModel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatHe
import CFSG.Blueprint.NativeSporadic
public import Certificates.Certificate3168
public import Certificates.Certificate4033
public import Certificates.Certificate4090
public import Certificates.Certificate4141

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.HePairs

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.Ch1.SporLat.He
  CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Blueprint
open CFSG.Open (pCoreOf)

theorem he_J7
    : 7 < heCtx.J := by rw [he_J]; norm_num

theorem he_J2
    : 2 < heCtx.J := by rw [he_J]; norm_num

theorem he_lbl_size
    {j : ℕ} (hj : j < 11) :
    heCtx.D.Om[j]!.lbl.size = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! :=
  he_Om_size j hj

theorem he_letters7
    : heCtx.D.sTabs ++ heCtx.D.mt[7]! = heL7 := by
  have hsT : heCtx.D.sTabs = heSTabsW := by
    rw [← heCtx.hsg]
    exact he_sGens.1
  have hmt : heCtx.D.mt[7]! = (heMwLit[7]!).map (fun w => wordTabA #[heTa, heTb] 8330 w) := by
    have h := (heCtx.membersOK.2.2.2.2 7 he_J7).2.1
    have hmw : heCtx.D.mw = heMwLit := he_mw_lit
    rw [hmw] at h
    exact h
  rw [hsT, hmt]
  rfl

theorem he_letters2
    : heCtx.D.sTabs ++ heCtx.D.mt[2]! = heL2 := by
  have hsT : heCtx.D.sTabs = heSTabsW := by
    rw [← heCtx.hsg]
    exact he_sGens.1
  have hmt : heCtx.D.mt[2]! = (heMwLit[2]!).map (fun w => wordTabA #[heTa, heTb] 8330 w) := by
    have h := (heCtx.membersOK.2.2.2.2 2 he_J2).2.1
    have hmw : heCtx.D.mw = heMwLit := he_mw_lit
    rw [hmw] at h
    exact h
  rw [hsT, hmt]
  rfl

theorem he_goodLocal_Y7
    : GoodLocal (heCtx.Y 7) := by
  have hcard : heCtx.D.Om[7]!.lbl.size = 3 * 7 := by rw [he_lbl_size (by norm_num)]; rfl
  have hodd : heCtx.D.Om[7]!.lbl.size % 2 = 1 := by rw [hcard]
  have h3 : Wit3Ok 8330 heCtx.A.act (heCtx.D.sTabs ++ heCtx.D.mt[7]!) (heCtx.Λ 7) b7a q7a q7b := by
    rw [he_letters7]
    exact he_wit_cert.2.1.mono_lbls he_labels7
  have hP : WitPOk 8330 heCtx.A.act (heCtx.D.sTabs ++ heCtx.D.mt[7]!) (heCtx.Λ 7) 7 b7p q7p := by
    rw [he_letters7]
    exact he_wit_cert.2.2.mono_lbls he_labels7
  exact heCtx.goodLocal_of_wit he_J7 hodd he_base_lt he_base_property (p := 7) (by norm_num)
    (by norm_num) hcard h3 hP

theorem he_o2_Y2
    : Nat.card ↥(pCoreOf 2 (heCtx.Y 2)) = 256 := by
  have h1 := (heCtx.memStmt_default he_o2OK he_J2).2.1
  have h2 : heOtK[2]!.lbl.size = 4 := by rw [he_Ot_size 2 (by norm_num)]; rfl
  have h3 : (defaultRow heCtx.k heCtx.D heOtK 2).o2 = 256 := by
    show 2 ^ 10 / heOtK[2]!.lbl.size = 256
    rw [h2]
    norm_num
  exact h1.trans h3

theorem he_goodLocal_Y2
    : GoodLocal (heCtx.Y 2) := by
  have hcard : heCtx.D.Om[2]!.lbl.size = 9 := by rw [he_lbl_size (by norm_num)]; rfl
  have hodd : heCtx.D.Om[2]!.lbl.size % 2 = 1 := by rw [hcard]
  have hO2 : 2 ^ heCtx.k * 9 < 60 * Nat.card ↥(pCoreOf 2 (heCtx.Y 2)) := by
    rw [he_o2_Y2]
    have hk : heCtx.k = 10 := rfl
    rw [hk]
    norm_num
  have h : CntOk 8330 heCtx.A.act (heCtx.D.sTabs ++ heCtx.D.mt[2]!) (heCtx.Λ 2) r2a r2b q2s := by
    rw [he_letters2]
    exact he_wit_cert.1.mono_lbls he_labels2
  exact heCtx.goodLocal_of_cnt_nine he_J2 hodd he_base_lt he_base_property hcard hO2 h

theorem he_card_vals
    {j : ℕ} (hj : j < 11) :
    Nat.card (heCtx.Y j) = #[1, 3, 9, 135, 135, 9, 3, 21, 3, 9, 3][j]! * 1024 :=
  he_member_card j hj

theorem he_localPair
    : LocalPair CFSG.Sporadic.He.J := by
  have hcard : Nat.card CFSG.Sporadic.He.J = 2 ^ 10 * 3935925 := he_card
  refine localPair_of_ctx_pair heCtx he_S_sylow 7 2 3 4 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    he_goodLocal_Y7 he_goodLocal_Y2
  · intro j hj h
    rw [he_J] at hj
    rw [he_card_vals hj, he_card_vals (by norm_num : 7 < 11)] at h
    interval_cases j <;> simp at h ⊢
  · rw [he_card_vals (by norm_num : 4 < 11), he_card_vals (by norm_num : 3 < 11)]
    rfl
  · intro j hj h
    rw [he_J] at hj
    rw [he_card_vals hj, he_card_vals (by norm_num : 3 < 11)] at h
    interval_cases j <;> simp at h ⊢
  · exact (he_Y_le_iff (by norm_num : 2 < 11) (by norm_num : 3 < 11)).2 (by decide)
  · exact (he_Y_le_iff (by norm_num : 2 < 11) (by norm_num : 4 < 11)).2 (by decide)
  · intro j hj h h3 h4
    rw [he_J] at hj
    rw [he_card_vals hj, he_card_vals (by norm_num : 2 < 11)] at h
    have h3' := (he_Y_le_iff hj (by norm_num : 3 < 11)).1 h3
    have h4' := (he_Y_le_iff hj (by norm_num : 4 < 11)).1 h4
    interval_cases j <;> simp_all <;> revert h3' h4' <;> decide
  · rw [hcard, he_card_vals (by norm_num : 7 < 11)]
    norm_num
  · rw [hcard, he_card_vals (by norm_num : 3 < 11)]
    norm_num
  · rw [hcard, he_card_vals (by norm_num : 2 < 11)]
    norm_num
  · intro j hj ⟨h1, h2⟩
    rw [he_J] at hj
    have d1 := Subgroup.card_dvd_of_le h1
    have d2 := Subgroup.card_dvd_of_le h2
    rw [he_card_vals (by norm_num : 7 < 11), he_card_vals hj] at d1
    rw [he_card_vals (by norm_num : 2 < 11), he_card_vals hj] at d2
    interval_cases j <;> simp at d1 d2

theorem pairsFor_He
    : PairsFor (TypeSporadic .He) := by
  refine pairsFor_of_localPair_equiv (s := .He) (Γ := ↥CFSG.Sporadic.He.J) ?_ he_localPair
  exact CFSG.Sporadic.He.heEquivJ

end CFSG.QuasithinUnique.Vol2Native.L239.HePairs
