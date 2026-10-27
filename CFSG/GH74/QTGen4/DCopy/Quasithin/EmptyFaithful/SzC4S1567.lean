module

public import CFSG.Quasithin.EmptyFaithful.SzC4S1567
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Background.S1567V2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Matrix commutatorElement

theorem input15368PsiL3Loc_of_c134_corr_F4 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hMS : MS93.AS_C_1_34_corr_F4) (hcase3 : Case3Excl) : Input15368PsiL3Loc_F4 := by
  intro G _ _ T Mc M V₁ V₂ E t s c r45 r46 r49 r50 ld r66 r67 gl r68 hL3
  have k : Ctx67 G T Mc M V₁ V₂ E t :=
    ⟨c, r45, r46, r49, r50, ld, r66, ⟨r67.sylow_GE, r67.baum_le, r67.CGS_le⟩⟩
  obtain ⟨L, hL, hN, hprod, ⟨α, hαs, hαk⟩, hMSP⟩ :=
    S1567.exists_L_isMSPair h11 h113 k r67 gl r68 hL3
  have hLG : L ≤ G0_153 T Mc M E s := le_of_mem_cComp hL
  have hn : ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ IsModO2Surj L α :=
    ⟨1, ZMod 2, inferInstance, inferInstance, α, by simp, ⟨hαs, hαk⟩⟩
  obtain ⟨i, hi⟩ := hMS G (G0_153 T Mc M E s) (TE153 T E) L hMSP hL hprod hn
  have hO : oTwoUpper (G0_153 T Mc M E s) ≤ L :=
    S1567.oTwoUpper_G0_le_of_mul_TE k hN hLG hprod
  have hle : Nat.card ↥⁅pCoreOf 2 (G0_153 T Mc M E s), oTwoUpper (G0_153 T Mc M E s)⁆ ≤
      Nat.card ↥(c134Q (G0_153 T Mc M E s) L) :=
    Subgroup.card_le_of_le (Subgroup.commutator_mono le_rfl hO)
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact hi.elim
  · have h1 : IsC134Case1 (G0_153 T Mc M E s) (TE153 T E) L := hi
    have := S1567.card_c134Q_of_case1 α hαs hαk h1
    exact hle.trans (by rw [this]; norm_num)
  · have h2 : IsC134Case2 (G0_153 T Mc M E s) (TE153 T E) L := hi
    have := S1567.card_c134Q_of_case2 α hαs hαk h2
    exact hle.trans (by rw [this]; norm_num)
  · have h3 : IsC134Case3 (G0_153 T Mc M E s) (TE153 T E) L := hi
    exact (hcase3 G T Mc M V₁ V₂ E t s L c r45 r46 r49 r50 ld r66 r67 gl r68 hL3 hL hN hprod h3).elim
  · have h4 : MS93.IsC134Case4Corr (G0_153 T Mc M E s) (TE153 T E) L := hi
    exact (S1567.false_of_c134Case4_corr h113 k r67 gl r68 hLG hO α hαs hαk h4).elim
  · have h5 : IsC134Case5 (G0_153 T Mc M E s) (TE153 T E) L := hi
    have := S1567.card_c134Q_of_case5 h5
    exact hle.trans (by rw [this]; norm_num)
  · exact hi.elim

theorem input15368PsiL3Loc_of_ms_corr_F4 (h11 : StageLemma14111) (h113 : StageLemma14113)
    (hMS : MS93.AS_C_1_34_corr_F4) : Input15368PsiL3Loc_F4 :=
  input15368PsiL3Loc_of_c134_corr_F4 h11 h113 hMS (S1567.case3Excl h113)

end CFSG.Quasithin
