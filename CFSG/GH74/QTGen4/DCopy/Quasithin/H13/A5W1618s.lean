module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.A5W1618s
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Final
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1326
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S136h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618l
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618o
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618p
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1618r
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Y1367b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.Stmt331F4

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped IsMulCommutative

theorem lemma13618Four_of_F4
    (h126 : TheoremC126)
    (h23 : E2.E23Statement) (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h56 : AsB56)
    (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) : Lemma13618Four_F4 := by
  intro G _ _ T L V S hH K hK hT F _ _ hF4 ⟨e⟩
  have hF := hH.hF
  have hR := S.isTwoReducedIn_WK_F4 h1222 h517 hF hK.1 hT
  have : IsMulCommutative ↥(S.WK K) := hR.2.2.1.1
  have hKW : K ≤ Subgroup.normalizer ((S.WK K : Subgroup G) : Set G) :=
    (le_sup_left.trans le_sup_left).trans hR.2.1

  obtain ⟨G₂, U, C, K', _, _, π, hK'4, hsup, -, hc, hπ, hCfix, hUV⟩ :=
    S.nat_of_sl2_four_F4 h1222 h517 h56 hH hK hT hF4 e

  obtain ⟨K₀, M, hK₀K, hK₀, hTK₀, hK₀im, hmp⟩ :=
    S.exists_minParabolic_of_sl2_four_F4 h1222 h517 hF hK hT hF4 e
  have hz := S.not_le_centralizer_z_of_plus_eq_F4 h1222 h517 hF hK hT hK₀im
  obtain ⟨hblk, hcases⟩ := S.isChi0Block_of_minParabolic_F4 h126 h1222 h517 h132two h132fsu
    h132A5 h331 h1327 h37 h39 hF (hK₀K.trans hK.1) hK₀ hTK₀ hz hmp
  obtain ⟨hV, hred, hE⟩ := S.e23_cases_F4 h23 h1222 h517 hF hK hT hK₀K hK₀ hK₀im hmp
  rcases hcases with ⟨n, hn, hlin⟩ | h5
  · rcases hE with hnat | ha5
    ·
      have hcharF : CharP F 2 :=
        R3c.charP_two_of_natCard_eq_two_pow (f := 2) (by rw [hF4]; norm_num)
      have hsimp : IsSimpleGroup ↥(S.plus K) :=
        @MulEquiv.isSimpleGroup _ _ _ _ (NQRigid.isSimpleGroup_statedSL_two_charTwo hF4.ge) e
      have h3 : 3 ∣ Nat.card ↥(S.plus K) := by
        rw [Nat.card_congr e.toEquiv, R3c.card_statedSL_two_pow (n := 2) (by rw [hF4]; norm_num)]
        norm_num
      have hNQ : K₀ ⊓ Subgroup.centralizer ((S.WK K : Subgroup G) : Set G) ≤ S.Tv := by
        rw [S.inf_centralizer_WK_eq (hK₀K.trans hKW) hK₀im hsimp h3 hn hlin]
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact le_of_isPGroup_of_le_normalizer hmp.isSylow
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀)
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₀).trans le_sup_left)
          (hTK₀.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀))
      obtain ⟨x, hxK₀, hxB, hxW, hx3⟩ := S.exists_mem_normalizer_baum_F4 h1222 h517 hF hK hT hF4 e
        hK₀K hK₀ hTK₀ hK₀im hmp hNQ hV hred hnat
      exact S.false_of_lin2Block_of_baum_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h39 hH hK
        hT hF4 e hK₀K hK₀ hTK₀ hK₀im hblk.1 hn hlin hxK₀ hxB hxW hx3
    ·
      exact S.false_of_a5Case_of_natural_F4 h1222 h517 hF hK hT hF4 e hK₀K hK₀ hTK₀ hK₀im hV ha5
        hsup hc
  ·
    exact S.false_of_altBlock_of_natural_F4 h1222 h517 hF hK hT hK₀K hK₀ hTK₀ hK₀im hblk.1.1 h5 hK'4
      hπ hCfix hUV

theorem lemma13618_of_inputs_F4
    (h126 : TheoremC126)
    (h23 : E2.E23Statement) (h1222 : Stmt12_2_2_F4) (h517 : Stmt5_1_7_one_F4) (h56 : AsB56)
    (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat) : Lemma13618_F4 :=
  lemma13618_of_F4 h1222 h517 h56 (lemma13618Four_of_F4 h126 h23 h1222 h517 h56 h132two h132fsu h132A5
    h331 h1327 h37 h39)

end CFSG.Quasithin.H13.A5
