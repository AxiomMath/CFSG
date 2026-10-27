module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526Tr
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2B
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalProp526Rk2C

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.GH74.QTGen4.DSGen4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem stmt5_2_6_L2K_rank2_of_F4
    (h331 : Stmt3_3_1_F4) (hRL : RankOneListedFacts.{0}) (hF11 : StmtF11_5_2_F4)
    (hbor : Stmt5_2_6_borel_F4) (h524 : Stmt5_2_4_F4) (h510 : Stmt5_1_10_F4)
    (h38 : Vol2Native.A38ForSQTKCat) (hU3 : FactU3Cover) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h512 : Stmt5_1_2_F4) : Stmt5_2_6_L2K_rank2_F4 := by
  intro G _ _ T M L V H B D L₂ n hyp hnb ⟨P, hP, hL₂P⟩ hloc
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB₂ : IsBlock2 L₂ L₂ := hloc.1.2.2.1
  have hSL₂ : sec52S M H ≤ L₂ := hloc.2.1.2.2.2
  obtain ⟨K₁, hK₁, hKeq, hcase⟩ := hyp.choice
  rcases hcase with ⟨hbend, hL₂K₁⟩ | ⟨-, hK₁K, -⟩
  · subst hL₂K₁
    have hL₂K := hyp.eq_oTwoUpper_of_bender_F4 h38 hRL hU3 h510 h524 hK₁ hKeq hbend (Or.inl hSL₂)
    exact hnb (hL₂K ▸ hbend)
  subst hK₁K
  obtain ⟨k, hk, htype, hpsl, hL₂q, hperf, hNR₀, hR₀Q, hR₀L, hcardR₀⟩ :=
    Sec526.rank2_facts_F4 h510 hyp hK₁ hnb hP hL₂P
  set R₀ := pCoreOf 2 (oTwoUpper H) ⊓ L₂ with hR₀def
  obtain ⟨hv3, hv4⟩ := Sec526.factorization_two_of_rank2 (X := O2Q (oTwoUpper H)) hk
  have hbig : Nat.card R₀ * 2 ^ (2 * k) ≤ Nat.card (pCoreOf 2 L₂) := by
    have hv : 3 * k ≤ (Nat.card (O2Q (oTwoUpper H))).factorization 2 := by
      rcases htype with h3 | h4
      · rw [hv3 h3]
      · rw [hv4 h4]
        omega
    have hpow : 2 ^ (2 * k) * 2 ^ k ≤ 2 ^ (Nat.card (O2Q (oTwoUpper H))).factorization 2 := by
      rw [← pow_add]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2k : 0 < 2 ^ k := pow_pos (by norm_num) k
    have := Nat.mul_le_mul_left (Nat.card R₀) hpow
    rw [hcardR₀, ← mul_assoc] at this
    exact Nat.le_of_mul_le_mul_right this h2k
  exact Sec526.not_isShort2_of_card hk hperf hL₂q hR₀Q hNR₀ hR₀L hbig hB₂.1

end CFSG.Quasithin.H13
