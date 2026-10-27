module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6S1515c
public import CFSG.Quasithin.H13.A5Sit15h

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

namespace Setting4

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section Data

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15_F4) (h1356two : Input1356Two_F4)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hhat : ¬ IsHatA6 L)
  (hn : H ≤ Subgroup.normalizer (S.L1 : Set G)) (hna : ¬ IsElemAbelian 2 (conjClosure S.V3 H))
  {l : ↥(Subgroup.normalizer (V : Set G))} (hlL : (l : G) ∈ L) (hl : S.frame.ρ l = lK)
  (hobl : Obl13_5_14Six_F4) (hctk : Input13515CTK_F4)
include hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk

theorem H_eq_G1_six_S6_F4 (hTL : ¬ T ≤ L) : H = S.G1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := S.nonempty_pf15_six_F4 hNS h13315 h1356two hH hn hna hhat hlL hl hobl
  have hQ := S.card_Q_six_F4 hNS h13315 h1356two hH hhat hn hna hlL hl hobl hctk hTL
  have h36 := S.card_range_six_F4 hNS h13315 h1356two hH hhat hna P
  have hz := S.C_z_eq_F4 hNS h13315 h1356two hH hna P
  have hF1 := S.hypF91_F4 hNS h13315 h1356two (S.G1_mem_Hz hH)
  have hHG1 : H ≤ S.G1 := hH.2.1
  have hG1z : S.G1 ≤ Subgroup.centralizer ({P.C.z} : Set G) := by
    rw [hz]
    exact le_rfl
  set A := S.toA5Sit_F4 hNS h13315 h1356two hH hna

  have hQ1Q : pCoreOf 2 S.G1 ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2
      ((pCoreOf_two_le_of_isSylowTwoOf hF1.sylow_H).trans A.T_le_H)
      (hHG1.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  have hUQ1 : conjClosure S.V3 H ≤ pCoreOf 2 S.G1 :=
    (conjClosure_mono le_rfl hHG1).trans hF1.conjClosure_Vp_le_pCoreOf

  have hUQ : (conjClosure S.V3 H).relIndex (pCoreOf 2 H) = 2 := by
    have h := Subgroup.relIndex_mul_card (conjClosure S.V3 H) (pCoreOf 2 H)
    rw [inf_eq_left.2 A.U_le_Q, P.card_U, hQ] at h
    omega
  have h := Subgroup.relIndex_mul_relIndex (conjClosure S.V3 H) (pCoreOf 2 S.G1)
    (pCoreOf 2 H) hUQ1 hQ1Q
  rw [hUQ] at h
  rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro_left _ h) with h1 | h1
  ·
    have hQ1 : pCoreOf 2 S.G1 = pCoreOf 2 H :=
      le_antisymm hQ1Q (Subgroup.relIndex_eq_one.1 h1)
    exact P.H_eq_of_Q hQ h36 hF1 hHG1 hG1z hQ1
  ·
    rw [h1] at h
    have h2 : (conjClosure S.V3 H).relIndex (pCoreOf 2 S.G1) = 1 := by omega
    have hQ1 : pCoreOf 2 S.G1 = conjClosure S.V3 H :=
      le_antisymm (Subgroup.relIndex_eq_one.1 h2) hUQ1
    exact P.H_eq_of_U h36 hF1 hHG1 hG1z hQ1

end Data

end Setting4

end CFSG.Quasithin.H13.A6
