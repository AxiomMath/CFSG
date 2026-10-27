module

public import CFSG.Quasithin.H13.L32A728
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A706f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk7

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem card_dvd_three_of_isPGroup_F4 {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}
    (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4)
    (h1334 : A6.Stmt13_3_4_F4) (h3 : IsPGroup 3 ↥(modO2Image H (l1 T L V))) :
    Nat.card ↥(modO2Image H (l1 T L V)) ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1

  have hdvd : Nat.card ↥(modO2Image H (l1 T L V)) ∣ Nat.card ↥(l1 T L V) := by
    have h1 := Subgroup.card_map_dvd ((l1 T L V).subgroupOf H)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl1H).toEquiv] at h1
  have hidx := (M76.relIndex_l1_T_F4 S h1222 h1332 h1334).1
  have hcard : Nat.card ↥(l1 T L V) = Nat.card ↥(pCoreOf 2 (l1 T L V)) * 3 := by
    have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 (l1 T L V)) (K := l1 T L V)
    rw [inf_eq_left.mpr (pCoreOf_le 2 (l1 T L V)), hidx] at h1
    rw [← h1, mul_comm]
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 (l1 T L V)).exists_card_eq
  rw [hcard, ha, hk] at hdvd
  rw [hk]
  have hcop : Nat.Coprime (3 ^ k) (2 ^ a) := Nat.Coprime.pow k a (by decide)
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem lemma14_7_28_of_F4 (h27 : Lemma14_7_27_F4) (h76 : Lemma14_7_6_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) : Lemma14_7_28_F4 := by
  intro G _ _ T L V H S
  have hF := h76 G T L V H S
  have hP : Nat.card ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) ∣ 3 := by
    rcases h27 G T L V H S with h | h
    · rw [h, Subgroup.card_bot]
      exact one_dvd 3
    · have h3 : IsPGroup 3 ↥(modO2Image H (l1 T L V)) := by
        rw [← h]
        exact CFSG.pCore_isPGroup
      rw [h]
      exact card_dvd_three_of_isPGroup_F4 S h1222 h1332 h1334 h3
  rw [oddCore_eq_pCore_three hF hP]
  exact h27 G T L V H S

end CFSG.Quasithin.H13.L32A
