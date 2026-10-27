module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A705a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b
public import CFSG.Quasithin.H13.L32AC47k

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H K : Subgroup G}

theorem l1_inf_T_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) : l1 T L V ⊓ T = pCoreOf 2 (l1 T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN := Setting147.T_le_N_l1_F4 S h1332
  have h3 := relIndex_l1_F4 h1222 h1332 h1334 S.hyp
  have hPl : pCoreOf 2 (l1 T L V) ≤ l1 T L V := pCoreOf_le 2 _

  have hPT : pCoreOf 2 (l1 T L V) ≤ T := by
    have hN : l1 T L V ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 (l1 T L V) : Set G) :=
      sup_le (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 _))
        (hTN.trans (normalizer_le_normalizer_pCoreOf 2 _))
    exact (le_pCoreOf_of_le_normalizer 2 (hPl.trans le_sup_left) hN
      (pCoreOf_isPGroup 2 _)).trans (Setting147.R1_le_T S)
  have hle : pCoreOf 2 (l1 T L V) ≤ l1 T L V ⊓ T := le_inf hPl hPT
  refine le_antisymm ?_ hle

  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hle (inf_le_left : l1 T L V ⊓ T ≤ l1 T L V)
  rw [h3] at hmul
  have hd3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V ⊓ T) ∣ 3 := Dvd.intro _ hmul
  have h2 : IsPGroup 2 ↥(l1 T L V ⊓ T) :=
    S.hyp.fsu.sylow.1.to_le inf_le_right
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp h2)
  have hcard := Subgroup.relIndex_mul_card (pCoreOf 2 (l1 T L V)) (l1 T L V ⊓ T)
  rw [hk] at hcard
  have hd2 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V ⊓ T) ∣ 2 ^ k := Dvd.intro _ hcard
  have h1 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V ⊓ T) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hd3 with h | h
    · exact h
    · rw [h] at hd2
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd2)) (by norm_num)
  exact Subgroup.relIndex_eq_one.mp h1

theorem relIndex_TK_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) (hl1K : l1 T L V ≤ K) :
    (T ⊓ K).relIndex (l1 T L V ⊔ (T ⊓ K)) = 3 := by
  have hTN := Setting147.T_le_N_l1_F4 S h1332
  have hTKN : T ⊓ K ≤ Subgroup.normalizer (l1 T L V : Set G) := inf_le_left.trans hTN
  have h3 := relIndex_l1_F4 h1222 h1332 h1334 S.hyp
  have hinf : l1 T L V ⊓ (T ⊓ K) = pCoreOf 2 (l1 T L V) := by
    rw [← inf_assoc, inf_eq_left.mpr (inf_le_left.trans hl1K), l1_inf_T_F4 h1222 h1332 h1334 S]

  have hX := card_sup_eq hTKN
  rw [sup_comm] at hX

  have h1 := Subgroup.relIndex_mul_card (l1 T L V) (T ⊓ K)
  rw [hinf] at h1

  have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 (l1 T L V)) (l1 T L V)
  rw [h3, inf_eq_left.mpr (pCoreOf_le 2 _)] at h2

  have h4 := Subgroup.relIndex_mul_card (T ⊓ K) (l1 T L V ⊔ (T ⊓ K))
  rw [inf_eq_left.mpr (le_sup_right : T ⊓ K ≤ l1 T L V ⊔ (T ⊓ K))] at h4
  have hpos : 0 < Nat.card ↥(T ⊓ K) := Nat.card_pos
  have key : (T ⊓ K).relIndex (l1 T L V ⊔ (T ⊓ K)) * Nat.card ↥(T ⊓ K) =
      3 * Nat.card ↥(T ⊓ K) := by
    rw [h4, hX, ← h2, ← h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos key

end CFSG.Quasithin.H13.L32A.C
