module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.Sporadic.Mathieu.M11
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.J4
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20Facts
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.QuasithinUnique.Id2519

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint

theorem card_of_psl_three {X : Type} [Group X] {p f : ℕ}
    (h : StatedClassicalModel X .PSL 3 p f) :
    Nat.card X = ((p ^ f) ^ (3 * (3 - 1) / 2) * ∏ index ∈ Finset.Icc 2 3, ((p ^ f) ^ index - 1)) /
      Nat.gcd 3 (p ^ f - 1) :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl (by norm_num) h

theorem card_of_psl_three_four {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 2 2) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem card_of_psl_three_two {X : Type} [Group X] (h : StatedClassicalModel X .PSL 3 2 1) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_of_g2_four
    {X : Type} [Group X] (h : ChevalleyExceptionalModel X .G2 2 2) :
    Nat.card X = 251596800 := by
  have := CFSG.Timmesfeld.ExceptionalOrders.card_of_untwistedChevalleyModel_G2 h.2
  rw [this]
  unfold CFSG.Open.ordG2
  norm_num

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin]
  decide

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin]
  decide

theorem sporadic_data
    {s : TauCeti.SporadicName} (hs : Ch1.IsLemma115SporadicName s) :
    IsSimpleGroup (NativeSporadic.Carrier s) ∧
      (Nat.card (NativeSporadic.Carrier s) = 7920 ∨ Nat.card (NativeSporadic.Carrier s) = 95040 ∨
        Nat.card (NativeSporadic.Carrier s) = 443520 ∨
        Nat.card (NativeSporadic.Carrier s) = 10200960 ∨
        Nat.card (NativeSporadic.Carrier s) = 244823040 ∨
        Nat.card (NativeSporadic.Carrier s) = 604800 ∨
        Nat.card (NativeSporadic.Carrier s) = 86775571046077562880 ∨
        Nat.card (NativeSporadic.Carrier s) = 44352000 ∨
        Nat.card (NativeSporadic.Carrier s) = 4030387200 ∨
        Nat.card (NativeSporadic.Carrier s) = 145926144000) := by
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m11_simplicity.2.2,
      Or.inl CFSG.Sporadic.Mathieu.card_M11⟩
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2,
      Or.inr (Or.inl CFSG.Sporadic.Mathieu.card_M12)⟩
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2,
      Or.inr (Or.inr (Or.inl CFSG.Sporadic.Mathieu.card_M22))⟩
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m23_simplicity.2.2,
      Or.inr (Or.inr (Or.inr (Or.inl CFSG.Sporadic.Schreier.m23_card)))⟩
  · exact ⟨CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl CFSG.Sporadic.Mathieu.card_M24))))⟩
  · exact ⟨CFSG.Sporadic.J2.isSimpleGroup_J2,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl CFSG.Sporadic.J2.card_J2)))))⟩
  · exact ⟨CFSG.Sporadic.J4.isSimpleGroup_J4,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl CFSG.Sporadic.J4.card_J4))))))⟩
  · exact ⟨CFSG.Sporadic.HS.isSimpleGroup_HS,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl CFSG.Sporadic.HS.card_HS)))))))⟩
  · exact ⟨CFSG.Sporadic.He.isSimpleGroup_He,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl CFSG.Sporadic.He.card_He))))))))⟩
  · exact ⟨CFSG.Sporadic.Ru.isSimpleGroup_Ru,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        CFSG.Sporadic.Ru.card_Ru))))))))⟩

theorem no_psl_two_order {p N c : ℕ} (hc : c * (c * c - 1) < 2 * N)
    (hc' : 2 * N < (c + 1) * ((c + 1) * (c + 1) - 1)) : p * (p * p - 1) ≠ 2 * N := by
  intro h
  rcases le_or_gt p c with h1 | h1
  · have : p * (p * p - 1) ≤ c * (c * c - 1) :=
      Nat.mul_le_mul h1 (Nat.sub_le_sub_right (Nat.mul_le_mul h1 h1) 1)
    omega
  · have h2 : c + 1 ≤ p := h1
    have : (c + 1) * ((c + 1) * (c + 1) - 1) ≤ p * (p * p - 1) :=
      Nat.mul_le_mul h2 (Nat.sub_le_sub_right (Nat.mul_le_mul h2 h2) 1)
    omega

theorem not_card_isL2pType {K : Type} [Group K] (hK : IsL2pType K) {N : ℕ}
    (hN : N = 20160 ∨ N = 251596800 ∨ N = 360 ∨ N = 2520 ∨ N = 7920 ∨ N = 95040 ∨ N = 443520 ∨
      N = 10200960 ∨ N = 244823040 ∨ N = 604800 ∨ N = 86775571046077562880 ∨ N = 44352000 ∨
      N = 4030387200 ∨ N = 145926144000) (hc : Nat.card K = N) : False := by
  rcases hK with ⟨p, hFM, hp7, hmodel⟩ | hmodel
  · have hpp : p.Prime := hFM.1
    have hp2 : p ≠ 2 := by omega
    have hf := card_of_l2p hpp hp2 hmodel
    rw [hc] at hf
    rcases hN with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact no_psl_two_order (c := 34) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 795) (by norm_num) (by norm_num) hf
    ·
      have hle : p ≤ 9 := by
        by_contra hgt
        have h10 : 10 ≤ p := by omega
        have : 10 * (10 * 10 - 1) ≤ p * (p * p - 1) :=
          Nat.mul_le_mul h10 (Nat.sub_le_sub_right (Nat.mul_le_mul h10 h10) 1)
        omega
      interval_cases p
      · exact absurd hpp (by decide)
      · exact absurd hpp (by decide)
    · exact no_psl_two_order (c := 17) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 25) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 57) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 96) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 273) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 788) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 106) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 5577965) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 445) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 2005) (by norm_num) (by norm_num) hf
    · exact no_psl_two_order (c := 6633) (by norm_num) (by norm_num) hf
  · have h168 := card_of_psl_three_two hmodel
    rw [h168] at hc
    subst hc
    omega

end CFSG.QuasithinUnique.Id2519
