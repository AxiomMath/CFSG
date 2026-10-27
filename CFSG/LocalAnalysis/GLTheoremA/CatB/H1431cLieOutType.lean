module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1431cLieOutCharTwo
public import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Inputs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDet
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open CFSG CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB TauCeti
open CFSG.RankThree.PartTwo

theorem lieSOut_triD4_order_ge {Q : ℕ} (hQ : 4 ≤ Q) :
    16777216 * 15 * 4095 * 1 ≤ Q ^ 12 * (Q ^ 2 - 1) * (Q ^ 6 - 1) * (Q ^ 8 + Q ^ 4 + 1) := by
  have h1 : 16777216 ≤ Q ^ 12 :=
    calc 16777216 = 4 ^ 12 := by norm_num
      _ ≤ Q ^ 12 := Nat.pow_le_pow_left hQ 12
  have h2 : 16 ≤ Q ^ 2 :=
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
  have h3 : 4096 ≤ Q ^ 6 :=
    calc 4096 = 4 ^ 6 := by norm_num
      _ ≤ Q ^ 6 := Nat.pow_le_pow_left hQ 6
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)) (by omega)

theorem lieSOut_g2_order_ge {Q : ℕ} (hQ : 5 ≤ Q) :
    15625 * 15624 * 24 ≤ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
  have h1 : 15625 ≤ Q ^ 6 :=
    calc 15625 = 5 ^ 6 := by norm_num
      _ ≤ Q ^ 6 := Nat.pow_le_pow_left hQ 6
  have h2 : 25 ≤ Q ^ 2 :=
    calc 25 = 5 ^ 2 := by norm_num
      _ ≤ Q ^ 2 := Nat.pow_le_pow_left hQ 2
  exact Nat.mul_le_mul (Nat.mul_le_mul h1 (by omega)) (by omega)

theorem lieSOutOrd_sp6two : LieSOutOrd 1451520 where
  three_dvd := by norm_num
  not_dvd_216 := by norm_num
  not_dvd_360 := by norm_num
  not_dvd_12096 := by norm_num
  not_dvd_17971200 := by norm_num
  ne_triD4 := fun Q hQ => by
    rcases (by omega : Q = 2 ∨ Q = 3 ∨ 4 ≤ Q) with rfl | rfl | h4
    · norm_num
    · norm_num
    · exact ne_of_lt (lt_of_lt_of_le (by norm_num) (lieSOut_triD4_order_ge h4))
  ne_g2 := fun Q hQ => by
    rcases (by omega : Q = 4 ∨ 5 ≤ Q) with rfl | h5
    · norm_num
    · exact ne_of_lt (lt_of_lt_of_le (by norm_num) (lieSOut_g2_order_ge h5))
  ne_sl3 := KFacts.KS14.forall_of_forall_lt (B := 114) (by norm_num) (by norm_num)
    (by decide +kernel)
  ne_su3 := KFacts.KS14.forall_of_forall_lt (B := 114) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem lieSOutOrd_sp48 : LieSOutOrd 1056706560 where
  three_dvd := by norm_num
  not_dvd_216 := by norm_num
  not_dvd_360 := by norm_num
  not_dvd_12096 := by norm_num
  not_dvd_17971200 := by norm_num
  ne_triD4 := fun Q hQ => by
    rcases (by omega : Q = 2 ∨ Q = 3 ∨ 4 ≤ Q) with rfl | rfl | h4
    · norm_num
    · norm_num
    · exact ne_of_lt (lt_of_lt_of_le (by norm_num) (lieSOut_triD4_order_ge h4))
  ne_g2 := fun Q hQ => by
    rcases (by omega : Q = 4 ∨ 5 ≤ Q) with rfl | h5
    · norm_num
    · exact ne_of_lt (lt_of_lt_of_le (by norm_num) (lieSOut_g2_order_ge h5))
  ne_sl3 := KFacts.KS14.forall_of_forall_lt (B := 1020) (by norm_num) (by norm_num)
    (by decide +kernel)
  ne_su3 := KFacts.KS14.forall_of_forall_lt (B := 1020) (by norm_num) (by norm_num)
    (by decide +kernel)

theorem lieSOut_lieIndex_isSp48 {S : Type} [Group S] (h : catalogIs S S8.L84.isSp48) :
    ∃ (q : PrimePower) (hv : (LieTypeIndex.B 2 q).Valid), q.card = 8 ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨.B 2 q, hv⟩) := by
  obtain ⟨d, hv, hP, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex h
  cases d with
  | B r q =>
    rcases r with _ | _ | _ | r
    · exact hP.elim
    · exact hP.elim
    · exact ⟨q, hv, hP, ⟨e⟩⟩
    · exact hP.elim
  | _ => exact hP.elim

section Cert


theorem lieSOut_lieModel_sp6two {X : Type} [Group X] (hX : catalogIs X S9.isSp6two) :
    Blueprint.LieModel X .PSp 3 2 1 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.lieIndex_isSp6two hX
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
    (s := 1) (by norm_num) (hq.trans (by norm_num))
  have hm := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_B 3 q hv h1 e
  rwa [h1, h2] at hm

theorem lieSOut_lieModel_sp48 {X : Type} [Group X] (hX : catalogIs X S8.L84.isSp48) :
    Blueprint.LieModel X .PSp 2 2 3 := by
  obtain ⟨q, hv, hq, ⟨e⟩⟩ := lieSOut_lieIndex_isSp48 hX
  obtain ⟨h1, h2⟩ := CFSG.LocalAnalysis.GLTheoremA.primePower_eq_of_card_eq Nat.prime_two
    (s := 3) (by norm_num) (hq.trans (by norm_num))
  have hm := CFSG.HardMathSupport.Dickson.Sec6.blueprintLieModel_B 2 q hv h1 e
  rwa [h1, h2] at hm

theorem lieSOut_type_sp6two : LieSOutType S9.isSp6two 3 1 1451520 where
  card_eq := fun {X} _ hX => by
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (lieSOut_lieModel_sp6two hX)]
    decide +kernel
  det := fun {X} _ hX _ _ _ hm =>
    CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique (lieSOut_lieModel_sp6two hX) hm
  ord := lieSOutOrd_sp6two

theorem lieSOut_type_sp48 : LieSOutType S8.L84.isSp48 2 3 1056706560 where
  card_eq := fun {X} _ hX => by
    rw [CFSG.SeitzReduction.F4Pilot.card_eq_evenLieOrder (lieSOut_lieModel_sp48 hX)]
    decide +kernel
  det := fun {X} _ hX _ _ _ hm =>
    CFSG.SeitzReduction.SymplecticPilot.lieModel_PSp_two_unique (lieSOut_lieModel_sp48 hX) hm
  ord := lieSOutOrd_sp48

end Cert

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
