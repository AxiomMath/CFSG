module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporSevenType
public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.Fi7Base
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.I1416Rows

theorem not_simple_of_card_dvd_294 {T : Type} [Group T] [Finite T] [IsSimpleGroup T]
    (hnab : ∃ a b : T, a * b ≠ b * a) (hd : Nat.card T ∣ 294) : False := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hns : ¬ Group.IsSolvable T := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.2 h) a b)
  have h60 : 60 ≤ Nat.card T := by
    by_contra h
    exact hns (CFSG.GroupTheory.groups_order_below_sixty_solvable (by omega))
  have hcases : Nat.card T = 98 ∨ Nat.card T = 147 ∨ Nat.card T = 294 := by
    obtain ⟨c, hc⟩ := hd
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    have hc5 : c ≤ 4 := by
      by_contra h
      have : Nat.card T * 5 ≤ Nat.card T * c := Nat.mul_le_mul_left _ (by omega)
      omega
    interval_cases c <;> omega
  obtain ⟨P⟩ : Nonempty (Sylow 7 T) := inferInstance
  have hP : Nat.card (P : Subgroup T) = 49 := by
    rw [P.card_eq_multiplicity]
    rcases hcases with h | h | h <;> rw [h]
    · rw [show (98 : ℕ) = 7 ^ 2 * 2 by norm_num,
        Nat.factorization_mul_apply_of_coprime (by norm_num), Nat.factorization_pow,
        Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 2 by norm_num)]
      norm_num
    · rw [show (147 : ℕ) = 7 ^ 2 * 3 by norm_num,
        Nat.factorization_mul_apply_of_coprime (by norm_num), Nat.factorization_pow,
        Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 3 by norm_num)]
      norm_num
    · rw [show (294 : ℕ) = 7 ^ 2 * 6 by norm_num,
        Nat.factorization_mul_apply_of_coprime (by norm_num), Nat.factorization_pow,
        Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd (show ¬ 7 ∣ 6 by norm_num)]
      norm_num
  have hn1 : Nat.card (Sylow 7 T) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 T
  have hnidx : Nat.card (Sylow 7 T) = (Subgroup.normalizer ((P : Subgroup T) : Set T)).index :=
    Sylow.card_eq_index_normalizer P
  have hidx : (Subgroup.normalizer ((P : Subgroup T) : Set T)).index ∣ (P : Subgroup T).index :=
    Subgroup.index_dvd_of_le Subgroup.le_normalizer
  have hidx6 : (P : Subgroup T).index ∣ 6 := by
    have h1 := Subgroup.index_mul_card (P : Subgroup T)
    rw [hP] at h1
    rcases hcases with h | h | h <;> rw [h] at h1
    · exact ⟨3, by omega⟩
    · exact ⟨2, by omega⟩
    · exact ⟨1, by omega⟩
  have hn6 : Nat.card (Sylow 7 T) ∣ 6 := hnidx ▸ hidx.trans hidx6
  have hn : Nat.card (Sylow 7 T) = 1 := by
    have hle := Nat.le_of_dvd (by norm_num) hn6
    have h1 : Nat.card (Sylow 7 T) % 7 = 1 := hn1
    have hpos : 0 < Nat.card (Sylow 7 T) := Nat.card_pos
    interval_cases h : Nat.card (Sylow 7 T) <;> omega
  have hN : Subgroup.normalizer ((P : Subgroup T) : Set T) = ⊤ := by
    rw [← Subgroup.index_eq_one, ← hnidx, hn]
  have hPn : (P : Subgroup T).Normal := Subgroup.normalizer_eq_top_iff.mp hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (P : Subgroup T) with hb | ht
  · rw [hb, Subgroup.card_bot] at hP
    norm_num at hP
  · rw [ht, Subgroup.card_top] at hP
    omega

end CFSG.LocalAnalysis.GLTheoremA.I1416Rows

namespace CFSG.HardMathSupport.Dickson.I271.Fi7

open CFSG.Sporadic.Fi24 (J)
open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows


theorem card_pSimple_dvd_2520 (s : J) (hs : orderOf s = 7) {I : Subgroup J}
    (hI : GLAPComponent 7 (Subgroup.centralizer ({s} : Set J)) I) :
    Nat.card (PSimple 7 I) ∣ 2520 := by
  haveI : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab (by norm_num) hI
  haveI := hsI
  have hd := prime_mul_card_pSimple_dvd_cent (by norm_num) hs hI.1
  obtain ⟨g, hg⟩ := fi7_conj_class s hs
  have hc : Nat.card (Subgroup.centralizer ({s} : Set J)) =
      Nat.card (Subgroup.centralizer ({g * s * g⁻¹} : Set J)) :=
    (card_centralizer_conj' g s).symm
  rcases hg with h | h <;> rw [hc, h] at hd
  · rw [card_centralizer_Y7] at hd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) (hd.trans (by norm_num))
  · rw [card_centralizer_C7] at hd
    exact (not_simple_of_card_dvd_294 hnab
      (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 7) (hd.trans (by norm_num)))).elim

theorem fi24_model (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    Finite J ∧ IsSimpleGroup J ∧ (∃ a c : J, a * c ≠ c * a) ∧
      Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .Fi24Prime).Group) := by
  have hfin : Finite J := Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Fi24.card_J]; norm_num)
  have hs : IsSimpleGroup J := CFSG.Sporadic.Fi24.isSimpleGroup_J
  have hpr : ¬ (Nat.card J).Prime := by rw [CFSG.Sporadic.Fi24.card_J]; norm_num
  exact ⟨hfin, hs, @CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple J _ hfin hs hpr,
    ⟨CFSG.Sporadic.Fi24.fi24EquivJ.symm.trans (hbr .Fi24Prime).some⟩⟩

theorem row_Fi24_seven (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    I1416SporRow .Fi24Prime 7 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi24_model hbr
  refine @row_of_model .Fi24Prime 7 J _ hfin hs hOut b hnc fun x hx I hI => ?_
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab (by norm_num) hI
  haveI := hsI
  exact typeOK_seven_of_card_dvd_2520 hb hnab (card_pSimple_dvd_2520 x hx hI)

theorem qrow_Fi24_seven (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CFSG.LocalAnalysis.GLTheoremA.I1416QRows.I1416QRow .Fi24Prime 7 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := fi24_model hbr
  refine @CFSG.LocalAnalysis.GLTheoremA.I1416QRows.qrow_of_model .Fi24Prime 7 J _ hfin hs hOut b
    hnc fun x hx I hI => ?_
  obtain ⟨hsI, hnab⟩ := CFSG.LocalAnalysis.GLTheoremA.KDSpor.pSimple_simple_nonab (by norm_num) hI
  haveI := hsI
  exact qtypeOK_seven_of_card_dvd_2520 hb hnab (card_pSimple_dvd_2520 x hx hI)

end CFSG.HardMathSupport.Dickson.I271.Fi7
