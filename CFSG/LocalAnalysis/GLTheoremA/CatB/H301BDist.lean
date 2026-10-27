module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BDefs
public import CFSG.Sporadic.Bridge.LySurj
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.Sporadic.Bridge.Co2Surj
public import CFSG.Sporadic.Bridge.Co1Surj
public import CFSG.Sporadic.Bridge.SuzSurj
public import CFSG.Sporadic.Bridge.Fi24Surj
public import CFSG.Sporadic.Bridge.ThSurj
public import CFSG.RankThree.PartTwo.KFacts.KSListsProofCard
import CFSG.LocalAnalysis.GLTheoremA.CatB.U4Tab5
import CFSG.LocalAnalysis.GLTheoremA.CatB.I1431YCase2
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowU43
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

private theorem finite_card_le_of_equiv {H Y : Type} [Group H] [Group Y] (f : H ≃* Y) {m : ℕ}
    (hY : Finite Y ∧ Nat.card Y ≤ m) : Finite H ∧ Nat.card H ≤ m :=
  ⟨@Finite.of_equiv _ _ hY.1 f.symm.toEquiv, (Nat.card_congr f.toEquiv).trans_le hY.2⟩

private theorem false_of_lt_card {H X : Type} [Group H] [Group X] (e : H ≃* X) {m N : ℕ}
    (hH : Finite H ∧ Nat.card H ≤ m) (hN : m < N)
    (hX : Finite X → Nat.card X ≤ N → N ≤ Nat.card X) : False := by
  obtain ⟨hfin, hm⟩ := hH
  have hc : Nat.card H = Nat.card X := Nat.card_congr e.toEquiv
  have := hX (@Finite.of_equiv _ _ hfin e.toEquiv) (by omega)
  omega

private theorem finite_card_le_of_card {H : Type} [Group H] {n : ℕ} (hc : Nat.card H = n)
    (hn : n ≠ 0) : Finite H ∧ Nat.card H ≤ n :=
  ⟨Nat.finite_of_card_ne_zero (by rw [hc]; exact hn), hc.le⟩

private theorem card_of_isD4of_three {T : Type} [Group T] (h : catalogIs T (S8.isD4of 3)) :
    Nat.card T = 4952179814400 := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | D n q =>
      rcases n with _ | _ | _ | _ | _ | n
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · exact False.elim hi
      · have hq : q.card = 3 := hi
        have hp : q.p = 3 := by
          have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
          rw [← TauCeti.PrimePower.card_def, hq] at h1
          exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 h1
        have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD _ q hv e
        rw [(CFSG.ClassicalInvolution.card_statedClassicalModel_of_ne_two (by omega)
          hM).2.2.2.2.1 rfl, ← TauCeti.PrimePower.card_def, hq]
        decide
      · exact False.elim hi
    | _ => exact False.elim hi
  | _ => exact False.elim hi

section Ly


theorem distLy_holds : I301BDistinct .ly := by
  intro H _ hS hI
  obtain ⟨i, hi, ⟨e1⟩⟩ := hS
  obtain ⟨j, hj, ⟨e2⟩⟩ := hI
  simp only [S8.Row.name, S8.Row.Iq, S8.sporIs] at hi hj
  subst hi hj
  refine false_of_lt_card e1 (N := 51765179004000000)
    (finite_card_le_of_equiv e2 CFSG.Sporadic.Presentation.McL.finite_card_le) (by norm_num)
    fun hf hle => ?_
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Ly.nonempty_mulEquiv_of_card_le hf hle
  exact (CFSG.Sporadic.Ly.card_Ly.symm.trans (Nat.card_congr b.toEquiv)).le

end Ly

section Co2


theorem distCo2_holds : I301BDistinct .co2 := by
  intro H _ hS hI
  obtain ⟨i, hi, ⟨e1⟩⟩ := hS
  simp only [S8.Row.name, S8.sporIs] at hi
  subst hi
  have hc : Nat.card H = 25920 := by
    obtain ⟨j, hj, he⟩ := hI
    exact CatB.card_of_catalogIs_u4two ⟨j, I1431Y.isU4two_of_isPSp43 hj, he⟩
  refine false_of_lt_card e1 (N := 42305421312000) (finite_card_le_of_card hc (by norm_num))
    (by norm_num) fun hf hle => ?_
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv_of_card_le hf hle
  exact (CFSG.Sporadic.Co2.card_Co2.symm.trans (Nat.card_congr b.toEquiv)).le

end Co2

section Co1


theorem distCo1_holds : I301BDistinct .co1 := by
  intro H _ hS hI
  obtain ⟨i, hi, ⟨e1⟩⟩ := hS
  obtain ⟨j, hj, ⟨e2⟩⟩ := hI
  simp only [S8.Row.name, S8.Row.Iq, S8.sporIs] at hi hj
  subst hi hj
  refine false_of_lt_card e1 (N := 4157776806543360000)
    (finite_card_le_of_equiv e2 CFSG.Sporadic.Presentation.Suz.finite_card_le) (by norm_num)
    fun hf hle => ?_
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co1.nonempty_mulEquiv_of_card_le hf hle
  exact (CFSG.Sporadic.Co1.card_Co1.symm.trans (Nat.card_congr b.toEquiv)).le

end Co1

section Fi24


theorem distFi24_holds : I301BDistinct .fi24 := by
  intro H _ hS hI
  obtain ⟨i, hi, ⟨e1⟩⟩ := hS
  simp only [S8.Row.name, S8.sporIs] at hi
  subst hi
  refine false_of_lt_card e1 (N := 1255205709190661721292800)
    (finite_card_le_of_card (card_of_isD4of_three hI) (by norm_num)) (by norm_num)
    fun hf hle => ?_
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv_of_card_le hf hle
  exact (CFSG.Sporadic.Fi24.card_Fi24prime.symm.trans (Nat.card_congr b.toEquiv)).le

end Fi24

section Suz


theorem distSuz_holds : I301BDistinct .suz := by
  intro H _ hS hI
  obtain ⟨i, hi, ⟨e1⟩⟩ := hS
  simp only [S8.Row.name, S8.sporIs] at hi
  subst hi
  refine false_of_lt_card e1 (N := 448345497600)
    (finite_card_le_of_card (H1420.card_eq_of_isU4of_three hI) (by norm_num)) (by norm_num)
    fun hf hle => ?_
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Suz.nonempty_mulEquiv_of_card_le hf hle
  exact (CFSG.Sporadic.Suz.card_Suz.symm.trans (Nat.card_congr b.toEquiv)).le

end Suz

section Th


theorem distTh_holds : I301BDistinct .th := by
  intro H _ hS hI
  obtain ⟨i, hi, ⟨e1⟩⟩ := hS
  simp only [S8.Row.name, S8.sporIs] at hi
  subst hi
  have hc : Nat.card H = 4245696 := by
    obtain ⟨j, hj, ⟨e2⟩⟩ := hI
    cases j with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | G2 q =>
        have hq : q.card = 3 := hj
        rw [Nat.card_congr e2.toEquiv,
          CFSG.RankThree.PartTwo.Sec11.KSListsProof.card_G2_carrier q hv, hq]
        decide
      | _ => exact False.elim hj
    | _ => exact False.elim hj
  refine false_of_lt_card e1 (N := 90745943887872000) (finite_card_le_of_card hc (by norm_num))
    (by norm_num) fun hf hle => ?_
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Th.nonempty_mulEquiv_of_card_le hf hle
  exact (CFSG.Sporadic.Bridge.Th.card_J.symm.trans
    ((Nat.card_congr CFSG.Sporadic.Th.thEquivJ.toEquiv).symm.trans
      (Nat.card_congr b.toEquiv))).le

end Th

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
