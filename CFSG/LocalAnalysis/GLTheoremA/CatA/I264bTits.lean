module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bArith
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bLoc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bFacts
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.RankThree.PartOne.KF.ClsTits
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti CFSG.Sporadic.Schreier.Tits
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)


theorem titsEquiv_of_catalog {S : Type} [Group S] (h : catalogIs S fTits) : Nonempty (S ≃* titsD) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie dd =>
    obtain ⟨d, hv⟩ := dd
    cases d with
    | tits => exact titsModelEquiv S 2 1 (CFSG.StandardType.ChevTwo.reeTitsModel_of_tits hv e)
    | _ => exact hi.elim

theorem localRank_titsD_le_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    CFSG.Assembly.RankThreeEven.localRank p titsD ≤ 1 := by
  have hp2 : p ≠ 2 := by omega
  by_cases hp5' : p = 5
  · subst hp5'
    exact CFSG.RankThree.PartOne.KFU.localRank_le_one_of_small_centralizers (G := titsD) hp hp2
      (fun a ha => CFSG.RankThree.PartOne.KE.tits_not_four_dvd_card_centralizer_of_mulEquiv
        (MulEquiv.refl titsD) ha)
      (fun E _ hc => CFSG.RankThree.PartOne.KE.tits_odd_card_centralizer_of_mulEquiv
        (MulEquiv.refl titsD) (by simpa using hc))
  · have hp7 : 7 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p
      · exact hp5' rfl
      · exact absurd hp (by norm_num)
    exact CFSG.RankThree.PartOne.KFU.localRank_le_one_of_not_sq_dvd (G := titsD) hp (by
      rw [card_titsD]
      exact CFSG.RankThree.PartOne.KFU.not_sq_dvd_card_titsD hp hp7)

theorem rankBound_titsD_three :
    ∀ E T : Subgroup titsD, IsElemAbelian 3 E → IsPGroup 2 T → T ≠ ⊥ →
      E ≤ Subgroup.normalizer (T : Set titsD) → Nat.card E ≤ 3 := by
  intro E T hE hT2 hT hET
  by_contra hlt
  push Not at hlt
  obtain ⟨P, hPE, hP9⟩ := exists_sub_card_pow (n := 2) Nat.prime_three hE
    (sq_le_card_of_lt Nat.prime_three hE hlt)
  have hW3 : ¬ 3 ∣ Nat.card T := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := hT2.exists_card_eq
    rw [hj]
    intro hd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    omega
  exact hT (CFSG.RankThree.PartTwo.Sec4.Item434RemTits.eq_bot_of_le_normalizer
    (isElemAbelian_mono hE hPE) (by rw [hP9]; norm_num) hW3 (hPE.trans hET))

theorem kDescFam_tits (p : ℕ) : KDescFam p fTits := by
  intro hp hp2 Y _ _ K B h hc hcB
  obtain ⟨e⟩ := titsEquiv_of_catalog hc
  haveI : Finite (↥K ⧸ Subgroup.center ↥K) := inferInstance
  haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := h.qs.2
  have hcardS : Nat.card (↥K ⧸ Subgroup.center ↥K) = 17971200 := by
    rw [Nat.card_congr e.toEquiv, card_titsD]
  haveI : IsSimpleGroup titsD := e.symm.isSimpleGroup
  have hZ : Subgroup.center titsD = ⊥ :=
    center_eq_bot_of_simple_nonprime (n := 17971200) (by rw [← Nat.card_congr e.toEquiv]; exact hcardS)
      (by norm_num)
  have hOutc : Nat.card (Outer titsD) = 2 := card_outer_titsD
  have hOut : ¬ p ∣ Nat.card (Outer titsD) := by
    rw [hOutc]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hd)
  refine (false_of_rank_bound hp hp2 h hcB e hZ (inner_of_pow_eq_one_of_not_dvd_outer hp hOut) ?_).elim
  by_cases hp3 : p = 3
  · subst hp3
    exact rankBound_titsD_three
  · have hp5 : 5 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p
      · exact Nat.not_prime_zero hp
      · exact Nat.not_prime_one hp
      · exact hp2 rfl
      · exact hp3 rfl
      · exact absurd hp (by norm_num)
    exact rankBound_of_localRank_le_one hp (localRank_titsD_le_one hp hp5)

end CFSG.LocalAnalysis.GLTheoremA
