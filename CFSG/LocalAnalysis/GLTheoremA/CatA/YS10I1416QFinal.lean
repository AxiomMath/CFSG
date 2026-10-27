module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416QAlt
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416QLie
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416QU42
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416LRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416L
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open TauCeti

section Certs

theorem twoRank_lt_six_chev2Small (J : Type) [Group J] [Finite J] (hJ : CFSG.Open.IsQuasisimple J)
    (hcat : catalogIs (J ⧸ Subgroup.center J) chev2Small) : twoRank J < 6 := by
  have hJp : Group.IsPerfect J := ⟨hJ.1⟩
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic p hp => exact absurd hi (by simp [chev2Small])
  | sporadic s => exact absurd hi (by simp [chev2Small])
  | alternating n hn =>
    have hn' : n = 5 ∨ n = 6 ∨ n = 8 := hi
    rcases hn' with rfl | rfl | rfl
    · have h1 : Nat.card (Subgroup.center J) ∣
          Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin 5))) :=
        CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hJp e
      rw [griess_card_alt_five] at h1
      exact twoRank_lt_six_of_alt hJp (by norm_num) (m := 1) odd_one e (h1.trans (by norm_num))
    · have h1 : Nat.card (Subgroup.center J) ∣
          Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin 6))) :=
        CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hJp e
      rw [griess_card_alt_six] at h1
      exact twoRank_lt_six_of_alt hJp (by norm_num) (m := 3) (by decide) e (h1.trans (by norm_num))
    · have h1 : Nat.card (Subgroup.center J) ∣
          Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin 8))) :=
        CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier hJp e
      rw [griess_card_alt_eight] at h1
      exact twoRank_lt_six_of_alt hJp (by norm_num) (m := 1) odd_one e (h1.trans (by norm_num))
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | A r q =>
      cases r with
      | zero => exact absurd hi (by simp [chev2Small])
      | succ r =>
        cases r with
        | zero =>
          have hq : q.card = 7 ∨ q.card = 8 := hi
          rcases hq with hq | hq
          · exact twoRank_lt_six_of_A_one_seven hJp hv hq e
          · exact twoRank_lt_six_of_A_one_eight hJp hJ hv hq e
        | succ r => exact absurd hi (by simp [chev2Small])
    | twistedA r q =>
      rcases Nat.lt_or_ge r 4 with hr4 | hr4
      · interval_cases r
        · exact absurd hi (by simp [chev2Small])
        · exact absurd hi (by simp [chev2Small])
        · have hq : q.card = 3 := hi
          exact twoRank_lt_six_of_twistedA_two_three
            CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds hJp hv hq e
        · have hq : q.card = 2 := hi
          exact twoRank_lt_six_of_twistedA_three_two hJp hv hq e
      · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 4 := ⟨r - 4, by omega⟩
        exact absurd hi (by simp [chev2Small])
    | _ => exact absurd hi (by simp [chev2Small])

theorem chev2SporRank_holds : Chev2SporRank := by
  intro J _ _ hJ hZ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  rcases hi with hi | hi
  · exact twoRank_lt_six_chev2Small J hJ ⟨i, hi, ⟨e⟩⟩
  · cases i with
    | lie d =>
      obtain ⟨d, hv⟩ := d
      cases d with
      | A r q =>
        cases r with
        | zero => exact absurd hi (by simp [chev2L34])
        | succ r =>
          cases r with
          | zero => exact absurd hi (by simp [chev2L34])
          | succ r =>
            cases r with
            | zero =>
              have hq : q.card = 4 := hi
              exact twoRank_lt_six_of_A_two_four hZ hv hq e
            | succ r => exact absurd hi (by simp [chev2L34])
      | _ => exact absurd hi (by simp [chev2L34])
    | _ => exact absurd hi (by simp [chev2L34])

end Certs

end CFSG.LocalAnalysis.GLTheoremA

end
