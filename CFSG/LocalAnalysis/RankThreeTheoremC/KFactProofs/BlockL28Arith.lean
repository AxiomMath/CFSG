module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGenArith

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.AGLEmbedding

theorem ordA_eq_504_iff {n q f : ℕ} (hq : q = 2 ^ f) : ordA n q = 504 ↔ n = 1 ∧ q = 8 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq8⟩ => by subst hn hq8; unfold ordA; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordA_two_part hq (e := 3) (m := 63) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordA; decide)

theorem ordTwistedA_eq_504_iff {n q f : ℕ} (hq : q = 2 ^ f) :
    ordTwistedA n q = 504 ↔ n = 1 ∧ q = 8 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq8⟩ => by subst hn hq8; unfold ordTwistedA; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordTwistedA_two_part hq (e := 3) (m := 63)
    (by norm_num) (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordTwistedA; decide)

theorem ordBC_eq_504_iff {n q f : ℕ} (hq : q = 2 ^ f) : ordBC n q = 504 ↔ n = 1 ∧ q = 8 := by
  refine ⟨fun h => ?_, fun ⟨hn, hq8⟩ => by subst hn hq8; unfold ordBC; decide⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordBC_two_part hq (e := 3) (m := 63) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  subst hq
  interval_cases n <;> interval_cases f <;> first | omega | (revert h; unfold ordBC; decide)

theorem ordD_ne_504 {n q f : ℕ} (hq : q = 2 ^ f) : ordD n q ≠ 504 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordD_two_part hq (e := 3) (m := 63) (by norm_num)
    (by norm_num) (h.trans (by norm_num))
  interval_cases n <;> omega

theorem ordTwistedD_ne_504 {n q f : ℕ} (hq : q = 2 ^ f) : ordTwistedD n q ≠ 504 := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5⟩ := LeviBlock.ordTwistedD_two_part hq (e := 3) (m := 63)
    (by norm_num) (by norm_num) (h.trans (by norm_num))
  interval_cases n <;> omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
