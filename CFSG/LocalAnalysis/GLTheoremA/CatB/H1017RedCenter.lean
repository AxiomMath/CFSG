module

public import CFSG.LocalAnalysis.GLTheoremA.S8.Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
import CFSG.LocalAnalysis.GLTheoremA.CatB.I66At
import CFSG.LocalAnalysis.GLTheoremA.PartI.I2611

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S8

variable {G : Type} [Group G] [Finite G]

private theorem card_center_pQuot_facts
    (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) {p : ℕ} (hp : p.Prime)
    {X L : Subgroup G} (hL : GLAPComponent p X L) {s : TauCeti.SporadicName}
    (hs : catalogIs (PSimple p L) (sporIs s)) :
    (∃ n : ℕ, Nat.card (Subgroup.center (PQuot p L)) = p ^ n) ∧
      Nat.card (Subgroup.center (PQuot p L)) ∣
        CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨i, hi, ⟨e⟩⟩ := hs
  have hi' : i = .sporadic s := hi
  subst hi'
  have hq := isQuasisimple_pQuot_of_glaPComponent hp hL
  exact ⟨IsPGroup.iff_card.1 (I2611.isPGroup_center_pQuot' hp L),
    i66_card_center_dvd hT (K := PQuot p L) ⟨hq.1⟩ s e⟩

theorem center_pQuot_eq_bot_of_spor (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L) {s : TauCeti.SporadicName}
    (hs : catalogIs (PSimple p L) (sporIs s))
    (hps : ¬ p ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s) :
    Nat.card (Subgroup.center (PQuot p L)) = 1 := by
  obtain ⟨⟨n, hn⟩, hdvd⟩ := card_center_pQuot_facts hT hp hL hs
  rw [hn] at hdvd ⊢
  rcases n with _ | n
  · exact pow_zero p
  · exact absurd ((dvd_pow_self p n.succ_ne_zero).trans hdvd) hps

theorem card_center_pQuot_of_spor (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {p : ℕ} (hp : p.Prime) {X L : Subgroup G} (hL : GLAPComponent p X L) {s : TauCeti.SporadicName}
    (hs : catalogIs (PSimple p L) (sporIs s))
    (hps : ¬ p ^ 2 ∣ CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s) :
    Nat.card (Subgroup.center (PQuot p L)) = 1 ∨ Nat.card (Subgroup.center (PQuot p L)) = p := by
  obtain ⟨⟨n, hn⟩, hdvd⟩ := card_center_pQuot_facts hT hp hL hs
  rw [hn] at hdvd ⊢
  rcases n with _ | _ | n
  · exact Or.inl (pow_zero p)
  · exact Or.inr (pow_one p)
  · exact absurd ((pow_dvd_pow p (by omega : 2 ≤ n + 2)).trans hdvd) hps

theorem exists_rowL_of_spor (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers)
    {p : ℕ} {X L : Subgroup G}
    (hL : GLAPComponent p X L) (row : Row) (hp : row.prime = p)
    (hs : catalogIs (PSimple p L) (sporIs row.name)) : ∃ row' : Row, RowL row' p L := by
  subst hp
  have hpp : row.prime.Prime := by cases row <;> norm_num [S8.Row.prime]
  cases row with
  | ly => exact ⟨.ly, rfl, hs, center_pQuot_eq_bot_of_spor hT hpp hL hs (by decide)⟩
  | co2 => exact ⟨.co2, rfl, hs, center_pQuot_eq_bot_of_spor hT hpp hL hs (by decide)⟩
  | co1 => exact ⟨.co1, rfl, hs, center_pQuot_eq_bot_of_spor hT hpp hL hs (by decide)⟩
  | fi24 | fi24h =>
    rcases card_center_pQuot_of_spor hT hpp hL hs (by decide) with h | h
    · exact ⟨.fi24, rfl, hs, h⟩
    · exact ⟨.fi24h, rfl, hs, h⟩
  | suz | suzh =>
    rcases card_center_pQuot_of_spor hT hpp hL hs (by decide) with h | h
    · exact ⟨.suz, rfl, hs, h⟩
    · exact ⟨.suzh, rfl, hs, h⟩
  | th => exact ⟨.th, rfl, hs, center_pQuot_eq_bot_of_spor hT hpp hL hs (by decide)⟩
  | m3 => exact ⟨.m3, rfl, hs, center_pQuot_eq_bot_of_spor hT hpp hL hs (by decide)⟩
  | m5 => exact ⟨.m5, rfl, hs, center_pQuot_eq_bot_of_spor hT hpp hL hs (by decide)⟩

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
