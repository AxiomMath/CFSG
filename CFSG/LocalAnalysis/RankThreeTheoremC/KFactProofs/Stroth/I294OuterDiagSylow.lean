module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Card

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

theorem I294Cfg.le_of_dvd_eightyOne {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal]
    {z g : Y} {D : Subgroup Y} (h : I294Cfg 3 L z g D) (hL : 81 ∣ Nat.card L) : D ≤ L := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 2) h.card
  obtain ⟨P, hDP⟩ := hDp.exists_le_sylow
  have hP : Nat.card P = 81 := h.card_sylow_eq_eightyOne P hDP
  obtain ⟨Q⟩ : Nonempty (Sylow 3 L) := inferInstance
  have hQ : 81 ∣ Nat.card Q := by
    have := Q.pow_dvd_card_of_pow_dvd_card (n := 4) (by simpa using hL)
    simpa using this
  have hQ81 : 81 ≤ Nat.card Q := Nat.le_of_dvd Nat.card_pos hQ
  obtain ⟨Q', hQ'⟩ := Sylow.exists_comap_subtype_eq Q
  have hQ'c : Nat.card Q' = 81 := by
    rw [Sylow.card_eq_multiplicity Q', ← hP, Sylow.card_eq_multiplicity P]
  have hmap : (Q' : Subgroup Y).comap L.subtype = (Q : Subgroup L) := hQ'
  have hQ'L : (Q' : Subgroup Y) ≤ L := by
    have hle : (Q : Subgroup L).map L.subtype ≤ (Q' : Subgroup Y) := by
      rw [← hmap]
      exact Subgroup.map_comap_le _ _
    have hcard : Nat.card ((Q : Subgroup L).map L.subtype) = Nat.card Q :=
      Subgroup.card_map_of_injective L.subtype_injective
    have heq : (Q : Subgroup L).map L.subtype = (Q' : Subgroup Y) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hQ'c]; exact hQ81)
    rw [← heq]
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y Q' P
  have hPL : (P : Subgroup Y) ≤ L := by
    intro x hx
    rw [← hy, Sylow.coe_subgroup_smul] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact (inferInstance : L.Normal).conj_mem w (hQ'L hw) y
  exact hDP.trans hPL

theorem I294Cfg.exists_elemAbelian_twentySeven {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    [L.Normal] {z g : Y} {D : Subgroup Y} (h : I294Cfg 3 L z g D) :
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  obtain ⟨E, -, hE, hc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three
    (⊤ : Subgroup Y)
  rw [h.rank] at hc
  exact ⟨E, hE, by rw [hc]; norm_num⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
