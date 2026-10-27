module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Row
import CFSG.LocalAnalysis.GLTheoremA.S8.Lemma84Tools

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8

variable {G : Type} [Group G] [Finite G]

structure I1017RowRanks : Prop where
  ly : I1017LyRank
  co2 : I1017CoTwoRank
  co1 : I1017CoOneRank
  fi24 : I1017FiTwoFourRank
  fi24h : I1017FiTwoFourCoverRank
  suz : I1017SuzRank
  suzh : I1017SuzCoverRank
  th : I1017ThRank
  m3 : I1017MonsterThreeRank
  m5 : I1017MonsterFiveRank

private theorem rank_fact (hR : I1017RowRanks) (row : Row) :
    (row.center = 1 ∧ SimpleElemRank row.prime row.name row.rank) ∨
      (row.center = 3 ∧ row.prime = 3 ∧ CoverElemRank row.name (row.rank + 1)) := by
  cases row
  · exact Or.inl ⟨rfl, hR.ly⟩
  · exact Or.inl ⟨rfl, hR.co2⟩
  · exact Or.inl ⟨rfl, hR.co1⟩
  · exact Or.inl ⟨rfl, hR.fi24⟩
  · exact Or.inr ⟨rfl, rfl, hR.fi24h⟩
  · exact Or.inl ⟨rfl, hR.suz⟩
  · exact Or.inr ⟨rfl, rfl, hR.suzh⟩
  · exact Or.inl ⟨rfl, hR.th⟩
  · exact Or.inl ⟨rfl, hR.m3⟩
  · exact Or.inl ⟨rfl, hR.m5⟩

private theorem exists_lift {p : ℕ} [Fact p.Prime] {L : Subgroup G} {E₀ : Subgroup (PQuot p L)}
    (hE₀ : IsElemAbelian p E₀) :
    ∃ W : Subgroup G, W ≤ L ∧ IsElemAbelian p W ∧ Nat.card W = Nat.card E₀ := by
  obtain ⟨S, hS, -, hScard⟩ := GLTheoremB.exists_elemAbelian_lift (GLAPPrimeCore p ↥L)
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 CFSG.pPrimeCore_coprime_card) hE₀
  refine ⟨S.map L.subtype, Subgroup.map_subtype_le S, isElemAbelian_map_hom hS L.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective, hScard]

theorem i1017_moreover (hR : I1017RowRanks) {p : ℕ} {L : Subgroup G} {x : G} (hx1 : x ≠ 1)
    (hxp : x ^ p = 1) (hL : GLAPComponent p (cx x) L) (row : Row) (hrow : RowL row p L) :
    ∃ E : Subgroup G, E ≤ L ⊔ Subgroup.zpowers x ∧ IsElemAbelian p E ∧
      p ^ row.rank < Nat.card E := by
  obtain ⟨rfl, hcat, hZ⟩ := hrow
  have hp : row.prime.Prime := by
    cases row <;> first | exact Nat.prime_three | exact Nat.prime_five
  haveI : Fact row.prime.Prime := ⟨hp⟩
  have hLx : L ≤ cx x := hL.1
  rcases rank_fact hR row with ⟨h1, hrk⟩ | ⟨h3, hp3, hrk⟩
  ·
    rw [h1] at hZ
    obtain ⟨E₀, hE₀, hE₀c⟩ := hrk (PQuot row.prime L) (L84.catalogIs_pQuot_of_center hZ hcat)
    obtain ⟨W, hWL, hW, hWc⟩ := exists_lift hE₀
    have hxL : x ∉ L := fun hx => hx1 (L84.eq_one_of_mem_core hp
      (L84.mem_core_of_centMod hZ hx (L84.centMod_of_comm hLx)) hxp)
    have hlt : W < W ⊔ Subgroup.zpowers x := SetLike.lt_iff_le_and_exists.2
      ⟨le_sup_left, x, Subgroup.mem_sup_right (Subgroup.mem_zpowers x), fun hx => hxL (hWL hx)⟩
    refine ⟨W ⊔ Subgroup.zpowers x, sup_le_sup_right hWL _,
      isElemAbelian_sup hW (isElemAbelian_zpowers hxp) fun a ha b hb => ?_, ?_⟩
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      exact (Commute.zpow_right
        (show Commute a x from Subgroup.mem_centralizer_singleton_iff.1 (hLx (hWL ha))) k).eq
    · calc row.prime ^ row.rank = Nat.card W := by rw [hWc, hE₀c]
        _ < Nat.card ↥(W ⊔ Subgroup.zpowers x) := Subgroup.card_lt_of_lt hlt
  ·
    obtain ⟨E₀, hE₀, hE₀c⟩ := hrk (PQuot row.prime L) hcat (hZ.trans h3)
    have hE₀' : IsElemAbelian row.prime E₀ :=
      ⟨hE₀.1, fun y hy => (congrArg (fun n : ℕ => y ^ n) hp3).trans (hE₀.2 y hy)⟩
    obtain ⟨W, hWL, hW, hWc⟩ := exists_lift hE₀'
    refine ⟨W, hWL.trans le_sup_left, hW, ?_⟩
    rw [hWc, hE₀c, hp3]
    exact Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self _)

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
