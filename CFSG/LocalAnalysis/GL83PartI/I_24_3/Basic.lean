module

public import CFSG.Open.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace GL83.I243

open CFSG.Open Subgroup

theorem normal_le_center_or_eq_top {Q : Type*} [Group Q] (hq : IsQuasisimple Q)
    (N : Subgroup Q) [N.Normal] : N ≤ center Q ∨ N = ⊤ := by
  have hs : IsSimpleGroup (Q ⧸ center Q) := hq.2
  have hperf : commutator Q = ⊤ := hq.1
  let π := QuotientGroup.mk' (center Q)
  have hnormal : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hker : N ≤ π.ker := N.map_eq_bot_iff.mp hbot
    simpa only [π, QuotientGroup.ker_mk'] using hker
  · right
    have hsup : N ⊔ center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq π N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hder : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [hperf] at hder
    exact top_unique hder

theorem pCore_le_center {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hq : IsQuasisimple Q) : CFSG.pCore p Q ≤ center Q := by
  have : Fact p.Prime := ⟨hp⟩
  haveI : (CFSG.pCore p Q).Normal := CFSG.pCore_normal
  rcases normal_le_center_or_eq_top hq (CFSG.pCore p Q) with h | h
  · exact h
  · exfalso
    have hpg : IsPGroup p (⊤ : Subgroup Q) := h ▸ CFSG.pCore_isPGroup
    have hnil : Group.IsNilpotent Q := (hpg.of_equiv Subgroup.topEquiv).isNilpotent
    have hperf : Group.IsPerfect Q := ⟨hq.1⟩
    haveI : Nontrivial (Q ⧸ center Q) := hq.2.toNontrivial
    have : Nontrivial Q := (QuotientGroup.mk'_surjective (center Q)).nontrivial
    exact Group.IsPerfect.not_isSolvable Q inferInstance

theorem dvd_card_center_of_pCore_ne_bot {Q : Type*} [Group Q] [Finite Q] {p : ℕ}
    (hp : p.Prime) (hq : IsQuasisimple Q) (h : CFSG.pCore p Q ≠ ⊥) :
    p ∣ Nat.card (center Q) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := p) (G := Q)).exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact h (Subgroup.card_eq_one.mp (by simpa using hn))
  have hdvd : Nat.card (CFSG.pCore p Q) ∣ Nat.card (center Q) :=
    Subgroup.card_dvd_of_le (pCore_le_center hp hq)
  rw [hn] at hdvd
  exact (dvd_pow_self p hn0).trans hdvd

end GL83.I243
