module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKGQ

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

variable {A : Type} [Group A] [Finite A] {p : ℕ} {Kb Sb Bb Mb : Subgroup A} {z : A}

theorem n5_not_equiv_alt (c : KQCfg A p Kb Sb Bb Mb z)
    (hnb : ∀ b ∈ Bb, b ≠ 1 → ¬ ∀ k ∈ Kb, b * k = k * b)
    (hAutO : KFactAutAltOrder) {n : ℕ} (e : ↥Kb ≃* alternatingGroup (Fin n)) : False := by
  have hp := c.prime
  have hp2 : p ≠ 2 := by have := c.five_le; omega
  have hpdvd : p ∣ Nat.card ↥Kb := by
    have h1 : orderOf (⟨z, c.z_mem_K⟩ : ↥Kb) = p := by
      rw [Subgroup.orderOf_mk]
      exact c.z_order
    rw [← h1]
    exact orderOf_dvd_natCard _
  have hpn : p ≤ n := KGAlt.le_of_dvd_card_alt hp (by rwa [← Nat.card_congr e.toEquiv])
  have hn : n < 2 * p := KGAlt.lt_two_mul_of_pRank_le_one hp hp2 e c.rank
  obtain ⟨b, hbB, hb1, hbK⟩ := KGQ.exists_B1 c hAutO e hpn hn
  exact hnb b hbB hb1 hbK

theorem n5_kgroup_step4 (c : KQCfg A p Kb Sb Bb Mb z)
    (hnb : ∀ b ∈ Bb, b ≠ 1 → ¬ ∀ k ∈ Kb, b * k = k * b) (hAutO : KFactAutAltOrder)
    (h : IsChevSimple 2 ↥Kb ∨ ∃ n, Nonempty (↥Kb ≃* alternatingGroup (Fin n))) :
    KGStep4Concl A Kb Sb := by
  have hno : ∀ n : ℕ, ¬ Nonempty (↥Kb ≃* alternatingGroup (Fin n)) := fun n ⟨e⟩ =>
    n5_not_equiv_alt c hnb hAutO e
  exact ⟨h.resolve_right fun ⟨n, hn⟩ => hno n hn, fun ⟨⟨e⟩, _⟩ => hno 6 ⟨e⟩,
    fun n _ hn => hno n hn⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
