module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefs
import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux
import CFSG.LocalAnalysis.AGLEmbedding.ResidualFiveOddCore
import CFSG.LocalAnalysis.AGLEmbedding.OddCoreRank

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section OddCore

variable {G : Type} [Group G] [Finite G]

theorem barM_le_centralizer_pCore_or_four_le_pRank {p : ℕ} [Fact p.Prime] {M Z : Subgroup G}
    (hZM : Z ≤ M) (hZb : IsElemAbelian p (barM M Z)) (hZ2 : p ^ 2 ≤ Nat.card (barM M Z))
    (hirr : ∃ (r : ℕ) (t : G), 4 ≤ r ∧ t ∈ M ∧ t ∈ Subgroup.normalizer (Z : Set G) ∧
      ∀ k : ℕ, ¬ r ∣ k → ∀ Y : Subgroup G, Y ≤ Z →
        t ^ k ∈ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = Z)
    {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hsp : s ≠ p) :
    barM M Z ≤ Subgroup.centralizer
        ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
          Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
      4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) := by
  by_cases hns : barM M Z ≤ Subgroup.centralizer
      ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
        Set (↥M ⧸ CFSG.pCore 2 ↥M))
  · exact Or.inl hns
  right
  have hp : p.Prime := Fact.out
  have := Fact.mk hs
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥M) with hmk
  set Sg := CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) with hSg
  obtain ⟨r, t, hr4, htM, htZ, hirr⟩ := hirr
  have hSgN : (⊤ : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) ≤ Subgroup.normalizer (Sg : Set _) :=
    (Subgroup.normalizer_eq_top (H := Sg)).ge
  have hrank : r ≤ Open.pRank s Sg := by
    refine stmtOddCoreRank' hs hs2 hp hsp Sg (barM M Z) (mk ⟨t, htM⟩)
      CFSG.pCore_isPGroup (le_top.trans hSgN) hZb hZ2
      (hSgN (Subgroup.mem_top _)) (mem_normalizer_barM htM htZ) (fun k hk Y₀ hY₀ hkY₀ => ?_)
      hns
    have htk : mk ⟨t, htM⟩ ^ k = mk ⟨t ^ k, M.pow_mem htM k⟩ := by
      rw [← map_pow]
      rfl
    rw [htk] at hkY₀
    exact eq_bot_or_eq_barM_of_mem_normalizer hZM (M.pow_mem htM k)
      (Subgroup.pow_mem _ htZ k) (hirr k hk) hY₀ hkY₀
  have h1 := pRank_barM_le hs hs2 M ((Sg.comap mk).map M.subtype) (Subgroup.map_subtype_le _)
  rw [barM_preimage] at h1
  omega

end OddCore

theorem stmtOneLieOddCore :
    ∀ {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {n e : ℕ} {P : Sylow p G}
      {M H R Np Z : Subgroup G}, D1OneLieMData p n e P M H R Np Z →
      ∀ s : ℕ, s.Prime → s ≠ 2 → s ≠ p →
        barM M Z ≤ Subgroup.centralizer
          ((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M) : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)) :
            Set (↥M ⧸ CFSG.pCore 2 ↥M)) ∨
        4 ≤ Open.pRank s (((CFSG.pCore s (↥M ⧸ CFSG.pCore 2 ↥M)).comap
          (QuotientGroup.mk' (CFSG.pCore 2 ↥M))).map M.subtype) := by
  intro G _ _ p _ n e P M H R Np Z h s hs hs2 hsp
  obtain ⟨r, t, hr4, htK, htZ, hirr⟩ := h.exists_irr
  exact barM_le_centralizer_pCore_or_four_le_pRank (h.le_R.trans h.ph3.le_M)
    h.isElemAbelian_barM' (h.card_barM' ▸ h.two_le_card) ⟨r, t, hr4, htK.2, htZ, hirr⟩ hs hs2 hsp

end CFSG.AGLEmbedding
