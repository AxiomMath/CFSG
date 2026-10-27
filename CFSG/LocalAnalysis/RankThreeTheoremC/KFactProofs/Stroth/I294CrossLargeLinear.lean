module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossLargeTransfer
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.CrossPSL
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294OuterDiagRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Open CFSG.GroupTheory.WeirSylow CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

theorem I294Large.rank_psl {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) {F : Type} [Field F] [Finite F]
    (hrF : ¬ r ∣ Nat.card F) {n : ℕ} (hLU : ¬ (r ∣ n ∧ r ∣ Nat.card F - 1))
    (hS : ∃ S : Sylow r (StatedProj (StatedSL n F)),
      ¬ IsMulCommutative (S : Subgroup (StatedProj (StatedSL n F)))) :
    4 ≤ CFSG.Open.pRank r (⊤ : Subgroup (StatedProj (StatedSL n F))) := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fintype F := Fintype.ofFinite F
  have hrF' : ¬ r ∣ Fintype.card F := by rwa [← Nat.card_eq_fintype_card]
  have hr1 : Odd r := hr.odd_of_ne_two (by omega)
  have hGL : ∀ P : Sylow r (GL (Fin n) F), Nonempty (P ≃* sigmaModel r
      (orderOf (Fintype.card F : ZMod r))
      (padicValNat r (Fintype.card F ^ orderOf (Fintype.card F : ZMod r) - 1)) n) :=
    fun P => sylow_GL hr1 F hrF' n P
  obtain ⟨S, hS'⟩ := hS
  by_cases hA : r ∣ Nat.card F - 1
  · have he : orderOf (Fintype.card F : ZMod r) = 1 := by
      rw [orderOf_eq_one_iff, ← Nat.card_eq_fintype_card]
      have h1 : (((Nat.card F - 1 : ℕ)) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hA
      have hpos : 1 ≤ Nat.card F := Nat.card_pos
      rw [Nat.cast_sub hpos, Nat.cast_one, sub_eq_zero] at h1
      exact h1
    by_cases hnr : n < r
    · exfalso
      have hc := sylow_isMulCommutative_of_sigmaModel_of_lt hr
        (G := GL (Fin n) F) (e := orderOf (Fintype.card F : ZMod r))
        (a := padicValNat r (Fintype.card F ^ orderOf (Fintype.card F : ZMod r) - 1)) (N := n)
        (by rw [he, Nat.div_one]; exact hnr) hGL
      exact hS' (sylow_comm_of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
        (sylow_comm_of_subgroup (StatedSL n F) hc) S)
    · push Not at hnr
      have hn6 : 6 ≤ n := by
        by_contra h
        have h5n : n = 5 := by omega
        have hr5 : r = 5 := by omega
        exact hLU ⟨by rw [h5n, hr5], hA⟩
      exact odFour_le_pRank_psl hr hn6 hA
  · have hamb : I294Large.CommOrRank r (GL (Fin n) F) :=
      I294Large.CommOrRank.of_sylow_sigmaModel hr (PSLCross.one_le_padicValNat_card hr hrF') hGL
    haveI : (StatedSL n F).Normal := by
      rw [CFSG.Open.StatedAPI.statedSL_eq_ker_det]; infer_instance
    have hSL : I294Large.CommOrRank r ↥(StatedSL n F) :=
      I294Large.CommOrRank.of_normal_coprime_index hr _
        (fun hd => hA (hd.trans (PSLCross.index_statedSL_dvd n))) hamb
    have hPSL : I294Large.CommOrRank r (StatedProj (StatedSL n F)) :=
      I294Large.CommOrRank.of_surjective_coprime_ker hr (QuotientGroup.mk' _)
        (QuotientGroup.mk'_surjective _)
        (by
          rw [QuotientGroup.ker_mk']
          exact fun hd => hA (hd.trans (PSLCross.card_scalars_subgroupOf_dvd n))) hSL
    rcases hPSL with hc | hrk
    · exact (hS' (hc S)).elim
    · omega

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
