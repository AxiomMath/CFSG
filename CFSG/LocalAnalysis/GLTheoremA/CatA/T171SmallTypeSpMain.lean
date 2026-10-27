module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeSpWitness
public import CFSG.LocalAnalysis.GLTheoremA.CatB.RankFineSp
import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSpRootBig

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open CFSG.Open
open CFSG.StandardType.SpRootBig (seven_dvd_card_statedSp)

theorem not_smallOrd_of_mulEquiv_statedSp {G : Type} [Group G] {L : Subgroup G} {k : ℕ}
    (hk : 3 ≤ k) (e : ↥L ≃* StatedSp k (ZMod 2)) :
    ¬ HStdExcl.SmallOrd L := by
  intro h
  unfold HStdExcl.SmallOrd at h
  have hcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = Nat.card (StatedSp k (ZMod 2)) := by
    have h1 := Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥L)
      (Subgroup.center (StatedSp k (ZMod 2))) e (Subgroup.map_center_eq e)).toEquiv
    rw [h1]
    have hZ : Subgroup.center (StatedSp k (ZMod 2)) = ⊥ :=
      CFSG.Timmesfeld.Transvection.center_statedSp_eq_bot (n := k) (K := ZMod 2) (by omega)
    rw [hZ]
    exact Nat.card_congr (QuotientGroup.quotientBot).toEquiv
  rw [hcard] at h
  have h7 := seven_dvd_card_statedSp (ZMod 2) hk
  rcases h with h | h <;> rw [h] at h7 <;> norm_num at h7

theorem noSmallModel_statedSp_zmod_two (hBlock : SpOneBlock) (n : ℕ) (hn : 3 ≤ n) :
    NoSmallModel (StatedSp n (ZMod 2)) := by
  intro Bb h
  obtain ⟨T, hT, hTne, hTnorm⟩ := h.twoLocal
  have hle : Nat.card Bb ≤ 3 ^ (n - 1) :=
    CFSG.LocalAnalysis.GLTheoremA.CatB.rankFine_statedSp_two n Bb T h.elem hT hTne hTnorm
  rcases Nat.lt_or_ge n 4 with hn3 | hn4
  · have hn3' : n = 3 := by omega
    subst hn3'
    norm_num at hle
    have hge : 27 ≤ Nat.card Bb := h.card_ge
    omega
  · rcases Nat.lt_or_ge n 6 with hn5 | hn6
    · have hn5' : n ≤ 5 := by omega
      obtain ⟨y, hy, hy1, hstd, ⟨e⟩⟩ := hBlock n hn4 hn5' Bb h
      exact not_smallOrd_of_mulEquiv_statedSp (k := n - 1) (by omega) e
        (h.small y hy hy1 hstd)
    · obtain ⟨E, hEelem, hEcard, hEtwo⟩ := exists_twoLocal_elementaryAbelian n 5 (by omega)
      have hmax := h.max E hEelem hEtwo
      rw [hEcard] at hmax
      have h81 := h.card_le
      norm_num at hmax h81
      omega

theorem famSp_of_spOneBlock (hBlock : SpOneBlock) : FamSp := by
  intro n q hv hq hn
  obtain ⟨e⟩ := nonempty_mulEquiv_lie_statedSp n q hv hq hn
  exact noSmallModel_of_mulEquiv e (noSmallModel_statedSp_zmod_two hBlock n hn)

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
