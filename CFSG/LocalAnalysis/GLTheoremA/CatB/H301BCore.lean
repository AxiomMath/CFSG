module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BRank
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeSporadicRank
import CFSG.LargeExtraspecial.BridgeNat
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BImage
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BKernel
import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BType

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8
open CFSG.HardMathSupport.Timmesfeld.Coordinator

variable {G : Type} [Group G] [Finite G]

theorem i301B_core (hOut : SporadicOuterLeTwo)
    (hT : CFSG.RankThree.PartTwo.Sec4.Census.SporadicMultipliers) (h : I301BRes)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a y : G} {J Bs I K R0 : Subgroup G} {row : Row}
    (ha : orderOf a = p) (hodd : Odd (Nat.card (GLAPPrimeCoreOf p (cx a))))
    (hJ : GLAPComponent p (cx a) J) (hprow : p = row.prime)
    (hJcat : catalogIs (PSimple p J) (sporIs row.name)) (hBs : GLAIsBmax p Bs)
    (hBsX : Bs ≤ cx a) (hBscard : Nat.card Bs = p ^ row.rank)
    (hb : ∃ b ∈ Bs, b ≠ 1 ∧ CentMod p J b) (hy : y ∈ Bs)
    (hI : GLAPComponent p (J ⊓ cx y) I) (hIrow : RowI row p I)
    (hR0y : R0 ≤ cx y) (hR0 : IsExtraSpec2 R0 ∨ Nat.card R0 = 2)
    (hKd : K ≤ (cx a ⊓ cx y) ⊔ GLAPPrimeCoreOf p (cx a))
    (hKR0 : K ⊔ Bs ≤ Subgroup.normalizer (R0 : Set G)) (hK : RowK row p K)
    (hR0card : Nat.card R0 = 2 ^ row.r0exp) {R1 : Subgroup G} (hR1X : R1 ≤ cx a)
    (hR1 : IsPGroup 2 R1) (hKR1 : K ⊔ Bs ≤ Subgroup.normalizer (R1 : Set G)) (hR01 : R0 < R1) :
    IsExtraSpec2 R1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hrank : GLATwoLocalRank p G = row.rank :=
    Nat.pow_right_injective hp.two_le (hBs.2.1.symm.trans hBscard)
  have hrk1 : ∀ A : Subgroup G, IsElemAbelian p A → (∀ x ∈ A, CentMod p J x) → Nat.card A ≤ p :=
    fun A hA hAJ => card_le_prime_of_row hT h hp hp2 hJ hprow hJcat hrank hA hAJ
  have hXN := cx_le_normalizer_of_rankOne hp hp2 ha hJ hrk1
  have hrow : I301BRow row := by
    cases row with
    | ly => exact h.rowLy
    | co2 => exact h.rowCo2
    | co1 => exact h.rowCo1
    | fi24 | fi24h => exact h.rowFi24
    | suz | suzh => exact h.rowSuz
    | th => exact h.rowTh
    | m3 => exact h.rowM3
    | m5 => exact h.rowM5
  have hdist : I301BDistinct row := by
    cases row with
    | ly => exact h.distLy
    | co2 => exact h.distCo2
    | co1 => exact h.distCo1
    | fi24 | fi24h => exact h.distFi24
    | suz | suzh => exact h.distSuz
    | th => exact h.distTh
    | m3 => exact h.distM3
    | m5 => exact h.distM5
  have hr1 : 1 ≤ row.rank := by cases row <;> decide
  have hOX : GLAPPrimeCoreOf p (cx a) ≤ cx a := by
    unfold GLAPPrimeCoreOf
    exact Subgroup.map_subtype_le _
  have hIJ : I ≤ J := hI.1.trans inf_le_left
  have hIX : I ≤ cx a := hIJ.trans hJ.1
  have hR0X : R0 ≤ cx a := hR01.le.trans hR1X
  have hKX : K ≤ cx a := hKd.trans (sup_le inf_le_left hOX)
  have hyN : y ∈ Subgroup.normalizer (J : Set G) := hXN (hBsX hy)
  have hR0N := hR0X.trans hXN
  have hR1N := hR1X.trans hXN
  obtain ⟨e0⟩ := nonempty_mulEquiv_phiImg hp hp2 ha hJ hrk1 hodd hR0X (hR1.to_le hR01.le)
  obtain ⟨e1⟩ := nonempty_mulEquiv_phiImg hp hp2 ha hJ hrk1 hodd hR1X hR1
  have hD : Nat.card (Bs ⊓ centModSubgroup p J : Subgroup G) = p := by
    obtain ⟨b, hbB, hb1, hbJ⟩ := hb
    refine le_antisymm (hrk1 _ (hBs.1.mono inf_le_left) fun x hx => centMod_iff.2 hx.2) ?_
    calc p = Nat.card (Subgroup.zpowers b) := by
          rw [Nat.card_zpowers, orderOf_eq_prime (hBs.1.2 b hbB) hb1]
      _ ≤ _ := Subgroup.card_le_of_le (Subgroup.zpowers_le.2
        (show b ∈ Bs ⊓ centModSubgroup p J from ⟨hbB, centMod_iff.1 hbJ⟩))
  have hy1 : L62.phiC p J ⟨y, hyN⟩ ≠ 1 := by
    intro hy1
    have hyJ : CentMod p J y := (L62.phiC_eq_one_iff hp hJ hyN).1 hy1
    have haJ : CentMod p J a := CFSG.LocalAnalysis.GLTheoremA.centMod_of_mem_centralizer
      (Subgroup.mem_centralizer_iff.2 fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hl))
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_centMod ha haJ hrk1
      (hBs.1.2 y hy) hyJ (Subgroup.mem_centralizer_singleton_iff.1 (hBsX hy)).symm)
    have hJy : J ≤ cx y := fun l hl => by
      rw [Subgroup.mem_centralizer_singleton_iff, ← hk]
      exact (Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.1 (hJ.1 hl)) k).eq
    rw [inf_eq_left.2 hJy] at hI
    have hIeq : I = J := glaPComponent_eq_of_isQuasisimple
      (isQuasisimple_pQuot_of_glaPComponent hp hJ) hI
      (GLTheoremB.glaPComponent_of_le hp hJ le_rfl hJ.1)
    rw [hIeq] at hIrow
    exact hdist _ hJcat hIrow.1
  subst hprow
  set N := Subgroup.normalizer (J : Set G) with hN
  set Φ := L62.phiC row.prime J with hΦ
  have hsp : catalogIs (PSimple row.prime J) isSporIndex := by
    obtain ⟨i, hi, e⟩ := hJcat
    unfold sporIs at hi
    subst hi
    exact ⟨.sporadic row.name, trivial, e⟩
  have h3 : Nat.card ((Bs.subgroupOf N).map Φ) = row.prime ^ (row.rank - 1) := by
    have hmul := card_phiImg_mul hp hJ (hBsX.trans hXN)
    rw [hD, hBscard, ← Nat.sub_add_cancel hr1, pow_succ] at hmul
    exact Nat.eq_of_mul_eq_mul_right hp.pos hmul
  have h10 : IsExtraSpec2 ((R0.subgroupOf N).map Φ) ∨ Nat.card ((R0.subgroupOf N).map Φ) = 2 :=
    hR0.imp (CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv e0)
      fun h2 => (Nat.card_congr e0.toEquiv).symm.trans h2
  have h17 : (R0.subgroupOf N).map Φ < (R1.subgroupOf N).map Φ := by
    refine lt_of_le_of_ne (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.2
      (hR01.le (Subgroup.mem_subgroupOf.1 hx))) fun heq => (Subgroup.card_lt_of_lt hR01).ne ?_
    rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, heq]
  have key := hrow (PSimple row.prime J) hJcat ((Bs.subgroupOf N).map Φ) ((I.subgroupOf N).map Φ)
    ((K.subgroupOf N).map Φ) ((R0.subgroupOf N).map Φ) ((R1.subgroupOf N).map Φ) (Φ ⟨y, hyN⟩)
    (phiImg_le_range_conj hOut hp hp2 hJ hsp hBs.1.2) ((hBs.1.subgroupOf N).map Φ) h3
    ⟨⟨y, hyN⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩ hy1 (phiImg_le_range_conj_of_le hIJ)
    (phiImg_le_cx hp hJ hXN hyN (le_sup_of_le_left (le_inf hIX (hI.1.trans inf_le_right))))
    (mapsOntoType_phiC hp hp2 ha hJ hrk1 hI hIX hIrow.1)
    (phiImg_le_cx hp hJ hXN hyN (le_sup_of_le_left (le_inf hR0X hR0y))) h10
    ((Nat.card_congr e0.toEquiv).symm.trans hR0card) (phiImg_le_cx hp hJ hXN hyN hKd)
    (rowKS_phiC hp hp2 ha hJ hrk1 rfl hKX hK)
    (sup_le (phiImg_le_normalizer hR0N (le_sup_left.trans hKR0))
      (phiImg_le_normalizer hR0N (le_sup_right.trans hKR0))) (hR1.of_equiv e1)
    (sup_le (phiImg_le_normalizer hR1N (le_sup_left.trans hKR1))
      (phiImg_le_normalizer hR1N (le_sup_right.trans hKR1))) h17
  exact CFSG.LargeExtraspecial.Bridge.timmesfeldIsExtraspecial_of_mulEquiv e1.symm key

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
