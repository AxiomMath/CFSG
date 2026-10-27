module

import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1YLayer
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1Basic
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Family
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank62zH1XBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {f : ℕ} {X Q : Subgroup G}

omit [Finite G] in
theorem k631a_index_sup_dvd {N O : Subgroup G} (hON : O ≤ normalizer (N : Set G)) :
    (N.subgroupOf (N ⊔ O)).index ∣ Nat.card O := by
  have hNA : N ≤ N ⊔ O := le_sup_left
  have hOA : O ≤ N ⊔ O := le_sup_right
  have : (N.subgroupOf (N ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).2 (sup_le Subgroup.le_normalizer hON)
  have htop : O.subgroupOf (N ⊔ O) ⊔ N.subgroupOf (N ⊔ O) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hOA hNA, sup_comm, Subgroup.subgroupOf_self]
  have h1 := Subgroup.relIndex_sup_right (O.subgroupOf (N ⊔ O)) (N.subgroupOf (N ⊔ O))
  rw [htop, Subgroup.relIndex_top_right] at h1
  rw [h1]
  exact (Subgroup.relIndex_dvd_card _ _).trans
    (dvd_of_eq (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOA).toEquiv))

omit [Finite G] in
theorem k631a_mem_of_mem_sup_odd {N O : Subgroup G} (hON : O ≤ normalizer (N : Set G))
    (hO : Odd (Nat.card O)) {y : G} (hy : y ∈ N ⊔ O) {m : ℕ} (hym : y ^ 2 ^ m = 1) : y ∈ N := by
  have hNA : N ≤ N ⊔ O := le_sup_left
  have : (N.subgroupOf (N ⊔ O)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).2 (sup_le Subgroup.le_normalizer hON)
  have h1 : y ^ (N.subgroupOf (N ⊔ O)).index ∈ N := by
    have h2 := Subgroup.pow_index_mem (N.subgroupOf (N ⊔ O)) (⟨y, hy⟩ : ↥(N ⊔ O))
    exact Subgroup.mem_subgroupOf.1 h2
  have hodd : Odd (N.subgroupOf (N ⊔ O)).index := hO.of_dvd_nat (k631a_index_sup_dvd hON)
  have hcop : Nat.Coprime (N.subgroupOf (N ⊔ O)).index (2 ^ m) :=
    (Nat.coprime_two_right.mpr hodd).pow_right m
  exact k631a_mem_of_pow_mem hcop h1 (by rw [hym]; exact N.one_mem)

theorem k631a_core_le_normalizer_layer (f : ℕ) (X : Subgroup G) :
    GLAPPrimeCoreOf f X ≤ normalizer (GLAPLayer f X : Set G) := by
  have h := i183_le_normalizer_biSup (H := GLAPPrimeCoreOf f X)
    (S := {L | GLAPComponent f X L}) fun L hL => i183_glaPPrimeCoreOf_le_normalizer hL
  unfold GLAPLayer
  rw [sSup_eq_iSup]
  exact h

theorem k631a_layer (hInn : KFactInnerAction) (hL : LayerHyp f X Q) {Y V : Subgroup G}
    (hYX : Y ≤ X) (hY2 : IsPGroup 2 Y) (hVQ : V ≤ Q) (hYV : ⁅Y, V⁆ = Y) :
    Y ≤ GLAPLayer f X := by
  have hX := k631a_hyp_of_layer hL
  have hB := k631a_bhyp_barX hX
  have hVX : V ≤ X := hVQ.trans hL.le
  have hYb : IsPGroup 2 ↥(barX f X Y) :=
    (hY2.of_equiv (Subgroup.subgroupOfEquivOfLe hYX).symm).map (QuotientGroup.mk' _)
  have hVb : barX f X V ≤ barX f X Q := barX_mono f hVQ
  have hcomm : ⁅barX f X Y, barX f X V⁆ = barX f X Y := by
    rw [← barX_commutator f hYX hVX, hYV]
  have hlay := k631a_layer_le hInn hB hYb hVb hcomm
  have hlb : CFSG.layer (↥X ⧸ GLAPPrimeCore f ↥X) ≤ barX f X (GLAPLayer f X) := by
    refine sSup_le fun K hK => ?_
    obtain ⟨L, hLc, rfl⟩ :=
      exists_glaPComponent_barX_eq (p := f) X ((CFSG.isComponent_iff_open K).1 hK)
    exact barX_mono f (le_sSup hLc)
  intro y hy
  have hyX := hYX hy
  obtain ⟨x, hxX, hxL, hxy⟩ := k631a_mem_barX.1 (hlb (hlay (k631a_mk_mem_barX hyX hy)))
  have hn := (k631a_mk_eq_iff hxX hyX).1 hxy
  have hyNO : y ∈ GLAPLayer f X ⊔ GLAPPrimeCoreOf f X := by
    have := Subgroup.mul_mem_sup hxL hn
    rwa [mul_inv_cancel_left] at this
  obtain ⟨m, hm⟩ := hY2 ⟨y, hy⟩
  exact k631a_mem_of_mem_sup_odd (k631a_core_le_normalizer_layer f X) hL.odd hyNO
    (by simpa using congrArg Subtype.val hm)

end CFSG.LocalAnalysis.RankThreeTheoremC
