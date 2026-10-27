module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Check

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.RankThree.Native

theorem gensOK_chS : chS.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chS : chS.baseFin.Nodup := by decide

theorem gensOK_chX1 : chX1.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chX1 : chX1.baseFin.Nodup := by decide

theorem gensOK_chX2 : chX2.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chX2 : chX2.baseFin.Nodup := by decide

theorem gensOK_chX3 : chX3.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chX3 : chX3.baseFin.Nodup := by decide

theorem gensOK_chK1 : chK1.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chK1 : chK1.baseFin.Nodup := by decide

theorem gensOK_chK2 : chK2.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chK2 : chK2.baseFin.Nodup := by decide

theorem gensOK_chA1 : chA1.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA1 : chA1.baseFin.Nodup := by decide

theorem gensOK_chA2 : chA2.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA2 : chA2.baseFin.Nodup := by decide

theorem gensOK_chK1A1 : chK1A1.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chK1A1 : chK1A1.baseFin.Nodup := by decide

theorem gensOK_chK2A2 : chK2A2.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chK2A2 : chK2A2.baseFin.Nodup := by decide

theorem gensOK_chL : chL.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chL : chL.baseFin.Nodup := by decide

theorem gensOK_chB12 : chB12.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chB12 : chB12.baseFin.Nodup := by decide

theorem gensOK_chB23 : chB23.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chB23 : chB23.baseFin.Nodup := by decide

theorem gensOK_chSJ : chSJ.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chSJ : chSJ.baseFin.Nodup := by decide

theorem gensOK_chT1 : chT1.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chT1 : chT1.baseFin.Nodup := by decide

theorem gensOK_chT2 : chT2.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chT2 : chT2.baseFin.Nodup := by decide

theorem card_chS : Nat.card chS.grp = 32768 := by
  rw [ChainData.card_grp tabs_check gensOK_chS chS_ok nodup_chS, chS_order]

theorem mem_chS_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chS.grp ↔ siftA 693 lvS chS.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chS chS_ok nodup_chS hG

theorem card_chX1 : Nat.card chX1.grp = 4 := by
  rw [ChainData.card_grp tabs_check gensOK_chX1 chX1_ok nodup_chX1, chX1_order]

theorem mem_chX1_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chX1.grp ↔ siftA 693 lvX1 chX1.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chX1 chX1_ok nodup_chX1 hG

theorem card_chX2 : Nat.card chX2.grp = 4 := by
  rw [ChainData.card_grp tabs_check gensOK_chX2 chX2_ok nodup_chX2, chX2_order]

theorem mem_chX2_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chX2.grp ↔ siftA 693 lvX2 chX2.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chX2 chX2_ok nodup_chX2 hG

theorem card_chX3 : Nat.card chX3.grp = 2 := by
  rw [ChainData.card_grp tabs_check gensOK_chX3 chX3_ok nodup_chX3, chX3_order]

theorem mem_chX3_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chX3.grp ↔ siftA 693 lvX3 chX3.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chX3 chX3_ok nodup_chX3 hG

theorem card_chK1 : Nat.card chK1.grp = 25920 := by
  rw [ChainData.card_grp tabs_check gensOK_chK1 chK1_ok nodup_chK1, chK1_order]

theorem mem_chK1_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chK1.grp ↔ siftA 693 lvK1 chK1.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chK1 chK1_ok nodup_chK1 hG

theorem card_chK2 : Nat.card chK2.grp = 20160 := by
  rw [ChainData.card_grp tabs_check gensOK_chK2 chK2_ok nodup_chK2, chK2_order]

theorem mem_chK2_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chK2.grp ↔ siftA 693 lvK2 chK2.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chK2 chK2_ok nodup_chK2 hG

theorem card_chA1 : Nat.card chA1.grp = 512 := by
  rw [ChainData.card_grp tabs_check gensOK_chA1 chA1_ok nodup_chA1, chA1_order]

theorem mem_chA1_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chA1.grp ↔ siftA 693 lvA1 chA1.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chA1 chA1_ok nodup_chA1 hG

theorem card_chA2 : Nat.card chA2.grp = 512 := by
  rw [ChainData.card_grp tabs_check gensOK_chA2 chA2_ok nodup_chA2, chA2_order]

theorem mem_chA2_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chA2.grp ↔ siftA 693 lvA2 chA2.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chA2 chA2_ok nodup_chA2 hG

theorem card_chK1A1 : Nat.card chK1A1.grp = 13271040 := by
  rw [ChainData.card_grp tabs_check gensOK_chK1A1 chK1A1_ok nodup_chK1A1, chK1A1_order]

theorem mem_chK2A2_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chK2A2.grp ↔ siftA 693 lvK2A2 chK2A2.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chK2A2 chK2A2_ok nodup_chK2A2 hG

theorem card_chL : Nat.card chL.grp = 9196830720 := by
  rw [ChainData.card_grp tabs_check gensOK_chL chL_ok nodup_chL, chL_order]

theorem card_chB12 : Nat.card chB12.grp = 60 := by
  rw [ChainData.card_grp tabs_check gensOK_chB12 chB12_ok nodup_chB12, chB12_order]

theorem card_chB23 : Nat.card chB23.grp = 60 := by
  rw [ChainData.card_grp tabs_check gensOK_chB23 chB23_ok nodup_chB23, chB23_order]

theorem card_chSJ : Nat.card chSJ.grp = 98304 := by
  rw [ChainData.card_grp tabs_check gensOK_chSJ chSJ_ok nodup_chSJ, chSJ_order]

theorem mem_chSJ_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chSJ.grp ↔ siftA 693 lvSJ chSJ.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chSJ chSJ_ok nodup_chSJ hG

theorem card_chT1 : Nat.card chT1.grp = 64 := by
  rw [ChainData.card_grp tabs_check gensOK_chT1 chT1_ok nodup_chT1, chT1_order]

theorem mem_chT1_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chT1.grp ↔ siftA 693 lvT1 chT1.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chT1 chT1_ok nodup_chT1 hG

theorem card_chT2 : Nat.card chT2.grp = 64 := by
  rw [ChainData.card_grp tabs_check gensOK_chT2 chT2_ok nodup_chT2, chT2_order]

theorem mem_chT2_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chT2.grp ↔ siftA 693 lvT2 chT2.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chT2 chT2_ok nodup_chT2 hG

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
