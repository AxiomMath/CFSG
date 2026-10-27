module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3XCheck
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaSec3Check

public noncomputable section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaSec3

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Monster.B.Fischer CFSG.RankThree.Native

theorem gensOK_chA3 : chA3.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA3 : chA3.baseFin.Nodup := by decide

theorem gensOK_chA4 : chA4.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chA4 : chA4.baseFin.Nodup := by decide

theorem gensOK_chX8 : chX8.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chX8 : chX8.baseFin.Nodup := by decide

theorem gensOK_chSig : chSig.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chSig : chSig.baseFin.Nodup := by decide

theorem gensOK_chLam : chLam.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chLam : chLam.baseFin.Nodup := by decide

theorem gensOK_chZ2S : chZ2S.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chZ2S : chZ2S.baseFin.Nodup := by decide

theorem gensOK_chX6Z : chX6Z.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chX6Z : chX6Z.baseFin.Nodup := by decide

theorem gensOK_chZ : chZ.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chZ : chZ.baseFin.Nodup := by decide

theorem gensOK_chX1Z : chX1Z.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chX1Z : chX1Z.baseFin.Nodup := by decide

theorem gensOK_chP2 : chP2.GensOK := by unfold ChainData.GensOK; decide

theorem nodup_chP2 : chP2.baseFin.Nodup := by decide

theorem card_chA3 : Nat.card chA3.grp = 4096 := by
  rw [ChainData.card_grp tabs_check gensOK_chA3 chA3_ok nodup_chA3, chA3_order]

theorem mem_chA3_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chA3.grp ↔ siftA 693 lvA3 chA3.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chA3 chA3_ok nodup_chA3 hG

theorem card_chA4 : Nat.card chA4.grp = 16 := by
  rw [ChainData.card_grp tabs_check gensOK_chA4 chA4_ok nodup_chA4, chA4_order]

theorem mem_chA4_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chA4.grp ↔ siftA 693 lvA4 chA4.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chA4 chA4_ok nodup_chA4 hG

theorem card_chX8 : Nat.card chX8.grp = 4 := by
  rw [ChainData.card_grp tabs_check gensOK_chX8 chX8_ok nodup_chX8, chX8_order]

theorem mem_chX8_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chX8.grp ↔ siftA 693 lvX8 chX8.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chX8 chX8_ok nodup_chX8 hG

theorem card_chSig : Nat.card chSig.grp = 6 := by
  rw [ChainData.card_grp tabs_check gensOK_chSig chSig_ok nodup_chSig, chSig_order]

theorem card_chLam : Nat.card chLam.grp = 60 := by
  rw [ChainData.card_grp tabs_check gensOK_chLam chLam_ok nodup_chLam, chLam_order]

theorem card_chZ2S : Nat.card chZ2S.grp = 8 := by
  rw [ChainData.card_grp tabs_check gensOK_chZ2S chZ2S_ok nodup_chZ2S, chZ2S_order]

theorem mem_chZ2S_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chZ2S.grp ↔ siftA 693 lvZ2S chZ2S.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chZ2S chZ2S_ok nodup_chZ2S hG

theorem card_chX6Z : Nat.card chX6Z.grp = 32 := by
  rw [ChainData.card_grp tabs_check gensOK_chX6Z chX6Z_ok nodup_chX6Z, chX6Z_order]

theorem mem_chX6Z_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chX6Z.grp ↔ siftA 693 lvX6Z chX6Z.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chX6Z chX6Z_ok nodup_chX6Z hG

theorem card_chZ : Nat.card chZ.grp = 2 := by
  rw [ChainData.card_grp tabs_check gensOK_chZ chZ_ok nodup_chZ, chZ_order]

theorem mem_chZ_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chZ.grp ↔ siftA 693 lvZ chZ.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chZ chZ_ok nodup_chZ hG

theorem mem_chX1Z_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chX1Z.grp ↔ siftA 693 lvX1Z chX1Z.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chX1Z chX1Z_ok nodup_chX1Z hG

theorem card_chP2 : Nat.card chP2.grp = 1474560 := by
  rw [ChainData.card_grp tabs_check gensOK_chP2 chP2_ok nodup_chP2, chP2_order]

theorem mem_chP2_iff {g : Array ℕ} {G : Equiv.Perm (Fin 693)} (hG : Rep 693 g G) :
    G ∈ chP2.grp ↔ siftA 693 lvP2 chP2.B 0 g = true :=
  ChainData.mem_grp_iff tabs_check gensOK_chP2 chP2_ok nodup_chP2 hG

end CFSG.EvenSmallLie.UnitarySix.YamadaSec3
