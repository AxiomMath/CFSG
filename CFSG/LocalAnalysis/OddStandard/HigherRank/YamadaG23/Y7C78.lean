module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C77
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7C79m
public import CFSG.Sporadic.Schreier.Co1WeightChar

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

theorem y7c_card_SL3Four : Nat.card SL3Four = 60480 := by
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 2) = 4 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
    norm_num
  unfold SL3Four
  rw [Matrix.card_SL_field, hq, Fin.prod_univ_three]
  norm_num

theorem y7c_card_K_of_gl3pair {G : Type} [Group G] [Finite G] {M L1 L2 K : Subgroup G}
    (h : Gl3Pair M L1 L2) (hK : L1 ⊔ L2 = K) : Nat.card K = 168 ^ 2 * Nat.card M := by
  have hprod := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_sup_mul_card_inf
    (A := L1) (B := L2) h.symm.L1_le_normalizer_L2
  rw [h.inf, hK, h.ext1.card_eq, h.ext2.card_eq] at hprod
  have hpos : 0 < Nat.card M := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [hprod]
  ring

theorem y7c_not_secProp_sl3Four {G : Type} [Group G] [Finite G] {M K : Subgroup G} (hMK : M ≤ K)
    (hcard : Nat.card K = 168 ^ 2 * Nat.card M) :
    ¬ SecProp K M (fun Y _ _ _ => Nonempty (Y ≃* SL3Four)) := by
  rintro ⟨hn, ⟨e⟩⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (M.subgroupOf K)
  have h2 : Nat.card (M.subgroupOf K) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMK).toEquiv
  have h3 : Nat.card (↥K ⧸ M.subgroupOf K) = 60480 :=
    (Nat.card_congr e.toEquiv).trans y7c_card_SL3Four
  rw [h2, h3, hcard] at h1
  have hpos : 0 < Nat.card M := Nat.card_pos
  have : 168 ^ 2 = 60480 := Nat.eq_of_mul_eq_mul_right hpos h1
  omega

theorem y7c_78_of_compPre {G : Type} [Group G] [Finite G] {L : Subgroup G} (hB : Sec3Inputs)
    (hS : HRSetting G L) (hL : HRG23 (L ⧸ center L)) (c : Ctx7 G L) (h5 : c.toCtx5.Facts5)
    {L1 : Subgroup G} (hcomp : IsCompPre c.s L1) : c.Fact78 := by
  obtain ⟨hMle, hL1K, hsup, hinf, hcomm, hsec⟩ := hcomp
  have hH : F33Hyp c.s c.e := f33hyp_of hB hS hL c.s c.e
  have hpair : Gl3Pair (M3 c.s) L1 (conjSub c.s.t L1) :=
    { elem := y7c_M3_elem c hH h5.2.2.2.2.2
      card := y7c_card_M3 c.toCtx5 hH
      inf := hinf
      comm := hcomm
      ext1 := ⟨hMle, hsec⟩
      ext2 := y7c_isGL3Ext_conjSub ⟨hMle, hsec⟩ (y7c_conjSub_t_M3 c.toCtx5 hH) }
  exact y7c_not_secProp_sl3Four (hMle.trans hL1K) (y7c_card_K_of_gl3pair hpair hsup)

theorem sec78_holds (hB : Sec3Inputs) (hI31 : CFSG.ASVolI.I_3_1) (hN24 : Nar24)
    (hSM : Nat.card
      (CFSG.Open.griessHopfMultiplier (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ∣ 2) :
    Sec78 := by
  intro G _ _ L hS hL c h5 h77
  obtain ⟨-, L1, hL1⟩ := sec77_strong hB hI31 hN24 hSM hS hL c h5 h77.1
  exact y7c_78_of_compPre hB hS hL c h5 hL1

end CFSG.OddStandard.HigherRank.YamadaG23
