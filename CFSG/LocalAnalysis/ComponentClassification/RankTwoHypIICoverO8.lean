module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverSylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoHypIICoverO8Facts
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo2Pair
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicPairCensus
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeAut
public import CFSG.Blueprint.SourceClassicalTransport

public section

namespace CFSG.ComponentClassification.RankTwoHypIICover.O8

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoSporadic.Cert
open CFSG.ComponentClassification.RankTwoSporadic.RootCensus
open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native
open CFSG.EvenSmallLie.OmegaEight (omegaT autT sylowT repArrs repTypes repPerm)

theorem o8AutModel :
    AutModel ↥omegaT ↥autT (omegaT.subgroupOf autT) :=
  autModel_of_conj CFSG.EvenSmallLie.OmegaEight.omegaT_le_autT (MulEquiv.refl _)
    CFSG.EvenSmallLie.OmegaEight.autEquiv CFSG.EvenSmallLie.OmegaEight.autEquiv_apply

theorem index_omegaT : (omegaT.subgroupOf autT).index = 6 := by
  have h := (omegaT.subgroupOf autT).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    CFSG.EvenSmallLie.OmegaEight.omegaT_le_autT).toEquiv,
    CFSG.EvenSmallLie.OmegaEight.card_omegaT, CFSG.EvenSmallLie.OmegaEight.card_autT] at h
  omega

@[expose] noncomputable def o8Rep (j : ℕ) : ↥autT :=
  if hj : j < 38 then
    ⟨repPerm j, CFSG.EvenSmallLie.OmegaEight.sylowT_le_autT
      (CFSG.EvenSmallLie.OmegaEight.repPerm_spec hj).2⟩
  else 1

theorem coe_o8Rep {j : ℕ} (hj : j < 38) :
    ((o8Rep j : ↥autT) : Equiv.Perm (Fin 360)) = repPerm j := by
  rw [o8Rep, dite_eq_left hj]

theorem o8_yCensus (hw : O8PairFacts) :
    YCensus (omegaT.subgroupOf autT) (· ≤ omegaT.subgroupOf autT) := by
  refine yCensusII_of_sylowReps o8AutModel.normal (by rw [index_omegaT]; decide)
    CFSG.EvenSmallLie.OmegaEight.sylowA (k := 38) o8Rep ?_ ?_
  · intro u hu hu2 hu1
    rw [CFSG.EvenSmallLie.OmegaEight.coe_sylowA, mem_subgroupOf] at hu
    have ho : orderOf (u : Equiv.Perm (Fin 360)) = 2 :=
      orderOf_eq_prime (by rw [← coe_pow, hu2, coe_one]) (fun h1 => hu1 (Subtype.ext h1))
    obtain ⟨j, hj, c, hc, e⟩ := CFSG.EvenSmallLie.OmegaEight.exists_rep_of_involution hu ho
    refine ⟨j, hj, ⟨c, CFSG.EvenSmallLie.OmegaEight.sylowT_le_autT hc⟩, ?_, Subtype.ext ?_⟩
    · rw [CFSG.EvenSmallLie.OmegaEight.coe_sylowA, mem_subgroupOf]
      exact hc
    · rw [coe_mul, coe_mul, coe_inv, coe_o8Rep hj]
      exact e
  · intro j hj hjX b hb hb2 hbX hcomm
    rw [mem_subgroupOf, coe_o8Rep hj,
      CFSG.EvenSmallLie.OmegaEight.repPerm_mem_omegaT_iff hj] at hjX
    rw [CFSG.EvenSmallLie.OmegaEight.coe_sylowA, mem_subgroupOf] at hb
    rw [mem_subgroupOf] at hbX
    have hb2' : (b : Equiv.Perm (Fin 360)) ^ 2 = 1 := by rw [← coe_pow, hb2, coe_one]
    have hb1 : (b : Equiv.Perm (Fin 360)) ≠ 1 := fun h1 => hbX (h1 ▸ one_mem _)
    have hcomm' : (b : Equiv.Perm (Fin 360)) * repPerm j = repPerm j * b := by
      have := congrArg Subtype.val hcomm
      rwa [coe_mul, coe_mul, coe_o8Rep hj] at this
    have hM := hw j hj hjX _ hb hb2' hb1 hbX hcomm'
    have hXmap : (omegaT.subgroupOf autT).map autT.subtype = omegaT := by
      rw [subgroupOf_map_subtype, inf_eq_left.mpr CFSG.EvenSmallLie.OmegaEight.omegaT_le_autT]
    have hEmap : (closure ({o8Rep j, b} : Set ↥autT)).map autT.subtype =
        closure {repPerm j, (b : Equiv.Perm (Fin 360))} := by
      rw [MonoidHom.map_closure, Set.image_pair]
      simp only [coe_subtype, coe_o8Rep hj]
    rw [← monoW_map_iff autT.subtype autT.subtype_injective, hXmap, hEmap]
    exact hM

theorem hypII_of_pomegaPlus_four_two_of_facts
    (hw : O8PairFacts) {A : Type} [Group A] (hA : commutator A = ⊤)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (A ⧸ center A) .POmegaPlus 4 2 1) :
    AS76b.HypII A := by
  obtain ⟨e⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel h
    CFSG.EvenSmallLie.OmegaEight.statedClassicalModel_omegaT
  exact hypII_of_yCensus o8AutModel (o8_yCensus hw) hA e

end CFSG.ComponentClassification.RankTwoHypIICover.O8
