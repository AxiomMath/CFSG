module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265Fam
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCore
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ATri
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ATriTwo
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ATriBar
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ATriLift
import CFSG.LocalAnalysis.GLTheoremA.CatA.S265ATwE6Inv
import CFSG.LocalAnalysis.GLTheoremA.CatB.TriD4Main
import CFSG.LocalAnalysis.GLTheoremA.CatA.I264bO8

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S265

variable {Ω : Type} [Group Ω] [Finite Ω] {S B T : Subgroup Ω} {x : Ω} {D K : Subgroup Ω}

section Center


private theorem center_pQuot_eq_bot_of_d4two {X J : Subgroup Ω} (hJ : GLAPComponent 3 X J)
    (hT : catalogIs (PSimple 3 J) S9.isD4two) : Subgroup.center (PQuot 3 J) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := D4XF.statedModel_of_d4two hT
  haveI := CFSG.SeitzReduction.SeitzQ2.charTwo_of_natCard_eq_two_pow hF
  have hS := (CFSG.SeitzReduction.SeitzQ2.oddSchurTrivial_statedProj_omegaPlus (by norm_num)
    F).of_mulEquiv e.symm
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ
  have hodd : Odd (Nat.card ↥(QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (I2611.isPGroup_center_pQuot' Nat.prime_three J).exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hinj := hS (PQuot 3 J) ⟨hq.1⟩ (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    (QuotientGroup.ker_mk' _).le hodd
  rw [← QuotientGroup.ker_mk' (Subgroup.center (PQuot 3 J))]
  exact (MonoidHom.ker_eq_bot_iff _).2 hinj

end Center

section Main


theorem QSNL.false_of_d4two_outer (h : QSNL 3 S B T x D K)
    (hJ : catalogIs (PSimple 3 K) S9.isD4two)
    (hout : ¬ ∀ e ∈ B, ∀ he : e ∈ Subgroup.normalizer (K : Set Ω),
      chevAut 3 K ⟨e, he⟩ ∈ D4T.innerAut (PSimple 3 K)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : Nat.Prime 3 := Nat.prime_three
  have hout' : ∃ e ∈ B, ∃ he : e ∈ Subgroup.normalizer (K : Set Ω),
      chevAut 3 K ⟨e, he⟩ ∉ D4T.innerAut (PSimple 3 K) := by
    push Not at hout
    exact hout
  have hSN : ∀ g : Ω, g ∈ Subgroup.normalizer (S : Set Ω) := fun g =>
    (Subgroup.normalizer_eq_top_iff.2 h.cfg.normal) ▸ Subgroup.mem_top g
  obtain ⟨hDB, -, hD9, -, hKL, -, hDK⟩ := h.cfg.std
  have hpK : 3 ∣ Nat.card K :=
    (show 3 ∣ Nat.card (PSimple 3 K) by rw [card_o8p2 hJ]; norm_num).trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_quotient_dvd_card _))
  have hN := h.nlAct hpK
  have hKS : K ≤ S := hN.comp.1.trans inf_le_left
  have hDJ : D ≤ Subgroup.centralizer (K : Set Ω) := fun d hd => (hDK.le hd).2
  have hCD : Subgroup.centralizer (D : Set Ω) ≤ Subgroup.normalizer (K : Set Ω) := fun c hc => by
    rw [hKL]
    exact S12.mem_normalizer_glaLayer'
      (S12.mem_normalizer_inf' (hSN c) (Subgroup.le_normalizer hc))
  have hZ := center_pQuot_eq_bot_of_d4two hN.comp hJ
  have hF := D4XF.d4TwoFacts_of_residual D4YB.d4TwoAutNormInn_holds hJ
  obtain ⟨hB27, hTB, -⟩ := tri_residual hN h.cfg.elem hDJ hCD hZ hF hout' h.cfg.two h.cfg.bnorm
    (h.cfg.maxc.imp id fun hm => hm.1) h.cfg.rank
  obtain ⟨hSs, hnc, d, α, β, J, hd, hSd, hα, hα3, hα1, hβ, hβ3, hαβ, hJα, hTJ, hβJ, hni⟩ :=
    QSNL.triD4_data h hJ hout'
  have hE := TriD4.eq_twistedE6_of_triD4 hSs hnc d hd hSd hα hα3 hα1 hβ hβ3 hαβ hJα hTJ hβJ hni
  have hX4 : 3 ^ 4 ≤
      Nat.card ((B.subgroupOf (Subgroup.normalizer (S : Set Ω))).map (chevAut 3 S)) := by
    have hker : (chevAut 3 S).ker ⊓ B.subgroupOf (Subgroup.normalizer (S : Set Ω)) =
        (Subgroup.zpowers x).subgroupOf (Subgroup.normalizer (S : Set Ω)) := by
      ext ⟨b, hb⟩
      simp only [Subgroup.mem_inf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      refine ⟨fun ⟨h1, hbB⟩ =>
        (h.cfg.centB b hbB).1 ((chevAut_eq_one_iff hp h.cfg.comp hb).1 h1), fun hbx => ?_⟩
      have hbB : b ∈ B := Subgroup.zpowers_le.2 h.cfg.xB hbx
      exact ⟨(chevAut_eq_one_iff hp h.cfg.comp hb).2 ((h.cfg.centB b hbB).2 hbx), hbB⟩
    have h1 := Subgroup.relIndex_mul_card (H := (chevAut 3 S).ker)
      (K := B.subgroupOf (Subgroup.normalizer (S : Set Ω)))
    rw [Subgroup.relIndex_ker, hker,
      D4T.card_subgroupOf_of_le (N := Subgroup.normalizer (S : Set Ω))
        (Y := Subgroup.zpowers x) (fun g _ => hSN g),
      D4T.card_subgroupOf_of_le (N := Subgroup.normalizer (S : Set Ω)) (Y := B)
        (fun g _ => hSN g),
      Nat.card_zpowers, orderOf_eq_prime (h.cfg.elem.2 x h.cfg.xB) h.cfg.x1, hB27, hD9] at h1
    norm_num at h1 ⊢
    omega
  have hU : ∃ u ∈ (⁅T, B⁆ : Subgroup Ω), ∃ hu : u ∈ Subgroup.normalizer (S : Set Ω),
      chevAut 3 S ⟨u, hu⟩ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, hW2, hBW, -⟩ := S9.l94t_commutator_facts h.cfg.elem h.cfg.two h.cfg.bnorm
    have hO : GLAPPrimeCoreOf 3 S = ⊥ := by
      show (GLAPPrimeCore 3 ↥S).map S.subtype = ⊥
      rw [h.cfg.core, Subgroup.map_bot]
    refine hTB (tri_noTwo_comp hN h.cfg.elem hDJ hZ hF hout' h.cfg.rank hW2 hBW fun u hu => ?_)
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hc := (centMod_iff.1 ((chevAut_eq_one_iff hp h.cfg.comp (hSN u)).1
      (hcon u hu (hSN u)))).2 k (hKS hk)
    rw [hO, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.1 hc
  obtain ⟨v, hv2, hv1, hvB⟩ := exists_fixed_involution_of_twE6 h.cfg.normal h.cfg.inn
    h.cfg.elem d hE hSd hX4 h.cfg.two h.cfg.bnorm hU
  obtain ⟨z, -, hz2, hz1, hzB⟩ := lift_fixed_involution h.cfg.core (fun b _ => hSN b) hv2 hv1 hvB
  have hzC : Subgroup.zpowers z ≤ Subgroup.centralizer (B : Set Ω) :=
    Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 hzB)
  have hW : IsPGroup 2 (Subgroup.zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hz2) hz1, pow_one])
  exact hz1 (Subgroup.zpowers_eq_bot.1 (tri_noTwo_cent hN h.cfg.elem hDJ hCD hZ hF hout'
    h.cfg.rank hW ((Subgroup.le_centralizer_iff.1 hzC).trans (Subgroup.centralizer_le_normalizer _))
    (hzC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDB)))))

end Main

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
