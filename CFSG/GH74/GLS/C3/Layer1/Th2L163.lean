module

public import CFSG.GH74.GLS.C3.Layer1.Th2P812A7
public import CFSG.GH74.GLS.C3.Layer1.Th2P85Bar
public import CFSG.GroupTheory.Fitting.GeneralizedFittingOvergroup
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup
public import CFSG.GH74.GLS.C3.Layer1.St1P41L42
public import CFSG.GH74.GLS.Stage1.Thm2.Recip.Gen
public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndB
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuot
public import CFSG.LocalAnalysis.ComponentClassification.Walter86.GLSPumpupFoote
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23Pf3Lift
public import CFSG.GroupTheory.SuzukiTwoGroupsBasic
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Simple59
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic12
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma33Cover
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der7
public import CFSG.ClassicalInvolution.Asc77.AscE187Cop
public import CFSG.ClassicalInvolution.Asc77.AscFusionR7
public import CFSG.ClassicalInvolution.Asc77.AscR10QVm
public import CFSG.ClassicalInvolution.Asc77.AscT3VMain
public import CFSG.ClassicalInvolution.Asc77.AscT3WCases
public import CFSG.ClassicalInvolution.Asc77.AscT7CExit25
public import CFSG.ClassicalInvolution.Asc77.AscT7CWz
public import CFSG.ClassicalInvolution.Asc77.AscT7D242
public import CFSG.ClassicalInvolution.Asc77.AscT7EC23
public import CFSG.ClassicalInvolution.Asc77.AscT7HC1
public import CFSG.ClassicalInvolution.Asc77.AscT7HX23
public import CFSG.ClassicalInvolution.Asc77.AscT7K3
public import CFSG.ClassicalInvolution.Asc77.AscT7K4
public import CFSG.ClassicalInvolution.AschTight.Hall196Q
public import CFSG.ClassicalInvolution.AschTight.S1916HalfB
public import CFSG.ClassicalInvolution.AschTight.S19CFus
public import CFSG.ClassicalInvolution.AschTight.S19CGood
public import CFSG.ClassicalInvolution.AschTight.S19CMod
public import CFSG.ClassicalInvolution.AschTight.S19CSec
public import CFSG.ClassicalInvolution.AschTight.S19CSwap
public import CFSG.ClassicalInvolution.AschTight.Sec7L98J
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterSp4Model
public import CFSG.ClassicalInvolution.Q3.OddCoreCentral
public import CFSG.ClassicalInvolution.Q3.Q3CLNine3
public import CFSG.ClassicalInvolution.Q3.Q3CPOmega
public import CFSG.ClassicalInvolution.Q3.Q3WMain
public import CFSG.ClassicalInvolution.Q3.Q3ZFraStd
public import CFSG.ClassicalInvolution.Q3.RankThreeBootstrap
public import CFSG.ClassicalInvolution.Q3.TL3DichMain
public import CFSG.ClassicalInvolution.Uniform.U3Datum
public import CFSG.ClassicalInvolution.Uniform.UExact
public import CFSG.ClassicalInvolution.Uniform.UThm2
public import CFSG.GH74.GLS.C3.Layer1.BkL113aSix
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Closed
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt6
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt69
public import CFSG.GH74.GLS.Stage2.Final.Named
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Inputs217
public import CFSG.LocalAnalysis.OddStandard.Solomon75Goldschmidt
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Frattini
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec3Lemma51
public import CFSG.RankThree.PartTwo.KFacts.K72OmegaL2

public section


namespace CFSG.GH74.GLS.Th2.L163

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm3.Sec4
  CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.Sol78.F514
  CFSG.ComponentClassification.Walter86
  CFSG.ComponentClassification.GSThmB.OddQuot
  CFSG.GH74.GLS.C3.Layer1.PumpL42
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem preuniq_conjugate {M L : Subgroup G} {m : G} (hm : m ∈ M)
    (hpre : ∀ t ∈ CMK M L, orderOf t = 2 → centralizer ({t} : Set G) ≤ M) :
    ∀ t ∈ CMK M (conjugate L m), orderOf t = 2 → centralizer ({t} : Set G) ≤ M := by
  intro t ht ht2
  have htM : t ∈ M := ht.1
  have hmM : m * t * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm htM) (M.inv_mem hm)
  have hmapM : cmap m M = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact M.mul_mem (M.mul_mem hm hy) (M.inv_mem hm)
    · intro hx
      exact ⟨m⁻¹ * x * m, M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm, by
        simp only [MulEquiv.coe_toMonoidHom, MonoidHom.comp_apply, MulAut.conj_apply]
        group⟩
  have hmapL : cmap m (conjugate L m) = L := by
    have hconj : conjugate L m = cmap m⁻¹ L := rfl
    rw [hconj, cmap_cmap, mul_inv_cancel]
    simpa using Subgroup.map_id L
  have hmapO : cmap m (pPrimeCoreOf 2 (conjugate L m)) = pPrimeCoreOf 2 L := by
    have hconj : conjugate L m = cmap m⁻¹ L := rfl
    rw [hconj, pPrimeCoreOf_cmap, cmap_cmap, mul_inv_cancel]
    simpa using Subgroup.map_id (pPrimeCoreOf 2 L)
  have hCMK : cmap m (CMK M (conjugate L m)) = CMK M L := by
    unfold CMK
    rw [cmap_inf, cmap_centralizerSection, hmapM, hmapL, hmapO]
  have htCMK : m * t * m⁻¹ ∈ CMK M L := by
    have hmem : m * t * m⁻¹ ∈ cmap m (CMK M (conjugate L m)) := by
      exact Subgroup.mem_map_of_mem ((MulAut.conj m).toMonoidHom) ht
    rwa [hCMK] at hmem
  have ht2' : orderOf (m * t * m⁻¹) = 2 := by
    have h := MulEquiv.orderOf_eq (MulAut.conj m) t
    simpa [MulAut.conj_apply] using h.trans ht2
  have hcent := hpre (m * t * m⁻¹) htCMK ht2'
  have hcentMap : (centralizer ({t} : Set G)).map (MulAut.conj m).toMonoidHom =
      centralizer ({m * t * m⁻¹} : Set G) :=
    CFSG.GH74.GLS.Stage1.Thm2.Recip.map_centralizer_singleton_conj t m
  intro x hx
  have hx' : m * x * m⁻¹ ∈ centralizer ({m * t * m⁻¹} : Set G) := by
    rw [← hcentMap]
    exact Subgroup.mem_map_of_mem _ hx
  have hxM : m * x * m⁻¹ ∈ M := hcent hx'
  have hxeq : x = m⁻¹ * (m * x * m⁻¹) * m := by group
  rw [hxeq]
  exact M.mul_mem (M.mul_mem (M.inv_mem hm) hxM) hm

theorem centralizer_le_of_nonnormal {M L : Subgroup G}
    (hL : IsPCompIn 2 M L)
    (hpre : ∀ t ∈ CMK M L, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hnotnormal : ¬ (L.subgroupOf M).Normal) :
    ∀ t : G, t ∈ L → orderOf t = 2 → centralizer ({t} : Set G) ≤ M := by
  have hnot : ¬ ∀ m : M,
      (L.subgroupOf M).map (MulAut.conj m).toMonoidHom = L.subgroupOf M := by
    intro h
    exact hnotnormal (Subgroup.normal_iff_map_conj_eq.mpr fun m => h m)
  push Not at hnot
  obtain ⟨m, hmne⟩ := hnot
  set mG : G := (m : G) with hmG
  have hmM : mG ∈ M := m.2
  have hLconj := CFSG.ComponentClassification.GSThmB.OddQuot.isPComponent_conjugate_subgroupOf (L := L) (X := M)
    (g := m) m.2 hL.1 hL.2
  have hLconjLe : conjugate L mG ≤ M := hLconj.1
  have hLconjComp : IsPComponent 2 ((conjugate L mG).subgroupOf M) := hLconj.2
  have hne : L ≠ conjugate L mG := by
    intro h
    have hleft : cmap mG L = L := by
      have h2 : conjugate L mG = cmap mG⁻¹ L := rfl
      have h3 : L = cmap mG⁻¹ L := h.trans h2
      calc cmap mG L = cmap mG (cmap mG⁻¹ L) := congrArg (cmap mG) h3
        _ = L := by
          rw [cmap_cmap]
          simpa using (show cmap (mG * mG⁻¹) L = L by rw [mul_inv_cancel, cmap_one])
    have hsub : (L.subgroupOf M).map (MulAut.conj m).toMonoidHom = L.subgroupOf M := by
      apply Subgroup.map_injective M.subtype_injective
      rw [CFSG.map_subgroupOf_map_conj_eq hL.1 m, Subgroup.map_subgroupOf_eq_of_le hL.1]
      exact hleft
    exact hmne hsub
  have hcore : L ≤ coreActionKernel (conjugate L mG) :=
    le_coreActionKernel_of_ne (N := M) (B := L) (M := conjugate L mG)
      hL.1 hLconjLe hL.2 hLconjComp hne
  intro t htL ht2
  have htCore : t ∈ coreActionKernel (conjugate L mG) := hcore htL
  rw [← centralizerSection_pPrimeCoreOf_eq_coreActionKernel] at htCore
  have htCMK : t ∈ CMK M (conjugate L mG) := ⟨hL.1 htL, htCore⟩
  exact preuniq_conjugate hmM hpre t htCMK ht2


theorem centralizerSection_le_of_nonnormal {M L : Subgroup G}
    (hL : IsPCompIn 2 M L)
    (hpre : ∀ t ∈ CMK M L, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hnotnormal : ¬ (L.subgroupOf M).Normal) :
    centralizerSection L (pPrimeCoreOf 2 L) ≤ M := by
  have hb := centralizer_le_of_nonnormal hL hpre hnotnormal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup G := pPrimeCoreOf 2 L with hO
  set S : Subgroup G := centralizerSection L O with hS
  have hO_le_L : O ≤ L := by rw [hO]; exact Subgroup.map_subtype_le _
  have hOsub_eq : O.subgroupOf L = pPrimeCore 2 ↥L := by
    rw [hO, pPrimeCoreOf]
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map]
  haveI : (O.subgroupOf L).Normal := by
    rw [hOsub_eq]
    infer_instance
  have hO_odd : Odd (Nat.card ↥O) := by
    rw [hO]
    exact CFSG.GH74.GLS.Stage2.Bender.Thm1.odd_card_pPrimeCoreOf L
  have hOsub_odd : Odd (Nat.card ↥(O.subgroupOf L)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hO_le_L).toEquiv]
    exact hO_odd
  have h2L : 2 ∣ Nat.card L :=
    CFSG.ComponentClassification.GrSLit.GrS5.two_dvd_card_of_isPComponent hL.1 hL.2
  let P : Sylow 2 ↥L := Classical.choice (inferInstance : Nonempty (Sylow 2 ↥L))
  have hPne : (P : Subgroup ↥L) ≠ ⊥ := Sylow.ne_bot_of_dvd_card P h2L
  let Pamb : Subgroup G := (P : Subgroup ↥L).map L.subtype
  have hPamb2 : IsPGroup 2 Pamb := (P.isPGroup').map L.subtype
  have hPamb_le : Pamb ≤ L := Subgroup.map_subtype_le _
  have hO_le_S : O ≤ S := by
    rw [hS]
    intro o ho
    refine ⟨?_, ?_, ?_⟩
    · exact (hO_le_L.trans Subgroup.le_normalizer) ho
    · exact Subgroup.le_normalizer ho
    · intro k hk
      have hnorm : k ∈ Subgroup.normalizer (O : Set G) := by
        rw [hO]
        exact CFSG.GH74.GLS.Stage2.Bender.Thm1.le_normalizer_pPrimeCoreOf L hk
      have hconj : k * o * k⁻¹ ∈ O :=
        (Subgroup.mem_normalizer_iff.mp hnorm o).mp ho
      simpa [commutatorElement_def, mul_assoc] using O.mul_mem hconj (O.inv_mem ho)
  have hPO_bot : Pamb ⊓ O = ⊥ := by
    have hsub : IsPGroup 2 ↥(Pamb ⊓ O) :=
      hPamb2.of_injective (Subgroup.inclusion inf_le_left)
        (Subgroup.inclusion_injective inf_le_left)
    have hpow : ∃ n, Nat.card ↥(Pamb ⊓ O) = 2 ^ n :=
      IsPGroup.iff_card.mp hsub
    obtain ⟨n, hn⟩ := hpow
    have hcardO : Nat.card ↥(Pamb ⊓ O) ∣ Nat.card ↥O :=
      Subgroup.card_dvd_of_le inf_le_right
    have hodd : Odd (Nat.card ↥(Pamb ⊓ O)) := Odd.of_dvd_nat hO_odd hcardO
    have hn0 : n = 0 := by
      by_contra hne
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (Nat.pos_of_ne_zero hne).ne'
      rw [hn] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
    rw [Subgroup.eq_bot_iff_card, hn, hn0, pow_zero]
  haveI : Nontrivial ↥(P : Subgroup ↥L) := (Subgroup.nontrivial_iff_ne_bot _).2 hPne
  obtain ⟨zP, hzP2⟩ :=
    CFSG.GroupTheory.SuzukiTwoGroup.exists_orderOf_eq_two (S := ↥(P : Subgroup ↥L)) P.isPGroup'
  let z : G := (((zP : ↥L) : G))
  have hzPamb : z ∈ Pamb := by
    refine Subgroup.mem_map_of_mem L.subtype ?_
    exact zP.2
  have hzL : z ∈ L := hPamb_le hzPamb
  have hz2 : orderOf z = 2 := by
    simpa [z] using hzP2
  have hCz := hb z hzL hz2
  intro s hs
  have hsN : s ∈ Subgroup.normalizer (L : Set G) := hs.1
  have hNnorm : ∀ n ∈ Subgroup.normalizer (L : Set G), ∀ m ∈ L, n * m * n⁻¹ ∈ L :=
    fun n hn m hm => (Subgroup.mem_normalizer_iff.mp hn m).mp hm
  let φ : MulAut ↥L :=
    CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.conjMulAut hNnorm s hsN
  let B : Subgroup ↥L := (P : Subgroup ↥L).map φ.toMonoidHom
  have hB2 : IsPGroup 2 B := (P.isPGroup').map φ.toMonoidHom
  have hmap : (P : Subgroup ↥L).map (QuotientGroup.mk' (O.subgroupOf L)) =
      B.map (QuotientGroup.mk' (O.subgroupOf L)) := by
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      have hcomm : s * (p : G) * s⁻¹ * (p : G)⁻¹ ∈ O := by
        have h := hs.2.2 (p : G) p.2
        have hinv : (⁅(p : G), s⁆)⁻¹ ∈ O := O.inv_mem h
        simpa [commutatorElement_def, mul_assoc] using hinv
      have hdiv : (φ p) / p ∈ O.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        have hval : ((φ p / p : ↥L) : G) = s * (p : G) * s⁻¹ * (p : G)⁻¹ := by
          rw [Subgroup.coe_div, CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.conjMulAut_apply,
            div_eq_mul_inv]
        rw [hval]
        exact hcomm
      have heq : (QuotientGroup.mk' (O.subgroupOf L)) (φ p) =
          (QuotientGroup.mk' (O.subgroupOf L)) p :=
        (QuotientGroup.eq_iff_div_mem).2 hdiv
      exact ⟨φ p, ⟨p, hp, rfl⟩, heq⟩
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨b, hb, rfl⟩
      rcases Subgroup.mem_map.mp hb with ⟨p, hp, rfl⟩
      have hcomm : s * (p : G) * s⁻¹ * (p : G)⁻¹ ∈ O := by
        have h := hs.2.2 (p : G) p.2
        have hinv : (⁅(p : G), s⁆)⁻¹ ∈ O := O.inv_mem h
        simpa [commutatorElement_def, mul_assoc] using hinv
      have hdiv : (φ p) / p ∈ O.subgroupOf L := by
        rw [Subgroup.mem_subgroupOf]
        have hval : ((φ p / p : ↥L) : G) = s * (p : G) * s⁻¹ * (p : G)⁻¹ := by
          rw [Subgroup.coe_div, CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.conjMulAut_apply,
            div_eq_mul_inv]
        rw [hval]
        exact hcomm
      have heq : (QuotientGroup.mk' (O.subgroupOf L)) (φ p) =
          (QuotientGroup.mk' (O.subgroupOf L)) p :=
        (QuotientGroup.eq_iff_div_mem).2 hdiv
      exact ⟨p, hp, heq.symm⟩
  obtain ⟨o, ho, hconj⟩ :=
    CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.exists_odd_conj
      (N := O.subgroupOf L) hOsub_odd (P.isPGroup') hB2 hmap
  have hoO : (o : G) ∈ O := Subgroup.mem_subgroupOf.mp ho
  let a : G := s⁻¹ * (o : G)
  have haS : a ∈ S := S.mul_mem (S.inv_mem hs) (hO_le_S hoO)
  have haN : a ∈ Subgroup.normalizer (Pamb : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨p, hp, rfl⟩
      rcases Subgroup.mem_map.mp hp with ⟨pL, hpL, rfl⟩
      have hmemB : (MulAut.conj (o : ↥L)) pL ∈ B := by
        rw [← hconj]
        exact Subgroup.mem_map_of_mem (MulAut.conj (o : ↥L)).toMonoidHom hpL
      rcases Subgroup.mem_map.mp hmemB with ⟨q, hq, hqeq⟩
      have hqeq' : ((φ q : ↥L) : G) = (o : G) * (pL : G) * (o : G)⁻¹ := by
        simpa [MulAut.conj_apply] using congrArg (fun z : ↥L => (z : G)) hqeq
      have hφq : ((φ q : ↥L) : G) = s * (q : G) * s⁻¹ := by
        simpa using
          CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.conjMulAut_apply hNnorm s hsN q
      have haq : a * (pL : G) * a⁻¹ = (q : G) := by
        calc a * (pL : G) * a⁻¹ = s⁻¹ * ((o : G) * (pL : G) * (o : G)⁻¹) * s := by
              dsimp [a]; group
          _ = s⁻¹ * (s * (q : G) * s⁻¹) * s := by rw [← hqeq', hφq]
          _ = (q : G) := by group
      change a * (pL : G) * a⁻¹ ∈ Pamb
      rw [haq]
      exact Subgroup.mem_map_of_mem L.subtype hq
    · intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨pL, hpL, rfl⟩
      have hsB : φ pL ∈ B :=
        Subgroup.mem_map_of_mem φ.toMonoidHom hpL
      rw [← hconj] at hsB
      rcases Subgroup.mem_map.mp hsB with ⟨r, hr, hreq⟩
      have hreq' : ((r : ↥L) : G) = (o : G)⁻¹ * (s * (pL : G) * s⁻¹) * (o : G) := by
        have h : (o : G) * (r : G) * (o : G)⁻¹ = s * (pL : G) * s⁻¹ := by
          have hφp : ((φ pL : ↥L) : G) = s * (pL : G) * s⁻¹ := by
            simpa using
              CFSG.GH74.GLS.Stage1.Thm3.Sec8.Basic.conjMulAut_apply hNnorm s hsN pL
          simpa [MulAut.conj_apply] using
            (congrArg (fun z : ↥L => (z : G)) hreq).trans hφp
        calc ((r : ↥L) : G) = (o : G)⁻¹ * ((o : G) * (r : G) * (o : G)⁻¹) * (o : G) := by
              group
          _ = (o : G)⁻¹ * (s * (pL : G) * s⁻¹) * (o : G) := by rw [h]
      have haeq : a * (r : G) * a⁻¹ = (pL : G) := by
        rw [hreq']
        dsimp [a]
        group
      have hmem : (MulAut.conj a) (L.subtype r) ∈ Pamb.map (MulAut.conj a).toMonoidHom :=
        Subgroup.mem_map_of_mem (MulAut.conj a).toMonoidHom
          (Subgroup.mem_map_of_mem L.subtype hr)
      rw [show L.subtype pL = (MulAut.conj a) (L.subtype r) by
        rw [MulAut.conj_apply]
        exact haeq.symm]
      exact hmem
  have hacent : ∀ p ∈ Pamb, a * p = p * a := by
    intro p hp
    have hcommO : ⁅p, a⁆ ∈ O := haS.2.2 p (hPamb_le hp)
    have hconjP : a * p⁻¹ * a⁻¹ ∈ Pamb :=
      (Subgroup.mem_normalizer_iff.mp haN p⁻¹).mp (Pamb.inv_mem hp)
    have hcommP : ⁅p, a⁆ ∈ Pamb := by
      simpa [commutatorElement_def, mul_assoc] using Pamb.mul_mem hp hconjP
    have hbot : ⁅p, a⁆ ∈ (⊥ : Subgroup G) := by
      rw [← hPO_bot]
      exact ⟨hcommP, hcommO⟩
    have hone : ⁅p, a⁆ = 1 := by simpa using hbot
    exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm
  have haz : a ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hacent z hzPamb
  have haM : a ∈ M := hCz haz
  have hoM : (o : G) ∈ M := hL.1 (hO_le_L hoO)
  have hsa : s * a = (o : G) := by dsimp [a]; group
  have hs_eq : s = (o : G) * a⁻¹ := by
    calc s = s * a * a⁻¹ := by group
      _ = (o : G) * a⁻¹ := by rw [hsa]
  rw [hs_eq]
  exact M.mul_mem hoM (M.inv_mem haM)

theorem pPrimeCoreOf_le_centralizerSection {M L : Subgroup G}
    (hL : IsPCompIn 2 M L) :
    pPrimeCoreOf 2 M ≤ centralizerSection L (pPrimeCoreOf 2 L) := by
  intro o ho
  have hoM : o ∈ M := Subgroup.map_subtype_le _ ho
  refine CFSG.OddStandard.Solomon75.normalizes_isPCompIn_of_comm_mem hL ?_ ?_
  · exact Subgroup.le_normalizer hoM
  · intro l hl
    have hlM : l ∈ M := hL.1 hl
    have hnorm : l ∈ Subgroup.normalizer (pPrimeCoreOf 2 M : Set G) :=
      CFSG.GH74.GLS.Stage2.Bender.Thm1.le_normalizer_pPrimeCoreOf M hlM
    have hconj : l * o * l⁻¹ ∈ pPrimeCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp hnorm o).mp ho
    have hcomm : l * o * l⁻¹ * o⁻¹ ∈ pPrimeCoreOf 2 M :=
      (pPrimeCoreOf 2 M).mul_mem hconj ((pPrimeCoreOf 2 M).inv_mem ho)
    simpa [commutatorElement_def, mul_assoc] using hcomm

theorem imgM_centralizerSection {M L : Subgroup G} (hL : IsPCompIn 2 M L)
    (hSleM : centralizerSection L (pPrimeCoreOf 2 L) ≤ M) :
    CFSG.GH74.GLS.Th2.P85.imgM M (centralizerSection L (pPrimeCoreOf 2 L)) =
      Subgroup.centralizer (CFSG.GH74.GLS.Th2.P85.imgM M L : Set (CFSG.GH74.GLS.Th2.P85.Mb M)) := by
  let S : Subgroup G := centralizerSection L (pPrimeCoreOf 2 L)
  have hLeq : L = pPrimeCoreOf 2 L ⊔ L :=
    (sup_eq_right.mpr (Subgroup.map_subtype_le _)).symm
  have hsub : CFSG.GH74.GLS.IsSubnormalIn L M := by
    obtain ⟨K, -, hsub, -⟩ := hL.2
    exact ⟨hL.1, hsub⟩
  have hcmbar : CFSG.GH74.GLS.CMbar M L = S := by
    rw [CFSG.GH74.GLS.Th2.P812A7.cmbar_eq_cmk_of_isPCompIn hL hsub hLeq]
    exact inf_eq_right.mpr hSleM
  change CFSG.GH74.GLS.Th2.P85.imgM M S =
    Subgroup.centralizer (CFSG.GH74.GLS.Th2.P85.imgM M L :
      Set (CFSG.GH74.GLS.Th2.P85.Mb M))
  rw [← hcmbar]
  exact CFSG.GH74.GLS.Th2.P85.imgM_cmbar_eq hL.1

theorem imgM_sup_centralizerSection {M L : Subgroup G} (hL : IsPCompIn 2 M L)
    (hSleM : centralizerSection L (pPrimeCoreOf 2 L) ≤ M) :
    CFSG.GH74.GLS.Th2.P85.imgM M (L ⊔ centralizerSection L (pPrimeCoreOf 2 L)) =
      CFSG.GH74.GLS.Th2.P85.imgM M L ⊔
        Subgroup.centralizer (CFSG.GH74.GLS.Th2.P85.imgM M L :
          Set (CFSG.GH74.GLS.Th2.P85.Mb M)) := by
  rw [CFSG.GH74.GLS.Th2.P85.imgM, Subgroup.subgroupOf_sup hL.1 hSleM,
    Subgroup.map_sup]
  change map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) (L.subgroupOf M) ⊔
      map (QuotientGroup.mk' (pPrimeCore 2 ↥M))
        ((centralizerSection L (pPrimeCoreOf 2 L)).subgroupOf M) =
    CFSG.GH74.GLS.Th2.P85.imgM M L ⊔
      Subgroup.centralizer (CFSG.GH74.GLS.Th2.P85.imgM M L :
        Set (CFSG.GH74.GLS.Th2.P85.Mb M))
  have hSimg : map (QuotientGroup.mk' (pPrimeCore 2 ↥M))
      ((centralizerSection L (pPrimeCoreOf 2 L)).subgroupOf M) =
      CFSG.GH74.GLS.Th2.P85.imgM M (centralizerSection L (pPrimeCoreOf 2 L)) := rfl
  rw [hSimg, imgM_centralizerSection hL hSleM]
  rfl

theorem generalizedFitting_le_imgM_sup_centralizerSection {M L : Subgroup G}
    (hL : IsPCompIn 2 M L)
    (hSleM : centralizerSection L (pPrimeCoreOf 2 L) ≤ M) :
    generalizedFitting (CFSG.GH74.GLS.Th2.P85.Mb M) ≤
      CFSG.GH74.GLS.Th2.P85.imgM M (L ⊔ centralizerSection L (pPrimeCoreOf 2 L)) := by
  let Lbar : Subgroup (CFSG.GH74.GLS.Th2.P85.Mb M) := CFSG.GH74.GLS.Th2.P85.imgM M L
  have hLbarComp : IsComponent Lbar := by
    obtain ⟨K, hK, -, hmap, -⟩ := hL.2
    have hEq : Lbar = K := by
      dsimp [Lbar, CFSG.GH74.GLS.Th2.P85.imgM]
      exact hmap
    rw [hEq]
    exact hK
  have hImgH := imgM_sup_centralizerSection hL hSleM
  rw [hImgH, generalizedFitting.eq_sup]
  apply sup_le
  ·
    have hfit : fittingSubgroup (CFSG.GH74.GLS.Th2.P85.Mb M) ≤
        Subgroup.centralizer (layer (CFSG.GH74.GLS.Th2.P85.Mb M) :
          Set (CFSG.GH74.GLS.Th2.P85.Mb M)) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (CFSG.LocalCores.fitting_layer_commute (G := CFSG.GH74.GLS.Th2.P85.Mb M))
    have hcent : Subgroup.centralizer (layer (CFSG.GH74.GLS.Th2.P85.Mb M) :
          Set (CFSG.GH74.GLS.Th2.P85.Mb M)) ≤
        Subgroup.centralizer (Lbar : Set (CFSG.GH74.GLS.Th2.P85.Mb M)) :=
      Subgroup.centralizer_le (by intro x hx; exact CFSG.LocalCores.component_le_layer hLbarComp hx)
    exact hfit.trans (hcent.trans le_sup_right)
  ·
    rw [layer.eq_sSup]
    refine sSup_le ?_
    intro K hK
    rcases CFSG.LocalCores.distinct_components_commute hK hLbarComp with rfl | hcomm
    · exact le_sup_left
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans le_sup_right

theorem map_subgroupOf_pLayer_sup_pPrimeCore {M H : Subgroup G} (hHleM : H ≤ M) :
    ((((pLayer ↥(H.subgroupOf M) 2 ⊔ pPrimeCore 2 ↥(H.subgroupOf M)).map
        (H.subgroupOf M).subtype)).map M.subtype) =
      (pLayer ↥H 2 ⊔ pPrimeCore 2 ↥H).map H.subtype := by
  let e : ↥(H.subgroupOf M) ≃* ↥H := Subgroup.subgroupOfEquivOfLe hHleM
  have hcomp : H.subtype.comp e.toMonoidHom = M.subtype.comp (H.subgroupOf M).subtype := by
    ext x
    rfl
  rw [Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_map, Subgroup.map_map, ← hcomp,
    ← Subgroup.map_map, ← Subgroup.map_map, Subgroup.map_sup]
  rw [CFSG.ComponentClassification.UnbalancedGS.FixedLayerPComponent.map_pLayer_mulEquiv 2 e,
    pPrimeCore_map_iso 2 e]

theorem normalizer_le_of_normal [IsSimpleGroup G] {M L : Subgroup G}
    (hM : IsCoatom M) (hL : IsPCompIn 2 M L)
    (hnormal : (L.subgroupOf M).Normal) :
    normalizer (L : Set G) ≤ M := by
  have hL0 : L ≠ ⊥ := by
    rintro rfl
    exact (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_ne_bot hL.2) (by simp)
  have hLn : ∀ m ∈ M, ∀ l ∈ L, m * l * m⁻¹ ∈ L := by
    intro m hm l hl
    exact Subgroup.mem_subgroupOf.mp
      (hnormal.conj_mem ⟨l, hL.1 hl⟩ (Subgroup.mem_subgroupOf.mpr hl) ⟨m, hm⟩)
  have hN : normalizer (L : Set G) = M :=
    CFSG.GH74.GLS.C3.Layer1.Bk.normalizer_eq_of_coatom inferInstance hM hL.1 hLn hL0
  exact le_of_eq hN

theorem normalizer_le_of_nonnormal [IsSimpleGroup G] {M L : Subgroup G}
    (hM : IsCoatom M) (hL : IsPCompIn 2 M L)
    (hpre : ∀ t ∈ CMK M L, orderOf t = 2 → centralizer ({t} : Set G) ≤ M)
    (hnotnormal : ¬ (L.subgroupOf M).Normal) :
    normalizer (L : Set G) ≤ M := by
  set S : Subgroup G := centralizerSection L (pPrimeCoreOf 2 L) with hS
  set H : Subgroup G := L ⊔ S with hHdef
  have hSleM : S ≤ M := centralizerSection_le_of_nonnormal hL hpre hnotnormal
  have hHleM : H ≤ M := by rw [hHdef]; exact sup_le hL.1 hSleM
  have hOMH : pPrimeCoreOf 2 M ≤ H := by
    rw [hHdef]
    exact (pPrimeCoreOf_le_centralizerSection hL).trans le_sup_right
  have hH0 : pPrimeCore 2 ↥M ≤ H.subgroupOf M := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hOMH (Subgroup.mem_map_of_mem M.subtype hx))
  have hFbar : generalizedFitting (CFSG.GH74.GLS.Th2.P85.Mb M) ≤
      (H.subgroupOf M).map (QuotientGroup.mk' (pPrimeCore 2 ↥M)) := by
    simpa [CFSG.GH74.GLS.Th2.P85.imgM] using
      generalizedFitting_le_imgM_sup_centralizerSection hL hSleM
  have hTrans := CFSG.map_pLayer_two_sup_pPrimeCore_two_eq_of_quotient
    (X := ↥M) (H := H.subgroupOf M) hH0 hFbar
  have hYtransport : ((pLayer ↥M 2 ⊔ pPrimeCore 2 ↥M).map M.subtype) =
      ((pLayer ↥H 2 ⊔ pPrimeCore 2 ↥H).map H.subtype) := by
    have hmap := congrArg (Subgroup.map M.subtype) hTrans
    rw [map_subgroupOf_pLayer_sup_pPrimeCore hHleM] at hmap
    exact hmap.symm
  set Y : Subgroup G := (pLayer ↥M 2 ⊔ pPrimeCore 2 ↥M).map M.subtype with hY
  have hL0 : L ≠ ⊥ := by
    rintro rfl
    exact (CFSG.ComponentClassification.CatalogueBPrimeJoin.pComponent_ne_bot hL.2) (by simp)
  have hL_le_pLayer : L.subgroupOf M ≤ pLayer ↥M 2 := le_sSup hL.2
  have hL_le_Y : L ≤ Y := by
    rw [hY]
    calc L = (L.subgroupOf M).map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hL.1).symm
      _ ≤ (pLayer ↥M 2).map M.subtype := Subgroup.map_mono hL_le_pLayer
      _ ≤ (pLayer ↥M 2 ⊔ pPrimeCore 2 ↥M).map M.subtype :=
          Subgroup.map_mono le_sup_left
  have hYne : Y ≠ ⊥ := by
    intro hbot
    have hLbot : L ≤ (⊥ : Subgroup G) := hbot ▸ hL_le_Y
    exact hL0 (le_bot_iff.mp hLbot)
  have hYleM : Y ≤ M := by
    rw [hY]
    exact Subgroup.map_subtype_le _
  haveI : (pLayer ↥M 2 ⊔ pPrimeCore 2 ↥M).Normal := inferInstance
  have hM_Y : M ≤ normalizer (Y : Set G) := by
    rw [hY]
    exact CFSG.ABGLocalTools.le_normalizer_map_subtype M
      (pLayer ↥M 2 ⊔ pPrimeCore 2 ↥M)
  have hYn : ∀ m ∈ M, ∀ y ∈ Y, m * y * m⁻¹ ∈ Y := by
    intro m hm y hy
    exact (Subgroup.mem_normalizer_iff.mp (hM_Y hm) y).mp hy
  have hNY : normalizer (Y : Set G) = M :=
    CFSG.GH74.GLS.C3.Layer1.Bk.normalizer_eq_of_coatom inferInstance hM hYleM hYn hYne
  haveI : (pLayer ↥H 2).Characteristic :=
    CFSG.ComponentClassification.CatalogueBPrimeJoin.pLayer_characteristic
  have hNH_layer : normalizer (H : Set G) ≤
      normalizer ((pLayer ↥H 2).map H.subtype : Set G) :=
    CFSG.Walter.normalizer_le_normalizer_map_of_characteristic (pLayer ↥H 2)
  have hNH_core : normalizer (H : Set G) ≤ normalizer (pPrimeCoreOf 2 H : Set G) :=
    CFSG.Walter.normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 ↥H)
  have hNH_Y : normalizer (H : Set G) ≤ normalizer (Y : Set G) := by
    have h := (le_inf hNH_layer hNH_core).trans
      (Subgroup.inf_normalizer_le_normalizer_sup
        ((pLayer ↥H 2).map H.subtype) ((pPrimeCore 2 ↥H).map H.subtype))
    rw [← Subgroup.map_sup] at h
    rwa [← hYtransport, hHdef] at h
  have hLH : L ≤ H := by rw [hHdef]; exact le_sup_left
  have hSH : S ≤ H := by rw [hHdef]; exact le_sup_right
  have hHnorm : H ≤ normalizer (L : Set G) := by
    rw [hHdef]
    exact sup_le Subgroup.le_normalizer (fun s hs => hs.1)
  have hNLH : normalizer (L : Set G) ≤ normalizer (H : Set G) := by
    intro n hn
    have hnL : n ∈ normalizer (L : Set G) := hn
    have hnO : n ∈ normalizer (pPrimeCoreOf 2 L : Set G) :=
      CFSG.Walter.normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 ↥L) hn
    have hcmapL : cmap n L = L := Subgroup.mem_normalizer_iff_map_conj_eq.mp hnL
    have hcmapO : cmap n (pPrimeCoreOf 2 L) = pPrimeCoreOf 2 L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnO
    have hcmapS : cmap n S = S := by
      rw [hS, cmap_centralizerSection, hcmapL, hcmapO]
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [hHdef]
    change (L ⊔ S).map (MulAut.conj n).toMonoidHom = L ⊔ S
    rw [Subgroup.map_sup]
    simpa only [cmap] using congrArg₂ (· ⊔ ·) hcmapL hcmapS
  exact hNLH.trans (hNH_Y.trans (le_of_eq hNY))

theorem normalizer_le [IsSimpleGroup G] {M L : Subgroup G} (hM : IsCoatom M)
    (hL : IsPCompIn 2 M L)
    (hpre : ∀ t ∈ CMK M L, orderOf t = 2 → centralizer ({t} : Set G) ≤ M) :
    normalizer (L : Set G) ≤ M := by
  by_cases hnormal : (L.subgroupOf M).Normal
  · exact normalizer_le_of_normal hM hL hnormal
  · exact normalizer_le_of_nonnormal hM hL hpre hnormal

end CFSG.GH74.GLS.Th2.L163
