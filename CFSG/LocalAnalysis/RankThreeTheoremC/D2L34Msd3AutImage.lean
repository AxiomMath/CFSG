module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3Layer
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2L34Msd3TwoLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerAutImageProved
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.LayerTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.I542Three

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbeddingD2
open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2.Tits
open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

theorem d2L34BetaLayerAutImage3_of_I542Three (hI : AGL81I542Three)
    (hN : D2L34BetaNormalizerSolvable3 G) (hD1 : D1NoXBlock3 G) : D2L34BetaLayerAutImage3 G := by
  intro d P M A H R Rbar K ctx hstr hKmax hcon L hlay
  classical
  have := ctx.amb
  have hc := ctx.conf
  have hNX : NoXBlockFor G := noXBlockFor_of_setting hD1 ctx.setting
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf M
  have hTM : T ≤ M := hT.1
  have := (D2Amb3.glob (G := G)).simple
  have hMtop : M ≠ ⊤ := twoLocal_ne_top (D2Amb3.glob (G := G)).nonab hc.esc.maxTwoLocal_M.1
  have hGN : GNSetting ↥M (T.subgroupOf M) :=
    gnSetting_of_core (D2Amb3.glob (G := G)).kProper hMtop
      ((D2Amb3.glob (G := G)).charTwo M hc.esc.maxTwoLocal_M.1) hT
      (fun Y hYM hYs hYX => hNX M Y hc.esc.maxTwoLocal_M hYM hYs hYX)
  have hT1 : T ≠ ⊥ := by
    intro h
    apply CFSG.PreuniquenessRankFour.Helpers.twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hNZ := hN d P M A H R Rbar K ctx hstr hKmax T hT (omegaOneCenterOf T)
    (Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1) (Setup.omegaOneCenterOf_le T)
    (Setup.characteristic_omegaOneCenterOf T)
  have hNJ := hN d P M A H R Rbar K ctx hstr hKmax T hT (thompsonJ T)
    (Setup.thompsonJ_ne_bot hT.2.1 hT1) (CFSG.Quasithin.B6.thompsonJ_le T)
    (Setup.characteristic_thompsonJ T)
  set T' : Subgroup ↥M := T.subgroupOf M with hT'def
  set D : Subgroup G := GLBPrimeCore 3 M with hD
  set D' : Subgroup ↥M := D.subgroupOf M with hD'
  set L' : Subgroup ↥M := L.subgroupOf M with hL'
  set C' : Subgroup ↥M := gnC T' with hC'
  have hLM : L ≤ M := hlay.1
  have hDL : D ≤ L := hlay.2.1
  have hL'n : L'.Normal := hlay.2.2.1
  have hD'L' : D' ≤ L' := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hDL (Subgroup.mem_subgroupOf.mp hx))
  set C : Subgroup G := C'.map M.subtype with hC
  have h3C : CFSG.HallHigman.IsPSolvable 3 ↥C := isPSolvable_map_gnC hTM hNZ
  have hCM : C ≤ M := by
    rintro _ ⟨c, -, rfl⟩
    exact c.2
  have hCn : (C.subgroupOf M).Normal := by
    have : C.subgroupOf M = C' := Subgroup.comap_map_eq_self_of_injective M.subtype_injective C'
    rw [this]; infer_instance
  obtain ⟨hLC, -⟩ := inf_le_core_of_psolvable hlay hCM hCn h3C
  set E : Subgroup ↥M := C' ⊔ D' with hE
  set LE : Subgroup ↥M := L' ⊔ E with hLE
  have hDE : D' ≤ E := le_sup_right
  have hKN : L' ⊓ E = D' := by
    apply le_antisymm
    · rintro x ⟨hxL, hxE⟩
      obtain ⟨c, hc', d, hd, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxE
      have hdL : d ∈ L' := hD'L' hd
      have hcL : c ∈ L' := by simpa using L'.mul_mem hxL (L'.inv_mem hdL)
      have hcG : (c : G) ∈ L ⊓ C := ⟨Subgroup.mem_subgroupOf.mp hcL, ⟨c, hc', rfl⟩⟩
      exact D'.mul_mem (Subgroup.mem_subgroupOf.mpr (hLC hcG)) hd
    · exact le_inf hD'L' hDE
  have hmapE : LE.map (QuotientGroup.mk' E) = L'.map (QuotientGroup.mk' E) := by
    rw [hLE, Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]
  let φ := CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.AutImageStar.quotMapEquiv L' D' E hDE hKN
  have hS : IsSimpleGroup ↥(L'.map (QuotientGroup.mk' D')) := hlay.2.2.2.1
  have hnc : ¬ IsMulCommutative ↥(L'.map (QuotientGroup.mk' D')) := hlay.2.2.2.2.1
  have hty : IsRankTwoLayerType ↥(L'.map (QuotientGroup.mk' D')) := hlay.2.2.2.2.2
  have hsimple : IsSimpleGroup ↥(LE.map (QuotientGroup.mk' E)) := by
    rw [hmapE]
    have := hS
    exact MulEquiv.isSimpleGroup φ.symm
  have hnc' : ¬ IsMulCommutative ↥(LE.map (QuotientGroup.mk' E)) := by
    rw [hmapE]
    intro hcm
    apply hnc
    refine ⟨⟨fun a b => ?_⟩⟩
    have := hcm.is_comm.comm (φ a) (φ b)
    exact φ.injective (by rw [map_mul, map_mul]; exact this)
  have hty' : IsRankTwoLayerType ↥(LE.map (QuotientGroup.mk' E)) := by
    rw [hmapE]
    exact isRankTwoLayerType_of_equiv φ hty
  have hD3 : ¬ 3 ∣ Nat.card D' := by
    have hDM : D ≤ M := glbPrimeCore_le 3 M
    rw [hD', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (glbPrimeCore_coprime 3 M)
  have h3 : ¬ 3 ∣ Nat.card ↥(E.map (QuotientGroup.mk' (gnC T'))) := by
    have : E.map (QuotientGroup.mk' (gnC T')) = D'.map (QuotientGroup.mk' (gnC T')) := by
      rw [hE, Subgroup.map_sup, hC', QuotientGroup.map_mk'_self, bot_sup_eq]
    rw [this]
    intro h
    exact hD3 (dvd_trans h (Subgroup.card_map_dvd D' _))
  have hJ := layer_le_commutator_thompsonJ hlay hT hNJ
  have hT'map : T'.map M.subtype = T := by
    rw [hT'def, Subgroup.subgroupOf_map_subtype, inf_of_le_left hTM]
  have hJmap : (thompsonJ T').map M.subtype = thompsonJ T := by
    rw [← thompsonJ_map_of_injective' M.subtype_injective, hT'map]
  have hLmap : L'.map M.subtype = L := by
    rw [hL', Subgroup.subgroupOf_map_subtype, inf_of_le_left hLM]
  have hDmap : D'.map M.subtype = D := by
    rw [hD', Subgroup.subgroupOf_map_subtype, inf_of_le_left (glbPrimeCore_le 3 M)]
  have hJ' : L' ≤ ⁅L', thompsonJ T'⁆ ⊔ D' := by
    rw [← Subgroup.map_le_map_iff_of_injective M.subtype_injective, Subgroup.map_sup,
      Subgroup.map_commutator, hLmap, hJmap, hDmap]
    exact hJ
  have hJE : LE ≤ ⁅LE, thompsonJ T'⁆ ⊔ E :=
    sup_le (hJ'.trans (sup_le_sup (Subgroup.commutator_mono le_sup_left le_rfl) hDE)) le_sup_right
  have hEn : E.Normal := inferInstance
  have hLEn : LE.Normal := inferInstance
  have hAut := hI ↥M T' hGN E LE le_sup_left le_sup_right h3 hsimple hnc' hty' hJE
  rw [hmapE] at hAut
  exact autImageOK_of_quot hlay E hDE hKN hAut

theorem d2L34BetaLayerAutImage3_proved
    (hN : D2L34BetaNormalizerSolvable3 G) (hD1 : D1NoXBlock3 G) : D2L34BetaLayerAutImage3 G :=
  d2L34BetaLayerAutImage3_of_I542Three agl81I542Three hN hD1

end CFSG.LocalAnalysis.RankThreeTheoremC
