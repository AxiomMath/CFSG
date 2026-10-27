module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.GNSettingM
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerThompson
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.LayerAutImageQuot
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.PSolvableSub
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbeddingD2 CFSG.AGLEmbedding
open scoped commutatorElement

@[expose] def AGL81I542Three : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ (E L : Subgroup X) [E.Normal] [L.Normal], gnC T ≤ E → E ≤ L →
      ¬ 3 ∣ Nat.card ↥(E.map (QuotientGroup.mk' (gnC T))) →
      IsSimpleGroup ↥(L.map (QuotientGroup.mk' E)) →
      ¬ IsMulCommutative ↥(L.map (QuotientGroup.mk' E)) →
      IsRankTwoLayerType ↥(L.map (QuotientGroup.mk' E)) →
      L ≤ ⁅L, thompsonJ T⁆ ⊔ E → AutInOK (L.map (QuotientGroup.mk' E))

theorem statedPSL_of_equiv' {G G' : Type} [Group G] [Group G'] {n p f : ℕ} (e : G ≃* G')
    (h : StatedClassicalModel G .PSL n p f) : StatedClassicalModel G' .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem statedPSU_of_equiv' {G G' : Type} [Group G] [Group G'] {n p f : ℕ} (e : G ≃* G')
    (h : StatedClassicalModel G .PSU n p f) : StatedClassicalModel G' .PSU n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h

theorem isRankTwoLayerType_of_equiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsRankTwoLayerType A) : IsRankTwoLayerType B := by
  rcases h with h | h | h
  · obtain ⟨i⟩ := h
    exact Or.inl ⟨e.symm.trans i⟩
  · exact Or.inr (Or.inl (statedPSL_of_equiv' e h))
  · exact Or.inr (Or.inr (statedPSU_of_equiv' e h))


theorem map_gnC_le {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M) :
    (gnC (T.subgroupOf M)).map M.subtype ≤
      Subgroup.normalizer (omegaOneCenterOf T : Set G) ⊓ M := by
  have hT' : (T.subgroupOf M).map M.subtype = T := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hTM]
  have hZ : (omegaOneCenterOf (T.subgroupOf M)).map M.subtype = omegaOneCenterOf T := by
    rw [← omegaOneCenterOf_map_of_injective M.subtype_injective, hT']
  rintro _ ⟨c, hc, rfl⟩
  refine ⟨?_, c.2⟩
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [← hZ] at hz
  obtain ⟨w, hw, rfl⟩ := hz
  have hwV : w ∈ gnV (T.subgroupOf M) := Subgroup.subset_normalClosure hw
  have := Subgroup.mem_centralizer_iff.mp hc w hwV
  exact congrArg Subtype.val this

theorem isPSolvable_map_gnC {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)
    (hN : CFSG.HallHigman.IsPSolvable 3 ↥(Subgroup.normalizer (omegaOneCenterOf T : Set G) ⊓ M)) :
    CFSG.HallHigman.IsPSolvable 3 ↥((gnC (T.subgroupOf M)).map M.subtype) := by
  set C : Subgroup G := (gnC (T.subgroupOf M)).map M.subtype with hC
  set NZ : Subgroup G := Subgroup.normalizer (omegaOneCenterOf T : Set G) ⊓ M with hNZ
  have hCle : C ≤ NZ := map_gnC_le hTM
  have hCnorm : ∀ n ∈ NZ, ∀ c ∈ C, n * c * n⁻¹ ∈ C := by
    rintro n hn _ ⟨c, hc, rfl⟩
    refine ⟨⟨n, hn.2⟩ * c * ⟨n, hn.2⟩⁻¹, ?_, rfl⟩
    exact (inferInstance : (gnC (T.subgroupOf M)).Normal).conj_mem c hc _
  have hNorm : (C.subgroupOf NZ).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using hCnorm g g.2 x hx
  have h1 := isPSolvable_of_isSubnormal hN hNorm.isSubnormal
  exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.QuasisimpleSolvableNormal.isPSolvable_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hCle) h1


theorem d2L34BetaLayerAutImage_of_I542Three (hI : AGL81I542Three)
    (hN : D2L34BetaNormalizerSolvable) (hD1 : D1NoXBlock) : D2L34BetaLayerAutImage := by
  intro d G _ _ P M A H R Rbar K hc hstr hAll hKmax hcon L hlay
  classical
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf M
  have hTM : T ≤ M := hT.1
  have hGN := MsideParabolicEscape.D2L34BetaConf.gnSetting hc hD1 hT
  have hT1 : T ≠ ⊥ := by
    intro h
    apply CFSG.PreuniquenessRankFour.Helpers.twoLocal_pCoreOf_ne_bot hc.esc.maxTwoLocal_M.1
    rw [eq_bot_iff, ← h]
    exact CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hNZ := hN d G P M A H R Rbar K hc hstr hAll hKmax T hT (omegaOneCenterOf T)
    (Setup.omegaOneCenterOf_ne_bot hT.2.1 hT1) (Setup.omegaOneCenterOf_le T)
    (Setup.characteristic_omegaOneCenterOf T)
  have hNJ := hN d G P M A H R Rbar K hc hstr hAll hKmax T hT (thompsonJ T)
    (Setup.thompsonJ_ne_bot hT.2.1 hT1) (CFSG.Quasithin.B6.thompsonJ_le T)
    (Setup.characteristic_thompsonJ T)
  set T' : Subgroup ↥M := T.subgroupOf M with hT'def
  set D : Subgroup G := GLBPrimeCore 3 M with hD
  set D' : Subgroup ↥M := D.subgroupOf M with hD'
  set L' : Subgroup ↥M := L.subgroupOf M with hL'
  set C' : Subgroup ↥M := gnC T' with hC'
  have hLM : L ≤ M := hlay.1
  have hDL : D ≤ L := hlay.2.1
  haveI hL'n : L'.Normal := hlay.2.2.1
  have hD'L' : D' ≤ L' := fun x hx => Subgroup.mem_subgroupOf.mpr (hDL (Subgroup.mem_subgroupOf.mp hx))
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
    haveI := hS
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
  haveI hEn : E.Normal := inferInstance
  haveI hLEn : LE.Normal := inferInstance
  have hAut := hI ↥M T' hGN E LE le_sup_left le_sup_right h3 hsimple hnc' hty' hJE
  rw [hmapE] at hAut
  exact autImageOK_of_quot hlay E hDE hKN hAut

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
