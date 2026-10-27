module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinWireIfc
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinE4PerfPf4FinV2
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVKPfConn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfTables
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Twin1711PfPerfect

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrame

set_option linter.unusedSectionVars false

theorem e4_of_1711Out {n : ℕ} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n) (hthin : TwinThinInput n)
    (hPerf : TwinE4Perfect n) (hT1 : Fin1711Sandwich) (hT2 : Fin1711Pairing) :
    ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TwinCoreHyp n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
        ∀ π : Set (Subgroup Y),
          π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) →
          NoCentralInv π → ∀ g : Y, conjSub g (tightCore R) ∈ π →
            ¬ TwinE4 (SecQuot (conjSub g (piGen π))) := by
  intro Y _ _ R S t h hconn π hπ hH1 g hg hE4
  obtain ⟨hθ', hmem, -, hgs⟩ := hPre _ _ _ _ h hconn
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  have hK₀Ω : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core h.datum
  have hos := hgs.orbitStd
  have hq8 : Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) := (hmem _ hK₀Ω).2
  have hKX : tightCore R ≤ conjSub g (piGen π) := hos.le_conj_piGen hπ hg
  have hw : IsUniqueInvolution (conjSub g (tightCore R)) (g * t * g⁻¹) := hz.conj g
  have hXw := (hos.conj_piGen_le_centralizer hK₀Ω hπ hH1 hz g).1
  have hXn := hos.conj_piGen_normal hK₀Ω hπ hH1 hz g
  have hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥ :=
    TwinSecXg.oddCore_eq_bot_of_normal hXn hXw (hθ' _ ⟨g, rfl⟩ _ hw)
  have hnotO2 : ¬ TightInO2 (secInv (conjSub g (piGen π)) ⟨t, hKX hz.mem⟩) := fun hO2 =>
    hthin Y R S t h hconn (TwinSecXg.twin_thin_of_tightInO2 hgs
      (fun _ hPn hP => TwinSecXg.normalTwo_eq_bot_of_fstar_simple h.simple h.nonab hPn hP)
      hK₀Ω (hmem _ hK₀Ω).2 hπ hH1 hz hg hKX hO hO2)
  have hperf := hPerf Y R S t h hconn π hπ hH1 g hg hKX t hz hnotO2 hE4
  have hcfg : Twin1711.Cfg' (CoreAssembly.conjClass (tightCore R)) (tightCore R) π t g :=
    ⟨⟨hos, TwinSecXg.conj_trans_of_mem_conjClass hK₀Ω, iSup_conjClass_eq_top hgs.gen, hZ, hK₀Ω,
      hπ, hH1, hz, hq8⟩, hg⟩
  have h2 := hcfg.swap
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := hE4
  let F : ↥(conjSub g (piGen π)) →* Q := f.comp (QuotientGroup.mk' _)
  have hFs : Function.Surjective F := hfs.comp (QuotientGroup.mk'_surjective _)
  have hker : IsPGroup 2 ↥F.ker := by
    have hmk : IsPGroup 2 ↥(QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjSub g (piGen π)))).ker := by
      rw [QuotientGroup.ker_mk', hO]
      exact IsPGroup.of_card (n := 0) (by simp)
    exact hf2.comap_of_ker_isPGroup _ hmk
  have hFt : F ⟨t, hKX hz.mem⟩ ≠ 1 := by
    intro h1
    exact hnotO2 ⟨f.ker, MonoidHom.normal_ker f, hf2, h1⟩
  have hw' : IsUniqueInvolution (conjSub g⁻¹ (conjSub g (tightCore R))) t := by
    rw [conjSub_inv_conjSub]; exact hz
  have hQE := h2.quasiE4_of_surj hw' (piGen_conj π g) (hKX hz.mem) hperf F hFs hker hQ hFt
  exact Twin1711.not_quasiE4 hT1 hT2 h2 (by rw [piGen_conj]; exact hQE)

open TwinE4Perf in
theorem twinE4Untwisted_of_fin3TOut {n : ℕ} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n) (hF3 : Fin3ActsModels) :
    TwinE4Untwisted n := by
  intro Y _ _ R S t h hconn π hπ hH1 g hg hKX z hz hnot hE4
  obtain ⟨hθ', hmem, -, hgs⟩ := hPre _ _ _ _ h hconn
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  have hK₀Ω : tightCore R ∈ CoreAssembly.conjClass (tightCore R) :=
    CoreAssembly.mem_conjClass_self _
  have hos := hgs.orbitStd
  have hq8 : Nonempty (↥(tightCore R) ≃* QuaternionGroup 2) := (hmem _ hK₀Ω).2
  have hw : IsUniqueInvolution (conjSub g (tightCore R)) (g * z * g⁻¹) := hz.conj g
  have hXw := (hos.conj_piGen_le_centralizer hK₀Ω hπ hH1 hz g).1
  have hXn := hos.conj_piGen_normal hK₀Ω hπ hH1 hz g
  have hO : classicalInvolutionOddCore ↥(conjSub g (piGen π)) = ⊥ :=
    TwinSecXg.oddCore_eq_bot_of_normal hXn hXw (hθ' _ ⟨g, rfl⟩ _ hw)
  have hcfg : Twin1711.Cfg' (CoreAssembly.conjClass (tightCore R)) (tightCore R) π z g :=
    ⟨⟨hos, TwinSecXg.conj_trans_of_mem_conjClass hK₀Ω, iSup_conjClass_eq_top hgs.gen, hZ, hK₀Ω,
      hπ, hH1, hz, hq8⟩, hg⟩
  have h2 := hcfg.swap
  obtain ⟨Q, _, f, hfs, hf2, hQ⟩ := hE4
  let F : ↥(conjSub g (piGen π)) →* Q := f.comp (QuotientGroup.mk' _)
  have hFs : Function.Surjective F := hfs.comp (QuotientGroup.mk'_surjective _)
  have hker : IsPGroup 2 ↥F.ker := by
    have hmk : IsPGroup 2
        ↥(QuotientGroup.mk' (classicalInvolutionOddCore ↥(conjSub g (piGen π)))).ker := by
      rw [QuotientGroup.ker_mk', hO]
      exact IsPGroup.of_card (n := 0) (by simp)
    exact hf2.comap_of_ker_isPGroup _ hmk
  have hFz : F ⟨z, hKX hz.mem⟩ ≠ 1 := by
    intro h1
    exact hnot ⟨f.ker, MonoidHom.normal_ker f, hf2, h1⟩
  have hw' : IsUniqueInvolution (conjSub g⁻¹ (conjSub g (tightCore R))) z := by
    rw [conjSub_inv_conjSub]; exact hz
  exact TwinE4Perf.members_le_commutator_of_cfg2' h2 hF3 (Twin1711.Cfg'.Y_eq π g).symm hw'
    (hKX hz.mem) F hFs hker hQ hFz

open TwinE4Perf in
theorem twinE4Perfect_of_fin3TOut {n : ℕ} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n) (hF3 : Fin3ActsModels) :
    TwinE4Perfect n :=
  twinE4Perfect_of_untwisted (twinE4Untwisted_of_fin3TOut hSp hD4m hM12 hPre hEdg hF3)

theorem twinE4Perfect_of_certsOut {n : ℕ} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n) : TwinE4Perfect n :=
  twinE4Perfect_of_fin3TOut hSp hD4m hM12 hPre hEdg fin3ActsModels_of_certs₂

theorem TwinConnPreS.of_outV {Y : Type} [Group Y] [Finite Y] {n : ℕ} {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n) (h : TwinCoreHyp n Y R S t)
    (hconn : DConnected (CoreAssembly.conjClass (tightCore R))) (hT : Thm1RTwinLiftSetBelow n) :
    TwinConnPreS n R t := by
  obtain ⟨hθ', hmem, -, hgs⟩ := hPre _ _ _ _ h hconn
  have hZ : Subgroup.center Y = ⊥ :=
    InductionBridge.center_eq_bot_of_fstar_simple h.simple h.nonab
  exact ⟨h.card, h.simple, h.nonab, h.below, hT, h.aEmpty, Q8Datum.isUniqueInvolution_core h.datum,
    h.twin, hθ', hmem, hgs, hEdg _ _ _ _ h hZ⟩

theorem TwinConnPreS.of_outSV {Y : Type} [Group Y] [Finite Y] {n : ℕ} {R : Subgroup Y}
    {S : Sylow 2 R} {t : Y} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n) (h : TwinCoreHypS n Y R S t)
    (hconn : DConnected (CoreAssembly.conjClass (tightCore R))) : TwinConnPreS n R t :=
  TwinConnPreS.of_outV hSp hD4m hM12 hPre hEdg h.toHyp hconn h.twinBelow

theorem twinCoreConnSE'_of_outV {n : ℕ} (hSp : TwinCentRes.ModelFactSp62)
    (hD4m : TwinCentRes.ModelFactD42) (hM12 : TwinCentRes.ModelFactM12)
    (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n)
    (hthin : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TwinCoreHyp n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
        ¬ ∀ M N : Subgroup Y, MaxAdj (nbrAdj (CoreAssembly.conjClass (tightCore R))) M N →
          ThinAt (CoreAssembly.conjClass (tightCore R)) M N)
    (he4 : ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
      TwinCoreHyp n Y R S t → DConnected (CoreAssembly.conjClass (tightCore R)) →
        ∀ π : Set (Subgroup Y),
          π ∈ maxOrbs (nbrAdj (CoreAssembly.conjClass (tightCore R))) (tightCore R) →
          NoCentralInv π → ∀ g : Y, conjSub g (tightCore R) ∈ π →
            ¬ TwinE4 (SecQuot (conjSub g (piGen π)))) :
    TwinCoreConnSE' n :=
  twinCoreConnSE'_of_prelude (fun _ _ _ _ _ _ h hconn => TwinConnPreS.of_outSV hSp hD4m hM12 hPre hEdg h hconn)
    (fun Y _ _ R S t h hconn => hthin Y R S t h.toHyp hconn)
    (fun Y _ _ R S t h hconn => he4 Y R S t h.toHyp hconn)

theorem twinCoreConnSE'_of_1711Out {n : ℕ}
    (hSp : TwinCentRes.ModelFactSp62) (hD4m : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n) (hthin : TwinThinInput n)
    (hPerf : TwinE4Perfect n) (hT1 : Fin1711Sandwich) (hT2 : Fin1711Pairing) :
    TwinCoreConnSE' n :=
  twinCoreConnSE'_of_outV hSp hD4m hM12 hPre hEdg hthin
    (e4_of_1711Out hSp hD4m hM12 hPre hEdg hthin hPerf hT1 hT2)

theorem twinCoreConnSE'_of_pfOut {n : ℕ}
    (hSp : TwinCentRes.ModelFactSp62) (hD4m : TwinCentRes.ModelFactD42)
    (hM12 : TwinCentRes.ModelFactM12) (hPre : TwinConnPreludeOut n) (hEdg : TwinConnEdgesOut n) (hthin : TwinThinInput n)
    (hPerf : TwinE4Perfect n) (hT : Twin1711.PfTables) : TwinCoreConnSE' n :=
  twinCoreConnSE'_of_1711Out hSp hD4m hM12 hPre hEdg hthin hPerf
    (Twin1711.fin1711Sandwich_of_tables hT) (Twin1711.fin1711Pairing_of_tables hT)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
