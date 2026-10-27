
module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.PositiveCore
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

namespace L238

variable {G : Type} [Group G]

theorem ne_bot_of_isGamma0 [Finite G] {T M H S : Subgroup G} (h : UniqueSetting G T M)
    (hH : IsGamma0 M H) (hS : IsSylowTwoOf S (H ⊓ M)) : S ≠ ⊥ := by
  obtain ⟨hSH, -, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  intro hbot
  have hle := hSH.pCoreOf_le
  rw [hbot] at hle
  exact hH.isGamma.1 (le_bot_iff.mp hle)

theorem cgsIn_le_inf [Finite G] {T M H S : Subgroup G} (h : UniqueSetting G T M)
    (hH : IsGamma0 M H) (hc : CharTwo H) (hS : IsSylowTwoOf S (H ⊓ M)) : cgsIn H S ≤ H ⊓ M :=
  iSup_le fun _ => iSup_le fun hCS => iSup_le fun hC1 => iSup_le fun hCc =>
    hH.normalizer_inf_le_of_characteristic h hc hS hC1 hCS hCc

theorem inf_normalizer_le [Finite G] {T M H S : Subgroup G} (h : UniqueSetting G T M)
    (hH : IsGamma0 M H) (hc : CharTwo H) (hS : IsSylowTwoOf S (H ⊓ M)) :
    H ⊓ Subgroup.normalizer (S : Set G) ≤ M := by
  have hS1 := ne_bot_of_isGamma0 h hH hS
  have hchar : (S.subgroupOf S).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact (hH.normalizer_inf_le_of_characteristic h hc hS hS1 le_rfl hchar).trans inf_le_right

theorem pCoreOf_le_pCoreOf_of_sylow {H S P : Subgroup G} (hSH : IsSylowTwoOf S H) (hSP : S ≤ P)
    (hPH : P ≤ H) : pCoreOf 2 H ≤ pCoreOf 2 P :=
  le_pCoreOf_of_normalizes (hSH.pCoreOf_le.trans hSP)
    (hPH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H))
    (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H)

theorem isMinimalParabolic_of_mem_uFamHat [Finite G] {H S P : Subgroup G}
    (hSH : IsSylowTwoOf S H) (hP : P ∈ uFamHat H S) : IsMinimalParabolic S P := by
  have hPH : P ≤ H := hP.1.1
  have hSP : S < P := hP.1.2.1
  have hSyl : IsSylowTwoOf S P := C1GN.isSylowTwoOf_of_le hSH hSP.le hPH
  have hmin : IsMinParabolicOf P P := ⟨S, hSyl, ⟨le_rfl, hSP, hP.1.2.2⟩, hP.2⟩
  obtain ⟨M₀, hM₀⟩ := Set.ncard_eq_one.1 hP.1.2.2
  exact minParabolic_exists_iff.1 ⟨M₀, minParabolic_iff.2 ⟨hmin, hSyl, hM₀⟩⟩

theorem pushUpObstruction_of_mem_uFamHat [Finite G] {T M H S P : Subgroup G}
    (h : UniqueSetting G T M) (hH : IsGamma0 M H) (hc : CharTwo H)
    (hS : IsSylowTwoOf S (H ⊓ M)) (hP : P ∈ uFamHat H S) (hPM : ¬ P ≤ M) :
    PushUpObstruction S P := by
  obtain ⟨hSH, -, -⟩ := IsGamma.sylow_properties h hH.isGamma hS
  have hPH : P ≤ H := hP.1.1
  have hSP : S ≤ P := hP.1.2.1.le
  have hmin := isMinimalParabolic_of_mem_uFamHat hSH hP
  have hcore : pCoreOf 2 P ≠ ⊥ := by
    intro hbot
    have hle := pCoreOf_le_pCoreOf_of_sylow hSH hSP hPH
    rw [hbot] at hle
    exact hH.isGamma.1 (le_bot_iff.mp hle)
  refine ⟨hmin.1, C1GN.charTwo_of_le hc hSH hSP hPH, hmin,
    positiveTwoCoreSQTK G T M h P hcore, ?_⟩
  intro R hR1 hRS hRc hPN
  exact hPM ((le_inf hPH hPN).trans
    ((hH.normalizer_inf_le_of_characteristic h hc hS hR1 hRS hRc).trans inf_le_right))

theorem exists_block_of_mem_uFamHat [Finite G] (hMB : MinParabolicBlocks) {T M H S P : Subgroup G}
    (h : UniqueSetting G T M) (hH : IsGamma0 M H) (hc : CharTwo H)
    (hS : IsSylowTwoOf S (H ⊓ M)) (hP : P ∈ uFamHat H S) (hPM : ¬ P ≤ M) :
    ∃ L : Subgroup G, IsChi0Block P L ∧ ⁅L, thompsonJ S⁆ = L ∧ ¬ L ≤ M ∧
      P = conjJoin S L ⊔ S := by
  obtain ⟨L, hL, hLJ, hPL, -⟩ := hMB G S P (pushUpObstruction_of_mem_uFamHat h hH hc hS hP hPM)
  refine ⟨L, hL, hLJ, ?_, hPL⟩
  intro hLM
  apply hPM
  rw [hPL]
  have hSM : S ≤ M := hS.le.trans inf_le_right
  refine sup_le (iSup_le fun s => ?_) hSM
  rintro _ ⟨y, hy, rfl⟩
  have hsM : (s : G) ∈ M := hSM s.2
  show (s : G) * y * (s : G)⁻¹ ∈ M
  exact M.mul_mem (M.mul_mem hsM (hLM hy)) (M.inv_mem hsM)

end L238

end CFSG.QuasithinUnique
