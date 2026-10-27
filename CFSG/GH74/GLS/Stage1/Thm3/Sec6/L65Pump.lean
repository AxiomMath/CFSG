module

public import CFSG.GH74.GLS.TwoThin.PumpData
public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.ComponentClassification
  CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def ABar (I : Subgroup G) (w : G) :
    Subgroup (barQ ↥(centralizer ({w} : Set G))) :=
  (I.subgroupOf (centralizer ({w} : Set G))).map (barMk ↥(centralizer ({w} : Set G)))

@[expose] noncomputable def sBar (z w : G) (hzw : z ∈ centralizer ({w} : Set G)) :
    barQ ↥(centralizer ({w} : Set G)) :=
  barMk ↥(centralizer ({w} : Set G)) ⟨z, hzw⟩

theorem orderOf_sBar {z w : G} (hz : orderOf z = 2) (hzw : z ∈ centralizer ({w} : Set G)) :
    orderOf (sBar z w hzw) = 2 :=
  orderOf_barMk (orderOf_mk_centralizer hzw hz)

theorem ABar_le_centralizer {z w : G} (hz : orderOf z = 2) (hzw : z ∈ centralizer ({w} : Set G))
    {I : Subgroup G}
    (hI : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G)) I) :
    ABar I w ≤ centralizer ({sBar z w hzw} : Set (barQ ↥(centralizer ({w} : Set G)))) :=
  (Subgroup.map_mono (le_centralizer_mk (isPCompIn_two_iff.mp hI).1 hzw)).trans
    (map_centralizer_barMk (orderOf_mk_centralizer hzw hz)).le

theorem ABar_isComponent (hG : IsKProperSimple G) (hgen4 : CFSG.GH74.Gen4 G) (hB2 : B_B2_g4)
    {z w : G} (hz : orderOf z = 2) (hw : orderOf w = 2) (hzw : z ∈ centralizer ({w} : Set G))
    {I : Subgroup G}
    (hI : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G)) I) :
    CFSG.IsComponent ((ABar I w).subgroupOf
      (centralizer ({sBar z w hzw} : Set (barQ ↥(centralizer ({w} : Set G)))))) := by
  set Y' := centralizer ({w} : Set G) with hY'
  have hY'ne : Y' ≠ ⊤ := centralizer_involution_ne_top hG.1 hG.2.1 hw
  have hX : IsKGroupNative (barQ ↥Y') :=
    isKGroupNative_of_surjective (X := ↥Y') (isKGroupNative_of_kProper hG.2.2 hY'ne) ⊤
      ((barMk ↥Y').comp (⊤ : Subgroup ↥Y').subtype)
      (barMk_surjective.comp fun m => ⟨⟨m, trivial⟩, rfl⟩)
  have hso : orderOf (⟨z, hzw⟩ : ↥Y') = 2 := orderOf_mk_centralizer hzw hz
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hI).1 hzw
  have hΛ2 := isTwoComponent_centralizer_mk hI hzw
  have hmap2 := isTwoComponent_map_barMk hso hΛC hΛ2
  have hle := ABar_le_centralizer hz hzw hI
  have hpc : IsPCompIn 2 (centralizer ({sBar z w hzw} : Set _)) (ABar I w) :=
    isPCompIn_two_iff.mpr ⟨hle, hmap2⟩
  have hcore : pPrimeCore 2 (barQ ↥Y') = ⊥ := by
    have := oddCore_barQ (Y := ↥Y')
    rwa [← CatalogueBAlternating.primeCore_two_eq_oddCore] at this
  have hg4 : CFSG.GH74.Gen4 (barQ ↥Y') := CFSG.GH74.Gen4.quotient _ (CFSG.GH74.Gen4.subgroup Y' hgen4)
  exact (hB2 _ hg4 hX hcore (sBar z w hzw) (orderOf_sBar hz hzw) (ABar I w) hpc).2

theorem pump_dichotomy {z w : G} (hz : orderOf z = 2) (hzw : z ∈ centralizer ({w} : Set G))
    {I : Subgroup G}
    (hI : IsPCompIn 2 (centralizer ({z} : Set G) ⊓ centralizer ({w} : Set G)) I) :
    ∃ L : Subgroup (barQ ↥(centralizer ({w} : Set G))), CFSG.IsComponent L ∧
      ((conjSub (sBar z w hzw)⁻¹ L = L ∧ ABar I w ≤ L) ∨
        (conjSub (sBar z w hzw)⁻¹ L ≠ L ∧ ∃ hAB : ⁅L, conjSub (sBar z w hzw)⁻¹ L⁆ = ⊥,
          ABar I w ≤ (swapDiag hAB).range)) := by
  have hso := orderOf_mk_centralizer hzw hz
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp hI).1 hzw
  have hΛ2 := isTwoComponent_centralizer_mk hI hzw
  obtain ⟨-, -, L, hL, hcases, -⟩ := pumpupY_structure hso hΛC hΛ2
  exact ⟨L, hL, hcases⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
