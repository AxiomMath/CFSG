module

public import CFSG.LocalAnalysis.SeitzReduction.E8PilotMain
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotUniqueFieldStep3

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.E8Pilot

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.EvenSmallLie
open CFSG.Quasithin (perfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatLeaf (GLS3OddLieAutComponentsInput MonsterInnerInput
  MonsterLocalComponentsInput)
open CFSG.SeitzReduction.F4Pilot (QuadraticFrobenius centralizerPerfectCore)
open E6Pilot (modelToG)

section Fix

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem modelToG_map_subtype_levi_high (e : L ≃* adjointGroup .E8 K) :
    modelToG e ((E8Neighbour.high.levi K).map (adjointGroup .E8 K).subtype) = rootLeviG e := by
  rw [E8Neighbour.levi_high, modelToG, rootLeviG]
  congr 2
  exact Subgroup.comap_map_eq_self_of_injective (adjointGroup .E8 K).subtype_injective _

theorem perfectCore_neighbourCore_high_inf_centralizer {t : G} {f : ℕ} (hw : E8Work L K t f)
    (hf : 2 ≤ f) (e : L ≃* adjointGroup .E8 K) :
    perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) =
      modelToG e ((E8Neighbour.high.levi K).map (adjointGroup .E8 K).subtype) := by
  have := F4Pilot.finite_of_natCard_eq_two_pow hw.card_eq
  have := F4Pilot.charP_two_of_natCard_eq_two_pow hw.card_eq
  have hq : 4 ≤ Nat.card K := by
    rw [hw.card_eq]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have htC := hw.mem_centralizer
  rw [modelToG_map_subtype_levi_high]
  set A : Subgroup (adjointGroup .E8 K) :=
    (EPilot.highTorusLine .E8 K).subgroupOf (adjointGroup .E8 K) with hA
  set X : Subgroup G := rootTorusG e with hXdef
  set D : Subgroup G := rootLeviG e with hDdef
  have hX : X = (A.map e.symm.toMonoidHom).map L.subtype := rfl
  have hDe : D = ((e7Levi K).map e.symm.toMonoidHom).map L.subtype := rfl
  have hE : neighbourCore e .high = centralizerPerfectCore X := by
    rw [neighbourCore_high]
    rfl
  have hDperf : ⁅D, D⁆ = D := by
    have hCp : ⁅e7Levi K, e7Levi K⁆ = e7Levi K := isPerfect_iff.mp isQuasisimple_e7Levi.1
    rw [hDe, ← map_commutator, ← map_commutator, hCp]
  have hDE : D ≤ neighbourCore e .high := modelToG_rootSpan_perpRoots_le_neighbourCore_high e
  have hDt : D ≤ centralizer ({t} : Set G) := fun d hd =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC d (map_subtype_le _ hd))
  refine le_antisymm ?_ (CFSG.Quasithin.le_perfectCore_of_perfect (le_inf hDE hDt) hDperf)
  set P := perfectCore (neighbourCore e .high ⊓ centralizer ({t} : Set G)) with hPdef
  have hP : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect _
  have hPt : P ≤ centralizer ({t} : Set G) := (CFSG.Quasithin.perfectCore_le _).trans inf_le_right
  have hOut : Group.IsSolvable (Outer L) :=
    ⟨⟨2, derivedSeries_outer_eq_bot_of_mulEquiv e (exceptional_E_pinned_model_Schreier K).2.2⟩⟩
  have hPL : P ≤ L := std_perfect_le hw.standard hOut htC hw.orderOf_eq hP hPt
  have hPX : P ≤ centralizer (X : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans
      (inf_le_left.trans (hE ▸ F4Pilot.centralizerPerfectCore_le_centralizer _))
  have hPLX : P ≤ L ⊓ centralizer (X : Set G) := le_inf hPL hPX
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  have hcen := E6Pilot.centralizer_eq_highTorusLine_sup_of_le (τ := .E8) (Or.inr (Or.inr rfl)) hc
    le_rfl (Subgroup.mem_subgroupOf.2 (EPilot.rootDiagUnit_highDiag_mem_highTorusLine c))
  rw [hX, F4Pilot.inf_centralizer_map_symm, hcen, Subgroup.map_sup, Subgroup.map_sup, ← hX] at hPLX
  have hXD : X ≤ centralizer (D : Set G) := by
    rw [hX, hDe]
    exact le_centralizer_iff.mp
      (F4Pilot.map_map_symm_le_centralizer e E6Pilot.highTorusLine_subgroupOf_le_centralizer_perpLevi)
  have hXX : X ≤ centralizer (X : Set G) := by
    rw [hX]
    exact F4Pilot.map_map_symm_le_centralizer e E6Pilot.highTorusLine_subgroupOf_le_centralizer_self
  have hXsolv : Group.IsSolvable X := Group.isSolvable_of_comm fun a b =>
    Subtype.ext (mem_centralizer_iff.1 (hXX b.2) a a.2)
  exact perfect_le_of_le_sup (hXD.trans (centralizer_le_normalizer _)) hXsolv hP
    (by rw [sup_comm]; exact hPLX)

end Fix

@[expose] def E8FieldNeighbourIsoInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (K₂ : Type) [Field K₂] [Finite K₂]
    [CharP K₂ 2] (σ : K₂ ≃+* K₂) (f : ℕ), QuadraticFrobenius K₂ σ f → 2 ≤ f →
    ∀ (e : L ≃* adjointGroup .E8 (fixSubfield σ)) (t : G), E8Work L (fixSubfield σ) t f →
    HR8FieldE8 e t f → Nonempty (E8Neighbour.high.levi K₂ ≃* neighbourCore e .high)

theorem e8FieldNeighbourInput_of_iso (h : E8FieldNeighbourIsoInput) : E8FieldNeighbourInput := by
  intro G _ _ L K₂ _ _ _ σ f hq hf e t hw hX
  exact ⟨h G L K₂ σ f hq hf e t hw hX, perfectCore_neighbourCore_high_inf_centralizer hw hf e⟩

theorem seitzExclusion_highE8_of_inputs' (hGLS : GLS3OddLieAutComponentsInput)
    (hE7Odd : E7NotOddLieInput) (hMinn : MonsterInnerInput)
    (hMcomp : MonsterLocalComponentsInput) (hFI : E8FieldNeighbourIsoInput)
    (hSCT : E8SwapRowCTInput) (hSU : E8SwapRowUniqueInput) (h2 : E8TwoInput) :
    SeitzExclusion (HighExceptional .E8) :=
  seitzExclusion_highE8_of_inputs hGLS hE7Odd hMinn hMcomp (e8FieldNeighbourInput_of_iso hFI)
    e8FieldRowStep3Input_holds hSCT hSU h2

end CFSG.SeitzReduction.E8Pilot
