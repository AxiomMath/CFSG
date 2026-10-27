module

public import CFSG.LocalAnalysis.RankThreeUC.GN15JOutOffender
public import CFSG.LocalAnalysis.RankThreeUC.GN15Solv
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.GN
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped commutatorElement

@[expose] def OutDerivedOdd : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (T : Subgroup X), GNSetting X T →
    ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥ →
      Odd (Nat.card (commutator (Outer ↥L)))

theorem jOutCentralAt_of_offender (hS : FFOffenderInvertsOdd) {X : Type} [Group X] [Finite X]
    {T : Subgroup X} (hX : GNSetting X T)
    (hOdd : ∀ L : Subgroup (X ⧸ gnC T), IsComponentOf L ⊤ → ⁅L, gnImg T (thompsonJ T)⁆ ≠ ⊥ →
      Odd (Nat.card (commutator (Outer ↥L)))) : JOutCentralAt T := by
  intro L hL hne _ w hw j hj
  classical
  have hV : IsElemAbelian 2 (gnV T) := isElemAbelian_gnV T hX
  let _ : Module (ZMod 2) (Additive (IntMod (gnV T) hV)) :=
    binModule (fun v : IntMod (gnV T) hV => IntMod.sq_eq_one v)
  have hinj : Function.Injective (gnRep hV) := gnRep_injective hV
  have hC : CFSG.IsComponent L := (isComponent_iff_open L).2 hL
  have hQ : CFSG.IsQuasisimple L := hC.1
  have hnorm : ∀ A : Subgroup X, IsMaxElemAbelian T A →
      A.map (QuotientGroup.mk' (gnC T)) ≤ Subgroup.normalizer (L : Set (X ⧸ gnC T)) := fun A hA =>
    (le_bestOffenderSub (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep hV hX hA)).trans
      (bestOffenderSub_le_normalizer_component (gnRep hV) hinj hC)
  have hJle : gnImg T (thompsonJ T) ≤ JOut.commutesModInner L w := by
    unfold gnImg thompsonJ
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    by_cases hb : ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ = ⊥
    · intro j hj'
      have hjc : j ∈ Subgroup.centralizer (L : Set (X ⧸ gnC T)) := by
        intro l hl
        have : ⁅l, j⁆ ∈ ⁅L, A.map (QuotientGroup.mk' (gnC T))⁆ :=
          Subgroup.commutator_mem_commutator hl hj'
        rw [hb, Subgroup.mem_bot] at this
        exact commutatorElement_eq_one_iff_mul_comm.1 this
      exact JOut.sup_centralizer_le_commutesModInner hw (Subgroup.mem_sup_right hjc)
    · have hLA := commutator_eq_of_ne_bot hQ (hnorm A hA) hb
      intro j hj'
      exact ⟨hnorm A hA hj', commutator_mem_of_offender hS hinj (isKGroup_gnQuot hX)
        (pCore_two_gnQuot hX) (isElementaryAbelian_map_mk hA) (isBestOffender_gnRep hV hX hA) hL
        (hnorm A hA) hLA (hOdd L hL hne) hw hj'⟩
  exact (hJle hj).2

theorem jOutCentral_of_offender (hS : FFOffenderInvertsOdd) (hOdd : OutDerivedOdd) :
    JOutCentral :=
  fun X _ _ T hX => jOutCentralAt_of_offender hS hX (hOdd X T hX)

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
