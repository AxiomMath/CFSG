module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.SporAltSporGen
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporCo1ThreeRows

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier
  CFSG.Open CFSG.Blueprint CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.LieType.Multipliers.U43 CFSG.LocalAnalysis.GLTheoremA.SporAltRows

@[expose] def Co1ThreeOrd (T : Type) [Group T] : Prop :=
  Nat.card T = 3265920 ∨ Nat.card T = 181440 ∨ Nat.card T = 448345497600

theorem co1ThreeOrd_of_equiv (T T' : Type) [Group T] [Group T'] (e : T ≃* T')
    (h : Co1ThreeOrd T) : Co1ThreeOrd T' := by
  unfold Co1ThreeOrd at h ⊢
  rwa [← Nat.card_congr e.toEquiv]

theorem grow_Co1_three (hOut : SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    GRow Co1ThreeOrd .Co1 3 := by
  obtain ⟨hfin, hs, hnc, ⟨b⟩⟩ := co1_model_five hbr
  have hC := tabCo1_centShapeRk_three_good (Good := Co1ThreeOrd) co1ThreeOrd_of_equiv
    (fun _ _ e => Or.inl ((Nat.card_congr e.toEquiv).trans card_X₀))
    (Or.inr (Or.inl card_alt_nine)) (fun _ _ hc _ => Or.inr (Or.inr hc)) (hbr .Suz)
  exact @grow_of_model Co1ThreeOrd co1ThreeOrd_of_equiv .Co1 3 ↥GA _ hfin hs hOut b hnc
    fun _ hk => compGood_of_centShape Nat.prime_three (CentShape.of_centShapeRk hC) hk

end CFSG.HardMathSupport.Dickson.I271.TabCo1

namespace CFSG.LocalAnalysis.GLTheoremA.SporAltRows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem grow_He_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) :
    GRow (fun T _ => Nat.card T ∣ 2520) .He 3 := by
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥CFSG.Sporadic.HeldB.heP :=
    CFSG.Sporadic.HeldB.heEquivP
  have hs : IsSimpleGroup ↥CFSG.Sporadic.HeldB.heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  refine grow_of_model (fun _ _ _ _ e h => (Nat.card_congr e.toEquiv).symm ▸ h) hOut
    (e.symm.trans (hbr .He).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (by rw [CFSG.Sporadic.HeldB.card_heP]; norm_num))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin 8330)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  refine compGood_dvd_of_card_dvd Nat.prime_three hx ?_
  have hcc : Nat.card (Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.HeldB.heP)) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) ⊓
        CFSG.Sporadic.HeldB.heP) := by
    rw [← map_centralizer_subtype CFSG.Sporadic.HeldB.heP x,
      Subgroup.card_map_of_injective CFSG.Sporadic.HeldB.heP.subtype_injective]
  rw [hcc]
  rcases he3_card x.2 hx3 with h | h <;> rw [h] <;> norm_num

end CFSG.LocalAnalysis.GLTheoremA.SporAltRows
