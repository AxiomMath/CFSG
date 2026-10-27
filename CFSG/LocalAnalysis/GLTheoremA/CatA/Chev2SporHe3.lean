module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Chev2SporRows
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I1416SporTh7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I1416Rows

theorem ccompOK_three_of_card_dvd_7560
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) {Q : Type} [Group Q]
    [Finite Q] {k : Q} (hk3 : orderOf k = 3)
    (hk : Nat.card (Subgroup.centralizer ({k} : Set Q)) ∣ 7560) : CCompOK 3 k := by
  intro I hI
  obtain ⟨hs, hnab⟩ := KDSpor.pSimple_simple_nonab Nat.prime_three hI
  haveI := hs
  have h3 : 3 * Nat.card (PSimple 3 I) ∣ 7560 :=
    (prime_mul_card_pSimple_dvd_cent Nat.prime_three hk3 hI.1).trans hk
  exact ctypeOK_three_of_card_dvd_2520 hb hnab
    (Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 3) (h3.trans (by norm_num)))

open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.Coordinator.B3S3 in
theorem crow_He_three
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges)
    (hb : CFSG.HardMathSupport.Solomon.Coordinator.LieOrderBridge) :
    CRow .He 3 := by
  have e : CFSG.Blueprint.NativeSporadic.He ≃* ↥CFSG.Sporadic.HeldB.heP :=
    CFSG.Sporadic.HeldB.heEquivP
  have hs : IsSimpleGroup ↥CFSG.Sporadic.HeldB.heP :=
    @MulEquiv.isSimpleGroup _ _ _ _ CFSG.Sporadic.He.isSimpleGroup_He e.symm
  refine crow_of_model hOut (e.symm.trans (hbr .He).some)
    (CFSG.LocalAnalysis.GLTheoremA.S8.HNRows.exists_noncomm_of_simple
      (by rw [CFSG.Sporadic.HeldB.card_heP]; norm_num))
    fun x hx => ?_
  have hx3 : orderOf (x : Equiv.Perm (Fin 8330)) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  refine ccompOK_three_of_card_dvd_7560 hb hx ?_
  have hcc : Nat.card (Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.HeldB.heP)) =
      Nat.card ↥(Subgroup.centralizer ({(x : Equiv.Perm (Fin 8330))} : Set (Equiv.Perm (Fin 8330))) ⊓
        CFSG.Sporadic.HeldB.heP) := by
    rw [← map_centralizer_subtype CFSG.Sporadic.HeldB.heP x,
      Subgroup.card_map_of_injective CFSG.Sporadic.HeldB.heP.subtype_injective]
  rw [hcc]
  rcases he3_card x.2 hx3 with h | h <;> rw [h] <;> norm_num

end CFSG.LocalAnalysis.GLTheoremA.Chev2Rows

