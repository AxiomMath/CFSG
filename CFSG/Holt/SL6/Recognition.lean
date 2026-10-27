module

public import CFSG.Holt.SL6.Order
public import CFSG.Holt.SL6.Sylow
public import CFSG.Holt.SL6.Transport
public import CFSG.RankThree.PartOne.KLCE.TypeSL
public import CFSG.RankThree.PartOne.MB3.LnSevenFinal
public import CFSG.LocalAnalysis.StandardType.FS81.E7RecogPieces

public section

namespace CFSG.Holt.SL6

open scoped MatrixGroups
open CFSG.StandardType.FrameRoute.FS81

theorem eq_top_of_transvection_centralizer_le_of_holt (hHolt : HoltSimpleControl)
    {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (φ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) {z : X} (hzL : z ∈ L)
    (hz : φ ⟨z, hzL⟩ = stdTransvection) (hC : Subgroup.centralizer {z} ≤ L)
    (hfus : ∀ x : X, x * z * x⁻¹ ∈ L → ∃ l ∈ L, x * z * x⁻¹ = l * z * l⁻¹) : L = ⊤ := by
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) :=
    CFSG.RankThree.PartOne.MB3.isSimpleGroup_sl_two (m := 6) (by norm_num)
  have : IsSimpleGroup ↥L := φ.isSimpleGroup
  obtain ⟨P, hzP, hPc⟩ := exists_sylow_central_stdTransvection
  obtain ⟨S, hS, hmem⟩ := exists_isSylow2In_of_mulEquiv φ P
  have hzS : z ∈ S := (hmem ⟨z, hzL⟩).mp (by rw [hz]; exact hzP)
  refine hHolt X L S z inferInstance ?_ ?_ hS hzS ?_ ?_ fun g hg =>
    CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.mem_of_conj_mem_of_centralizer_le L hC hfus hg
  · obtain ⟨a, c, hac⟩ : ∃ a c : SL(6, ZMod 2), a * c ≠ c * a :=
      ⟨_, _, CFSG.RankThree.PartOne.KLCE.transvection_noncomm (m := 4) (K' := ZMod 2)⟩
    refine ⟨φ.symm a, φ.symm c, fun h => hac ?_⟩
    simpa using congrArg φ h
  · intro m hm
    rw [Nat.card_congr φ.toEquiv]
    exact two_mul_card_ne_factorial hm
  · have h1 : orderOf (⟨z, hzL⟩ : ↥L) = 2 := by
      rw [← MulEquiv.orderOf_eq φ, hz]
      exact CFSG.RankThree.PartOne.KLCE.orderOf_transvection_one (m := 4) (K' := ZMod 2)
        (i := 0) (j := 5) (by decide)
    simpa using h1
  · intro s hs
    have hsL : s ∈ L := hS.1 hs
    have h1 := hPc (φ ⟨s, hsL⟩) ((hmem ⟨s, hsL⟩).mpr hs)
    rw [← hz, ← map_mul, ← map_mul] at h1
    exact congrArg Subtype.val (φ.injective h1)

theorem eq_top_of_isConj_transvection_centralizer_le_of_holt (hHolt : HoltSimpleControl)
    {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (φ : ↥L ≃* Matrix.SpecialLinearGroup (Fin 6) (ZMod 2)) {z : X} (hzL : z ∈ L)
    (hz : IsConj stdTransvection (φ ⟨z, hzL⟩)) (hC : Subgroup.centralizer {z} ≤ L)
    (hfus : ∀ x : X, x * z * x⁻¹ ∈ L → ∃ l ∈ L, x * z * x⁻¹ = l * z * l⁻¹) : L = ⊤ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hz
  refine eq_top_of_transvection_centralizer_le_of_holt hHolt (φ.trans (MulAut.conj c⁻¹)) hzL ?_
    hC hfus
  rw [MulEquiv.trans_apply, MulAut.conj_apply, ← hc]
  group

end CFSG.Holt.SL6
