module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OConj
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6A5
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6D4
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Iso
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotLayer
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.T173
open CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType CFSG.StandardType.TableBExc.E6Three CFSG.StandardType.E6TwoPilot
open CFSG.StandardType.E6ThreeEnd CFSG.StandardType.SmallExc
open scoped MatrixGroups


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem range_torusE6Two_le_sup_stdLayer_e0 (h2 : (2 : K) = 0) (hK : Nat.card K = 2) :
    (torusE6Two (K := K) h2).range ≤ Subgroup.zpowers (torusE6Two h2 (.ofAdd e0E6)) ⊔
      stdLayer (torusE6Two (K := K) h2 (.ofAdd e0E6)) := by
  have hu0 : torusE6Two h2 (.ofAdd e0E6) = uE6Two (K := K) 0 := by
    change torusE6Two h2 (.ofAdd (Pi.single 0 (1 : ZMod 3))) = uE6Two (K := K) 0
    rw [torusE6Two_single_eq_pow, ZMod.val_one, pow_one]
  have hstd : stdLayer (torusE6Two (K := K) h2 (.ofAdd e0E6)) = leviB0 K := by
    rw [hu0]
    exact (CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer _).symm.trans
      (largeEvenLayer_centralizer_uE6Two_zero hK).1
  rintro _ ⟨w, rfl⟩
  set v := Multiplicative.toAdd w with hv
  have hdecomp : w = .ofAdd (Pi.single 0 (v 0)) * .ofAdd (v - Pi.single 0 (v 0)) := by
    rw [← ofAdd_add, add_sub_cancel, ofAdd_toAdd]
  rw [hdecomp, map_mul]
  refine Subgroup.mul_mem_sup ?_ ?_
  · rw [torusE6Two_single_eq_pow, hu0]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(v 0).val, by rw [zpow_natCast]⟩
  · rw [hstd]
    exact torusE6Two_mem_leviB0 h2 (by simp)

private theorem map_ker_coordD4_le_largeEvenLayer (h2 : (2 : K) = 0) (hK : Nat.card K = 2) :
    E6Node.coordD4.ker.map (torusE6Two (K := K) h2) ≤
      CFSG.Assembly.LargeEvenLayer (Subgroup.centralizer
        ({torusE6Two h2 (.ofAdd d2E6)} : Set (adjointGroup .E6 K))) := by
  obtain ⟨-, l, hl, -⟩ := E6Node.exists_inv_mul_map_uvSL_mul_eq_HSL hK
  have hx := TableBExcTwoFusion.sq_add_self_add_one_eq_zero hl
  obtain ⟨ha, hv⟩ := E6Node.liftConj_nD4_torusE6Two h2 hl (P := TableBExcTwoFusion.langP hx) (by
    rw [TableBExcTwoFusion.map_uSL_mul_vSL, mul_assoc, ← TableBExcTwoFusion.langP_mul_HSL hx,
      inv_mul_cancel_left])
  have hQC : (rootSpan .E6 _ (rootCharKernel (E6Node.chiD4 l))).comap
      (E6Node.liftConj (E6Node.nD4 (TableBExcTwoFusion.langP hx))) ≤
        Subgroup.centralizer {torusE6Two h2 (.ofAdd d2E6)} := fun c hc => by
    have h := (mem_toralCentralizer.1
      (rootSpan_rootCharKernel_le_toralCentralizer _ (Subgroup.mem_comap.1 hc))).2
    rw [← ha, ← map_inv, ← map_mul, ← map_mul] at h
    exact Subgroup.mem_centralizer_singleton_iff.2
      (mul_inv_eq_iff_eq_mul.1 (E6Node.liftConj_injective _ h)).symm
  have hQE := le_largeEvenLayer ⟨hQC, CFSG.Assembly.IsSubnormal.step hQC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQC).2 (E6Node.centralizer_le_normalizer_comap
      (E6Node.nD4_mem _) ha (toralCentralizer_le_normalizer_rootSpan _)))
    (CFSG.Assembly.IsSubnormal.refl _), E6Node.isQuasisimple_comap_liftConj_nD4 hK hx hl⟩
  intro x hx'
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hx'
  exact hQE (hv _ ((E6Node.mem_ker_coordD4 w).1 hw))

private theorem map_ker_coordD4_le_stdLayer (h2 : (2 : K) = 0) (hK : Nat.card K = 2) :
    E6Node.coordD4.ker.map (torusE6Two (K := K) h2) ≤
      stdLayer (torusE6Two (K := K) h2 (.ofAdd d2E6)) :=
  (map_ker_coordD4_le_largeEvenLayer h2 hK).trans
    (CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer _).le

private theorem coordD4_sub_smul_d2E6 : ∀ v : Fin 4 → ZMod 3,
    (v - (2 * (v 0 + v 1)) • d2E6) 0 + (v - (2 * (v 0 + v 1)) • d2E6) 1 = 0 := by
  decide +kernel

theorem range_torusE6Two_le_sup_stdLayer_d2 (h2 : (2 : K) = 0) (hK : Nat.card K = 2) :
    (torusE6Two (K := K) h2).range ≤ Subgroup.zpowers (torusE6Two h2 (.ofAdd d2E6)) ⊔
      stdLayer (torusE6Two (K := K) h2 (.ofAdd d2E6)) := by
  have hker := map_ker_coordD4_le_stdLayer h2 hK
  rintro _ ⟨w, rfl⟩
  set v := Multiplicative.toAdd w with hv
  have hdecomp : w = .ofAdd ((2 * (v 0 + v 1)) • d2E6) *
      .ofAdd (v - (2 * (v 0 + v 1)) • d2E6) := by
    rw [← ofAdd_add, add_sub_cancel, ofAdd_toAdd]
  rw [hdecomp, map_mul]
  refine Subgroup.mul_mem_sup ?_ ?_
  · have hc : (2 * (v 0 + v 1)) • d2E6 = (2 * (v 0 + v 1)).val • d2E6 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod 3) (2 * (v 0 + v 1)).val d2E6,
        ZMod.natCast_zmod_val]
    rw [hc, torusE6Two_nsmul]
    exact Subgroup.mem_zpowers_iff.mpr ⟨(2 * (v 0 + v 1)).val, by rw [zpow_natCast]⟩
  · exact hker (Subgroup.mem_map_of_mem _ ((E6Node.mem_ker_coordD4 _).2
      (coordD4_sub_smul_d2E6 v)))

theorem not_isStdElt_torusE6Two_d0 (h2 : (2 : K) = 0) (hK : Nat.card K = 2) :
    ¬ IsStdElt 3 (torusE6Two (K := K) h2).range (torusE6Two h2 (.ofAdd d0E6)) := by
  intro hd
  have hstd : stdLayer (torusE6Two (K := K) h2 (.ofAdd d0E6)) =
      CFSG.Assembly.LargeEvenLayer (Subgroup.centralizer
        ({torusE6Two h2 (.ofAdd d0E6)} : Set (adjointGroup .E6 K))) :=
    (CFSG.Assembly.LargeEven.largeEvenLayer_eq_glaLayer _).symm
  refine (E6Node.ggE6TwoIsoNodeInput_holds K h2 hK) ⟨?_, ?_⟩
  · rw [← hstd]
    exact CFSG.Assembly.isComponentOf_iff_open.2 hd.2.2.2.1
  · intro s hs
    have h := hd.2.2.2.2
    rw [hstd] at h
    have hmem : s ∈ Subgroup.centralizer (CFSG.Assembly.LargeEvenLayer (Subgroup.centralizer
        ({torusE6Two h2 (.ofAdd d0E6)} : Set (adjointGroup .E6 K))) : Set _) ↔
        s ∈ Subgroup.zpowers (torusE6Two h2 (.ofAdd d0E6)) := by
      rw [← h]
      exact ⟨fun hc => ⟨hs, hc⟩, fun hc => hc.2⟩
    rw [← hmem, Subgroup.mem_centralizer_iff]
    exact ⟨fun h' j hj => (h' j hj).symm, fun h' j hj => (h' j hj).symm⟩

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
