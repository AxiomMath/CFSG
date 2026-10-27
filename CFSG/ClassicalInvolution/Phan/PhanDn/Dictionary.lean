module

public import CFSG.ClassicalInvolution.Phan.PhanDn.PanelParab
public import CFSG.LocalAnalysis.StandardType.PhanEBridgeGeom

public section

namespace CFSG.ClassicalInvolution.PhanDn

open CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary
open CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Phan.PhanE
open CFSG.Monster.B.Geometry
open QuadraticMap

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2] {f : ℕ}
  (E : QuadExt F K (unitaryInvolution K 2 f)) {m : ℕ}

abbrev DΩ (m : ℕ) : Type :=
  ↥(CFSG.RankThree.Classical2.orthDerived (Qn E (m + 1)))

noncomputable def dictEquiv {M : CoxeterMatrix (Fin (m + 1))} (hm : 3 ≤ m)
    (S : PhanFamilyE K 2 f M (DΩ E m))
    (hS : IsStdDFamily E hm S) :
    (DΩ E m) ⧸ S.torus ≃
      DChamber (unitaryInvolution K 2 f) (m + 1) :=
  (Subgroup.quotientEquivOfEq
    (hS.torus_eq.trans (stabilizer_stdDChamber E).symm)).trans
    (Equiv.ofBijective
      (MulAction.ofQuotientStabilizer
        (DΩ E m)
        (stdDChamber (unitaryInvolution K 2 f) (m + 1)))
      (show Function.Bijective _ from
        ⟨MulAction.injective_ofQuotientStabilizer _ _,
          fun c => by
            obtain ⟨g, rfl⟩ := exists_smul_stdDChamber E (by omega : 4 ≤ m + 1) c
            exact ⟨(g : (DΩ E m) ⧸ _), MulAction.ofQuotientStabilizer_mk _ _ _⟩⟩))

theorem dictEquiv_mk {M : CoxeterMatrix (Fin (m + 1))} (hm : 3 ≤ m)
    (S : PhanFamilyE K 2 f M (DΩ E m))
    (hS : IsStdDFamily E hm S)
    (g : DΩ E m) :
    dictEquiv E hm S hS (g : (DΩ E m) ⧸ S.torus) =
      g • stdDChamber (unitaryInvolution K 2 f) (m + 1) := by
  have h : (Subgroup.quotientEquivOfEq
      (hS.torus_eq.trans (stabilizer_stdDChamber E).symm))
      (g : (DΩ E m) ⧸ S.torus) =
      (g : (DΩ E m) ⧸
        MulAction.stabilizer (DΩ E m)
          (stdDChamber (unitaryInvolution K 2 f) (m + 1))) :=
    Subgroup.quotientEquivOfEq_mk _ _
  unfold dictEquiv
  rw [Equiv.trans_apply, h, Equiv.ofBijective_apply]
  exact MulAction.ofQuotientStabilizer_mk _ _ _

theorem dictEquiv_adj_iff {M : CoxeterMatrix (Fin (m + 1))} (hm : 3 ≤ m)
    (S : PhanFamilyE K 2 f M (DΩ E m))
    (hS : IsStdDFamily E hm S) (i : Fin (m + 1))
    (x y : (DΩ E m) ⧸ S.torus) :
    (phanSystemE S).adj i x y ↔
      (dChamberSystem (unitaryInvolution K 2 f) m).adj i
        (dictEquiv E hm S hS x) (dictEquiv E hm S hS y) := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  rw [phanSystemE_adj_mk, dictEquiv_mk, dictEquiv_mk]
  rw [show (dChamberSystem (unitaryInvolution K 2 f) m).adj i
        (a • stdDChamber (unitaryInvolution K 2 f) (m + 1))
        (b • stdDChamber (unitaryInvolution K 2 f) (m + 1)) ↔
      (dChamberSystem (unitaryInvolution K 2 f) m).adj i
        (stdDChamber (unitaryInvolution K 2 f) (m + 1))
        ((a⁻¹ * b) • stdDChamber (unitaryInvolution K 2 f) (m + 1)) from by
    rw [← dChamberSystem_adj_smul_iff E m a⁻¹ i
      (a • stdDChamber (unitaryInvolution K 2 f) (m + 1))
      (b • stdDChamber (unitaryInvolution K 2 f) (m + 1))]
    simp only [inv_smul_smul, mul_smul]]
  exact Iff.intro (fun h => ChamberSystem.adj_symm
      ((adj_smul_stdDChamber_iff (E := E) (S := S) hm hS i (a⁻¹ * b)).mpr h))
    (fun h => (adj_smul_stdDChamber_iff (E := E) (S := S) hm hS i (a⁻¹ * b)).mp
      (ChamberSystem.adj_symm h))

theorem connected_phanSystemE {M : CoxeterMatrix (Fin (m + 1))} (hm : 3 ≤ m)
    (S : PhanFamilyE K 2 f M (DΩ E m))
    (hS : IsStdDFamily E hm S) :
    (dChamberSystem (unitaryInvolution K 2 f) m).Connected →
      (phanSystemE S).Connected :=
  connected_of_equiv (dictEquiv E hm S hS)
    (fun i x y => dictEquiv_adj_iff E hm S hS i x y)

theorem simplyTwoConnected_phanSystemE {M : CoxeterMatrix (Fin (m + 1))} (hm : 3 ≤ m)
    (S : PhanFamilyE K 2 f M (DΩ E m))
    (hS : IsStdDFamily E hm S) :
    (dChamberSystem (unitaryInvolution K 2 f) m).SimplyTwoConnected →
      (phanSystemE S).SimplyTwoConnected :=
  simplyTwoConnected_of_equiv (dictEquiv E hm S hS)
    (fun i x y => dictEquiv_adj_iff E hm S hS i x y)

theorem isUniversal_stdFamilyΩ_of_dChamberSystem (hm : 3 ≤ m)
    (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (hgood : (stdFamilyΩ E m hm hK hq).Good)
    (hconn : (dChamberSystem (unitaryInvolution K 2 f) m).Connected)
    (hsc : (dChamberSystem (unitaryInvolution K 2 f) m).SimplyTwoConnected) :
    (stdFamilyΩ E m hm hK hq).IsUniversal := by
  let S := stdFamilyΩ E m hm hK hq
  have hS : IsStdDFamily E hm S := isStdDFamily_stdFamilyΩ E hm hK hq
  refine universal_of_geometryE hK hq S hgood ?_ ?_
  · exact connected_phanSystemE E hm S hS hconn
  · exact simplyTwoConnected_phanSystemE E hm S hS hsc

end CFSG.ClassicalInvolution.PhanDn

end
