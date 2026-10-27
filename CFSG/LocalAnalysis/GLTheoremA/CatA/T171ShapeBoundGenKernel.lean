module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundGenBase
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeThree
public import CFSG.Adapters.StatedSLPerfect
public import CFSG.RankThree.PartOne.FOC.PSLDecomp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnLinCore
public import CFSG.Assembly.GL83StatedBridge
import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBase2
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GField
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GU64Pieces
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011U64Types

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.S15K

variable {N n p : ℕ} {K : Type} [Field K]

theorem commute_of_projConj_eq_one {d : ℕ} {H : Subgroup (GL (Fin d) K)}
    (hperf : Group.IsPerfect ↥H)
    (hker : (LargeEvenProjMk H).ker ≤ Subgroup.center ↥H)
    (X : Subgroup.normalizer (H : Set (GL (Fin d) K)))
    (hX : TableB.projConj H X = 1) :
    ∀ g ∈ H, (X : GL (Fin d) K) * g = g * (X : GL (Fin d) K) := by
  have key := eq_of_perfect_of_map_eq (LargeEvenProjMk H) hker hperf
    ((H.normalizerMonoidHom X).toMonoidHom) (MonoidHom.id H) (fun u => by
      have h1 := congrArg (fun ψ : MulAut (LargeEvenProj H) =>
        ψ (LargeEvenProjMk H u)) hX
      exact h1)
  intro g hg
  have h2 := congrArg Subtype.val (key ⟨g, hg⟩)
  change (X : GL (Fin d) K) * g * (X : GL (Fin d) K)⁻¹ = g at h2
  calc (X : GL (Fin d) K) * g = (X : GL (Fin d) K) * g * (X : GL (Fin d) K)⁻¹ *
        (X : GL (Fin d) K) := by group
    _ = g * (X : GL (Fin d) K) := by rw [h2]

theorem linKernelScalar_of_three_le [Finite K] (hN : 3 ≤ N)
    (X : Subgroup.normalizer (LargeEvenSLGroup (Fin N) K : Set (GL (Fin N) K)))
    (hX : TableB.projConj (LargeEvenSLGroup (Fin N) K) X = 1) :
    (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K := by
  have hperf : Group.IsPerfect ↥(LargeEvenSLGroup (Fin N) K) := by
    let e := MulEquiv.subgroupCongr (largeEvenSLGroup_eq_statedSL (K := K) N)
    haveI : Group.IsPerfect ↥(StatedSL N K) :=
      CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le hN K
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hker : (LargeEvenProjMk (LargeEvenSLGroup (Fin N) K)).ker ≤
      Subgroup.center ↥(LargeEvenSLGroup (Fin N) K) := by
    rw [largeEvenSLGroup_eq_statedSL]
    exact CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ker_projMk_le_center
  have hcomm := commute_of_projConj_eq_one hperf hker X hX
  have hcenter : (X : GL (Fin N) K) ∈ Subgroup.center (GL (Fin N) K) :=
    CFSG.RankThree.PartOne.FOC.mem_center_of_commute_SL (X : GL (Fin N) K) fun s => by
      have hmem : Matrix.SpecialLinearGroup.toGL s ∈ LargeEvenSLGroup (Fin N) K := by
        rw [largeEvenSLGroup_eq_statedSL, CFSG.Open.StatedAPI.mem_statedSL_iff]
        exact s.2
      exact (hcomm _ hmem).symm
  rw [largeEvenScalars_def, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact hcenter

theorem uniKernelScalar (h : UnitaryFieldData 2 n K) (hN : 3 ≤ N)
    (hNq : (N, 2 ^ n) ≠ (3, 2)) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1)
    (X : Subgroup.normalizer (LargeEvenSUGroup (Fin N) K (2 ^ n) : Set (GL (Fin N) K)))
    (hX : TableB.projConj (LargeEvenSUGroup (Fin N) K (2 ^ n)) X = 1) :
    (X : GL (Fin N) K) ∈ LargeEvenScalars (Fin N) K := by
  have hcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, Nat.mul_comm 2 n, ← pow_mul]
  haveI := h.finite
  exact TableBUE.mem_scalars_of_projConj_eq_one h hcard hN hNq hp hpq hX

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
