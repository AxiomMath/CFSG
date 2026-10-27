module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeU6Type9Shape
import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
import CFSG.CharacterTheory.Wreathed.BrauerWongTypes
import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
import CFSG.Dihedral.DihedralFusionPrefixes
import CFSG.HardMathSupport.Solomon.LocalBalance.ScpQuot
import CFSG.LocalAnalysis.ComponentClassification.BlockCentralSylowEquality
import CFSG.LocalAnalysis.ComponentClassification.BlockFourFactorSupport
import CFSG.LocalAnalysis.ComponentClassification.BlockLargeProductInvolutions
import CFSG.LocalAnalysis.ComponentClassification.BlockMovedFactorSylowCentral
import CFSG.LocalAnalysis.ComponentClassification.BlockNormalizerOrder
import CFSG.LocalAnalysis.ComponentClassification.BlockPermutationSylowLifting
import CFSG.LocalAnalysis.ComponentClassification.BlockStrictFullSylowAbelian
import CFSG.LocalAnalysis.ComponentClassification.KProper
import CFSG.LocalAnalysis.ComponentClassification.LabeledBlockPermutation
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.ComponentInitial.PerfectOuterInjection
import CFSG.LocalAnalysis.GLTheoremA.S10.Bridge
import CFSG.LocalAnalysis.GLTheoremA.S11.Defs
import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs
import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
import CFSG.LocalAnalysis.SignalizerFunctor
import CFSG.Quasithin.Background.A3ComponentsAmbient

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel

@[expose] def U6Type9Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L J A : Subgroup G) (d b : G) (n : ℕ) (K : Type)
    [Field K] [Finite K] (h : UnitaryFieldData 2 n K)
    (θ : ↥L ⧸ Subgroup.center ↥L ≃* LargeEvenProj (unitarySU 2 n K 6)),
    Setup 3 L J A d b → 3 ∣ 2 ^ n + 1 →
    (∀ a ∈ A, ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)),
      LargeEvenInduces θ (fun l l' => (l' : G) = a⁻¹ * l * a) φ) →
    ∀ (M : GL (Fin 6) K) (_ : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n))
      (hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K))),
      M ^ 3 = 1 →
      LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
        (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) → False

theorem u6Type9_of_core (hcore : U6Type9Core) : U6Type9 := by
  intro G _ _ L J A d b n K _ _ h θ hS hpq hA φ hφ
  classical
  haveI : Finite K := h.finite
  have hdA : d ∈ A := hS.d_mem
  have hd3 : d ^ 3 = 1 := pow_eq_one_of_mem_isElemAbelian hS.elem hdA
  have hdN : d ∈ Subgroup.normalizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag hdA
  have hconjmem : ∀ y : G, y ∈ L → d⁻¹ * y * d ∈ L := by
    intro y hy
    have hd' : d⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hdN
    simpa using (Subgroup.mem_normalizer_iff.1 hd' y).1 hy
  let cd : L → L := fun x => ⟨d⁻¹ * (x : G) * d, hconjmem _ x.2⟩
  have hex : ∀ l : L, ∃ l' : L, (l' : G) = d⁻¹ * l * d := fun l => ⟨cd l, rfl⟩
  obtain ⟨φd, hφd_mem, hφd_ind⟩ := hA d hdA
  have hφeq : φ = φd := largeEvenInduces_unique hφ hφd_ind hex
  subst φ
  have hφd3 : φd ^ 3 = 1 := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hstep : ∀ y : L, φd (θ (QuotientGroup.mk y)) =
        θ (QuotientGroup.mk (cd y)) := fun y => hφd_ind y (cd y) rfl
    have hstep3 : (φd ^ 3) (θ (QuotientGroup.mk x)) =
        θ (QuotientGroup.mk (cd (cd (cd x)))) := by
      change φd (φd (φd (θ (QuotientGroup.mk x)))) = _
      rw [hstep, hstep, hstep]
    have hcd3 : cd (cd (cd x)) = x := by
      apply Subtype.ext
      show d⁻¹ * (d⁻¹ * (d⁻¹ * (x : G) * d) * d) * d = (x : G)
      have hd3mul : d * d * d = 1 := by
        simpa [pow_succ, mul_assoc] using hd3
      have hdinv : d⁻¹ * d⁻¹ * d⁻¹ = 1 := by
        simpa [mul_inv_rev, mul_assoc] using congrArg Inv.inv hd3mul
      calc d⁻¹ * (d⁻¹ * (d⁻¹ * (x : G) * d) * d) * d
          = (d⁻¹ * d⁻¹ * d⁻¹) * (x : G) * (d * d * d) := by group
        _ = (x : G) := by rw [hdinv, hd3mul]; group
    rw [hstep3, hcd3]
    rfl
  obtain ⟨M, hMgu, hφd_eq⟩ :=
    TableB.exists_eq_projConj (TableBUE.gu_subset_normalizer h) hφd_mem
  have hMN : M ∈ Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
    TableBUE.gu_subset_normalizer h hMgu
  have hbase : TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩ = φd := hφd_eq.symm
  have hM3proj : TableB.projConj (unitarySU 2 n K 6) ⟨M ^ 3, by
      exact Subgroup.pow_mem _ hMN 3⟩ = 1 := by
    have hpow : TableB.projConj (unitarySU 2 n K 6) ⟨M ^ 3, by
        exact Subgroup.pow_mem _ hMN 3⟩ =
        (TableB.projConj (unitarySU 2 n K 6) ⟨M, hMN⟩) ^ 3 := by
      rw [← map_pow]
      congr 1
    rw [hpow, hbase, hφd3]
  have hKcard : Nat.card K = (2 ^ n) ^ 2 := by
    rw [h.card, ← pow_mul, mul_comm]
  obtain ⟨l, hl⟩ := TableBUE.mem_scalars_of_projConj_eq_one h hKcard (by norm_num)
    (by norm_num) Nat.prime_three hpq hM3proj
  have hl' : M ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) l := by
    simpa using hl.symm
  by_cases hcube : ∃ c : Kˣ, c ^ 3 = l
  · obtain ⟨c, hc⟩ := hcube
    obtain ⟨M', hM'gu, hM'N, hM'3, -, hproj_eq⟩ :=
      exists_unitary_rescale h hpq hMgu hMN hl' hc
    have hφ' : LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
        (TableB.projConj (unitarySU 2 n K 6) ⟨M', hM'N⟩) := by
      rw [← hproj_eq, hbase]
      exact hφd_ind
    exfalso
    exact hcore G L J A d b n K h θ hS hpq hA M' hM'gu hM'N hM'3 hφ'
  · rw [← hbase]
    refine fieldType_of_gu_pow_three_eq_scalar_not_cube h hMgu hMN hl' ?_
    intro c hc
    exact hcube ⟨c, hc⟩

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
