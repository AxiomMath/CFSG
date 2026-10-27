module

public import CFSG.ClassicalInvolution.ModelFacts.L6CDefs
import CFSG.ClassicalInvolution.ModelFacts.L6CUCore
import CFSG.ClassicalInvolution.ModelFacts.Orth15ChainU
import CFSG.ClassicalInvolution.RouteD.TypeULocal
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBLinearDescentFixedBasis
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import CFSG.ClassicalInvolution.LBalance.Main
import CFSG.ClassicalInvolution.ModelFacts.OddCover
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutAmbient
import CFSG.ClassicalInvolution.Models.LinearFrames
import CFSG.ClassicalInvolution.Models.LinearPairs
import CFSG.ClassicalInvolution.Models.OrthogonalPairs
import CFSG.ClassicalInvolution.Models.Transfer
import CFSG.ClassicalInvolution.Models.UnitaryFrames
import CFSG.ClassicalInvolution.Models.UnitaryPairs
import CFSG.ClassicalInvolution.RouteD.LocalLift
import CFSG.ClassicalInvolution.WeakCT.Main
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingTransport
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.BlockOvergroupDichotomy
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.ModelFacts.L6C

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped MatrixGroups

theorem aut164U4 (p : ℕ) [Fact p.Prime] : Aut164U4 p := by
  intro e hadm h4 Y _ ψ hker hsurj β hβ
  have hf : 1 ≤ e := hadm.2.1
  have he : e ≠ 0 := by omega
  have hp2 : p ≠ 2 := by
    intro hp
    subst hp
    obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h4
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have : 2 ^ (j + 1 + 1) = 4 * 2 ^ j := by ring
      rw [this] at h4
      omega
  have hF : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul p e hf
  have hFp : Nat.card (GaloisField p (2 * e)) = p ^ (2 * e) := by
    rw [hF, ← pow_mul, mul_comm]
  let h : UnitaryFieldData p e (GaloisField p (2 * e)) := ⟨Fact.out, hf, hFp⟩
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  let Φ₀ : Su (GaloisField p (2 * e)) p e 4 ≃* unitarySU p e (GaloisField p (2 * e)) 4 :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hF 4)
  let Φ : (Generic.modelUniv .PSU 4 p e Fact.out).K ≃* unitarySU p e (GaloisField p (2 * e)) 4 :=
    φ.trans Φ₀
  let ψ₀ : unitarySU p e (GaloisField p (2 * e)) 4 →* Y := ψ.comp Φ.symm.toMonoidHom
  have hψ₀ : ∀ x, ψ₀ (Φ x) = ψ x := fun x => by
    show ψ (Φ.symm (Φ x)) = ψ x
    rw [MulEquiv.symm_apply_apply]
  have hsurj₀ : Function.Surjective ψ₀ := by
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨Φ x, by rw [hψ₀, hx]⟩
  have hker₀ : ψ₀.ker ≤ Subgroup.center (unitarySU p e (GaloisField p (2 * e)) 4) := by
    intro z hz
    obtain ⟨x, rfl⟩ := Φ.surjective z
    have hx : x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ₀]
      exact hz
    have hxc := hker hx
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := Φ.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hxc y']
  obtain ⟨k, hord, hfix⟩ := aut164U4_core h hp2 h4 ψ₀ hker₀ hsurj₀ β hβ
  have hn : 2 ≤ 4 := by norm_num
  obtain ⟨kS, hkS⟩ : ∃ kS : Su (GaloisField p (2 * e)) p e 4, kS = Φ₀.symm k := ⟨_, rfl⟩
  let jS := CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU.jSU (GaloisField p (2 * e)) p e
  let Jelt : Su (GaloisField p (2 * e)) p e 4 :=
    blockEmb (GaloisField p (2 * e)) p e 4 2 0 (by omega) jS
  have hJ : Φ₀ Jelt = rotSU4 h := by
    apply Subtype.ext
    apply Units.ext
    show suMat Jelt = ((rotSU4 h : unitarySU p e (GaloisField p (2 * e)) 4) :
      GL (Fin 4) (GaloisField p (2 * e))).val
    rw [suMat_blockEmb, CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU.suMat_jSU,
      blockMat_four_zero, coe_rotSU4]
    ext a b
    fin_cases a <;> fin_cases b <;> simp [coe_rot4]
  have hΦ₀J : Φ₀.symm (rotSU4 h) = Jelt := by
    rw [← hJ]
    exact Φ₀.symm_apply_apply Jelt
  let R₀ : Subgroup (Su (GaloisField p (2 * e)) p e 4) :=
    (rootSU2 (GaloisField p (2 * e)) p e hn).map (MulAut.conj kS).toMonoidHom
  have hR₀ : R₀ ∈ longRootSetU hn := (mem_longRootSetU_iff hn).mpr ⟨kS, rfl⟩
  let R : Subgroup (Generic.modelUniv .PSU 4 p e Fact.out).K := R₀.map φ.symm.toMonoidHom
  have hRR : R.map φ.toMonoidHom = R₀ := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa using hz
    · intro hx
      exact ⟨φ.symm x, ⟨x, hx, rfl⟩, by simp⟩
  have hRf : R ∈ Generic.fundamentalSubgroups .PSU (Generic.modelUniv .PSU 4 p e Fact.out).D :=
    (hφ R).mpr (by rw [hRR]; exact hR₀)
  refine ⟨R, hRf, Φ.symm (k * rotSU4 h * k⁻¹), ?_, hord, hfix⟩
  have hJmem : Jelt ∈ rootSU2 (GaloisField p (2 * e)) p e hn := ⟨jS, rfl⟩
  have hconj : kS * Jelt * kS⁻¹ ∈ R₀ := ⟨Jelt, hJmem, rfl⟩
  refine ⟨kS * Jelt * kS⁻¹, hconj, ?_⟩
  have hΦ₀g : Φ₀.symm (k * rotSU4 h * k⁻¹) = kS * Jelt * kS⁻¹ := by
    rw [map_mul, map_mul, map_inv, hΦ₀J, ← hkS]
  show φ.symm (kS * Jelt * kS⁻¹) = Φ.symm (k * rotSU4 h * k⁻¹)
  rw [MulEquiv.symm_trans_apply, hΦ₀g]

end CFSG.ClassicalInvolution.ModelFacts.L6C
