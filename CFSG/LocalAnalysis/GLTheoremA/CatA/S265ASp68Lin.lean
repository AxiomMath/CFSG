module

public import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265AP2Lin
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Sp6
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBaseChange
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.GroupTheory.PLayer.Bootstrap
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Glue
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166SpBlocks2
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.CatalogInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1313Z
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.GLTheoremB.Prop95Input18
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotFieldNormalizeAutMain
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaPlusEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueRowsGeneration
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotUniqueStep3Basic
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2SmallJ
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotBLiftAniso
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotCatCovers
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotHR7iii
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotWeakCT
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphLinearGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphOmegaGlobal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryEnd
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotGraphUnitaryPower
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Partner
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14PartnerSp
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14Transfer
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotOmegaRowUniqueStep
public import Certificates.Certificate41501

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265A

open CFSG.Open CFSG.LocalAnalysis.GLTheoremA.Y10F CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks
open CFSG.LocalAnalysis.GLTheoremA.Y10F.SpEngine
open CFSG.RankThree.SubgroupLists (spForm spForm_isAlt spForm_nondegenerate)
open CFSG.RankThree.Classical (spEnd spEnd_apply)
open CFSG.ClassicalInvolution.Q3.Q3Z (spMap mat_spMap)
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks Matrix

section Descent

variable {F E : Type} [Field F] [Field E] {n : ℕ}

private theorem mem_ker_spEnd_sub_one (s : StatedSp n F) (v : Fin n ⊕ Fin n → F) :
    v ∈ LinearMap.ker (spEnd s - 1) ↔
      (((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1) *ᵥ v = 0 := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, spEnd_apply, Matrix.sub_mulVec,
    Matrix.one_mulVec]

private theorem natCard_ker_submatrix {L : Type} [Field L]
    (N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) L) :
    Nat.card {x : Fin (n + n) → L // ∀ _ : Unit,
        (N.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) *ᵥ x = 0} =
      Nat.card {v : Fin n ⊕ Fin n → L // N *ᵥ v = 0} := by
  let e : (Fin (n + n) → L) ≃ (Fin n ⊕ Fin n → L) :=
    { toFun := fun x => x ∘ finSumFinEquiv
      invFun := fun v => v ∘ finSumFinEquiv.symm
      left_inv := fun x => funext fun i => by simp
      right_inv := fun v => funext fun i => by simp }
  refine Nat.card_congr (Equiv.subtypeEquiv e fun x => ?_)
  change _ ↔ N *ᵥ (x ∘ finSumFinEquiv) = 0
  rw [Matrix.submatrix_mulVec_equiv, Equiv.symm_symm]
  constructor
  · intro h
    funext i
    simpa using congrFun (h ()) (finSumFinEquiv i)
  · intro h _
    rw [h]
    rfl

private theorem natCard_ker_spEnd (s : StatedSp n F) :
    Nat.card ↥(LinearMap.ker (spEnd s - 1)) =
      Nat.card {v : Fin n ⊕ Fin n → F //
        (((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1) *ᵥ v = 0} :=
  Nat.card_congr (Equiv.subtypeEquivRight (mem_ker_spEnd_sub_one s))

theorem finrank_ker_spEnd_spMap [Finite E] (ι : F →+* E) (s : StatedSp n F) :
    Module.finrank E ↥(LinearMap.ker (spEnd (spMap ι s) - 1)) =
      Module.finrank F ↥(LinearMap.ker (spEnd s - 1)) := by
  have : Finite F := Finite.of_injective ι ι.injective
  obtain ⟨r, hr⟩ : ∃ r, (letI := ι.toAlgebra; Module.finrank F E) = r := ⟨_, rfl⟩
  have hEF : Nat.card E = Nat.card F ^ r := by
    rw [← hr]
    letI := ι.toAlgebra
    haveI : Module.Finite F E := Module.Finite.of_finite
    exact Module.natCard_eq_pow_finrank
  have hr0 : 0 < r := by
    rw [← hr]
    letI := ι.toAlgebra
    haveI : Module.Finite F E := Module.Finite.of_finite
    exact Module.finrank_pos
  have hmat : ((spMap ι s : GL (Fin n ⊕ Fin n) E) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) E) - 1 =
      (((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1).map ι := by
    rw [Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι)]
    exact congrArg (· - 1) (mat_spMap ι s)
  have hbase := CFSG.QuasithinUnique.Setup.SL2Modules.natCard_common_ker_map ι (κ := Unit)
    fun _ => (((s : GL (Fin n ⊕ Fin n) F) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) - 1).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm
  rw [hr, ← Matrix.submatrix_map, natCard_ker_submatrix, natCard_ker_submatrix, ← hmat,
    ← natCard_ker_spEnd, ← natCard_ker_spEnd,
    Module.natCard_eq_pow_finrank (K := E) (V := ↥(LinearMap.ker (spEnd (spMap ι s) - 1))),
    Module.natCard_eq_pow_finrank (K := F) (V := ↥(LinearMap.ker (spEnd s - 1))), hEF,
    ← pow_mul, ← pow_mul] at hbase
  have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
  have h := Nat.pow_right_injective h2 hbase
  rw [mul_comm _ r] at h
  exact Nat.eq_of_mul_eq_mul_left hr0 h

end Descent

theorem eq_one_of_pow_three_eq_one_of_card_eight {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 8) {x : K} (hx : x ^ 3 = 1) : x = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h7 := FiniteField.pow_card_sub_one_eq_one x hx0
  rw [← Nat.card_eq_fintype_card, hK] at h7
  calc x = (x ^ 3) ^ 2 * x := by rw [hx, one_pow, one_mul]
    _ = x ^ (8 - 1) := by ring
    _ = 1 := h7

section Normalized

variable {n : ℕ} {K : Type} [Field K]

private noncomputable def spAct (n : ℕ) (K : Type) [Field K] :
    StatedSp n K →* ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
  (linIsometryGroup (spForm n K)).subtype.comp (statedSpEquivLinIsometryGroup n K).toMonoidHom

private theorem spAct_apply (s : StatedSp n K) (v : Fin n ⊕ Fin n → K) :
    spAct n K s v = spEnd s v := by
  rw [spEnd_apply]
  exact statedSpEquivLinIsometryGroup_apply n K s v

private theorem spAct_injective : Function.Injective (spAct n K) :=
  (linIsometryGroup (spForm n K)).subtype_injective.comp
    (statedSpEquivLinIsometryGroup n K).injective

private theorem spAct_isometry (s : StatedSp n K) (u v : Fin n ⊕ Fin n → K) :
    spForm n K (spAct n K s u) (spAct n K s v) = spForm n K u v :=
  mem_linIsometryGroup.mp (statedSpEquivLinIsometryGroup n K s).2 u v

private theorem fixedByEnd_spAct (s : StatedSp n K) :
    fixedByEnd (spAct n K s) = LinearMap.ker (spEnd s - 1) := by
  ext v
  rw [mem_fixedByEnd, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero,
    spAct_apply]

theorem sp_eq_bot_of_normalized_two_subgroup_of_card_nine [Finite K] [CharP K 2]
    (hF : ∀ x : K, x ^ 3 = 1 → x = 1) {Ab T : Subgroup (StatedSp n K)}
    (hAb : IsElemAbelian 3 Ab) (h9 : Nat.card Ab = 9)
    (hfix : ∀ s ∈ Ab, s ≠ 1 → Module.finrank K (LinearMap.ker (spEnd s - 1)) ≤ 2)
    (hT : IsPGroup 2 T) (hAT : Ab ≤ Subgroup.normalizer (T : Set (StatedSp n K))) :
    T = ⊥ := by
  haveI : Finite ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K)) :=
    Finite.of_injective (fun e : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K) =>
      (e : (Fin n ⊕ Fin n → K) → (Fin n ⊕ Fin n → K))) fun e e' h => LinearEquiv.ext (congrFun h)
  haveI : Fintype ↥(Ab.map (spAct n K)) := Fintype.ofFinite _
  have hA9 : Nat.card ↥(Ab.map (spAct n K)) = 9 := by
    rw [Subgroup.card_map_of_injective spAct_injective, h9]
  have hB : InvariantBilin (Ab.map (spAct n K)) (spForm n K) := fun a u v => by
    obtain ⟨s, -, hs⟩ := Subgroup.mem_map.mp a.2
    rw [← hs]
    exact spAct_isometry s u v
  have hfixA : ∀ a : ↥(Ab.map (spAct n K)), a ≠ 1 →
      Module.finrank K (fixedByEnd (a : (Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))) ≤ 2 :=
    fun a ha1 => by
      obtain ⟨s, hs, hsa⟩ := Subgroup.mem_map.mp a.2
      have hs1 : s ≠ 1 := by
        rintro rfl
        exact ha1 (Subtype.ext (hsa.symm.trans (map_one (spAct n K))))
      rw [← hsa, fixedByEnd_spAct]
      exact hfix s hs hs1
  have hA := CFSG.SectionRank.isElemAbelian_map hAb (spAct n K)
  have hpF : ((3 : ℕ) : K) ≠ 0 := fun h => by
    have h2 := (CharP.cast_eq_zero_iff K 2 3).mp h
    omega
  have hT' := eq_bot_of_normalized_two_subgroup (Ab.map (spAct n K)) hF spForm_isAlt hB
    spForm_nondegenerate hA
    (fixedSpaceOf_eq_bot_of_card_nine (Ab.map (spAct n K)) hpF spForm_isAlt hB
      spForm_nondegenerate hA hA9 hfixA)
    (finrank_blockSpace_le_two_of_card_nine (Ab.map (spAct n K)) hA9 hfixA)
    (T := T.map (spAct n K)) (hT.map (spAct n K)) (fun t ht u v => by
      obtain ⟨s, -, hs⟩ := Subgroup.mem_map.mp ht
      rw [← hs]
      exact spAct_isometry s u v)
    ((Subgroup.map_mono hAT).trans (Subgroup.le_normalizer_map (spAct n K)))
  exact (Subgroup.map_eq_bot_iff_of_injective T spAct_injective).mp hT'

end Normalized

end CFSG.LocalAnalysis.GLTheoremA.S265A

end
