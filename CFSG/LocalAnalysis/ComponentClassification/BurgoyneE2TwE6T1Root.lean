module

public import CFSG.LieType.HighestRoot.CentChevalleyData
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinning
public import CFSG.LieType.Chevalley.RationalToralSignDiagramDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE6T1

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.HighestRoot CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

abbrev t1Node (i : Fin 6) : Fin TwistTag.E6.tag.rank := i

@[expose] def witE6Two : List ℕ :=
  [0, 8952201, 0, 0, 9996424, 9013384, 0, 0, 8952201, 0, 0, 0, 0, 0, 9996424, 9013384, 9013384, 0,
    8947864, 0, 0, 0, 0, 0, 0, 0, 9013384, 8947864, 8947864, 8947864, 0, 0, 0, 0, 0, 0, 0, 8947864,
    8947864, 8947864, 8947864, 0, 0, 9996424, 0, 0, 8947864, 8947864, 0, 8947864, 9996424, 0,
    9013384, 0, 8947864, 0, 0, 9013384, 9013384, 0, 0, 0, 0, 9013384, 0, 0, 0, 0, 8947864, 8947864,
    8947864, 8947864]

theorem isolatedCheck_E6_two : isolatedCheck TwistTag.E6.tag (t1Node 2) witE6Two = true := by
  decide +kernel

theorem kernel_twenty_check : ∀ γ ∈ rootFinset TwistTag.E6.tag,
    maskPairing (natBits 20) γ % 2 = 0 → γ (t1Node 2) = γ (t1Node 4) := by
  decide +kernel

section Field

variable {L : Type} [Field L]


theorem rootChar_e6_eq (b : Fin TwistTag.E6.tag.rank → Lˣ) (v : Fin TwistTag.E6.tag.rank → ℤ) :
    rootChar b v = b (t1Node 0) ^ v (t1Node 0) * b (t1Node 1) ^ v (t1Node 1) *
      b (t1Node 2) ^ v (t1Node 2) * b (t1Node 3) ^ v (t1Node 3) * b (t1Node 4) ^ v (t1Node 4) *
        b (t1Node 5) ^ v (t1Node 5) := by
  show ∏ i : Fin 6, b i ^ v i = _
  rw [Fin.prod_univ_six]

theorem rootChar_twenty_three :
    rootChar (signCharTuple (k := L) (signMaskChar TwistTag.E6.tag 20))
      (Pi.single (t1Node 2) 1) = -1 := by
  rw [rootChar_signCharTuple, signMaskChar, maskChar_apply]
  have h : maskPairing (natBits 20) (Pi.single (t1Node 2) 1 : Fin TwistTag.E6.tag.rank → ℤ) = 1 :=
    by decide +kernel
  rw [h, zpow_one]
  ext
  simp

theorem rootChar_eq_one_of_mem_kernelRoots_twenty
    {b : Fin TwistTag.E6.tag.rank → Lˣ} (h0 : b (t1Node 0) = 1) (h1 : b (t1Node 1) = 1)
    (h3 : b (t1Node 3) = 1) (h5 : b (t1Node 5) = 1) (h24 : b (t1Node 2) * b (t1Node 4) = 1)
    {γ : Fin TwistTag.E6.tag.rank → ℤ} (hγ : γ ∈ kernelRoots (signMaskChar TwistTag.E6.tag 20)) :
    rootChar b γ = 1 := by
  rw [signMaskChar, mem_kernelRoots_maskChar] at hγ
  have h := kernel_twenty_check γ (mem_rootFinset.2 hγ.1) (Int.even_iff.1 hγ.2)
  rw [rootChar_e6_eq, h0, h1, h3, h5, h]
  simp only [one_zpow, one_mul, mul_one]
  rw [← mul_zpow, h24, one_zpow]

theorem rootDiagUnit_commute_levi_twenty {b : Fin TwistTag.E6.tag.rank → Lˣ} (h0 : b (t1Node 0) = 1)
    (h1 : b (t1Node 1) = 1) (h3 : b (t1Node 3) = 1) (h5 : b (t1Node 5) = 1)
    (h24 : b (t1Node 2) * b (t1Node 4) = 1) {y : ModGL TwistTag.E6.tag L}
    (hy : y ∈ torusGroup TwistTag.E6.tag L ⊔
      rootSpan TwistTag.E6.tag L (kernelRoots (signMaskChar TwistTag.E6.tag 20))) :
    rootDiagUnit TwistTag.E6.tag b * y = y * rootDiagUnit TwistTag.E6.tag b := by
  have hle : torusGroup TwistTag.E6.tag L ⊔
      rootSpan TwistTag.E6.tag L (kernelRoots (signMaskChar TwistTag.E6.tag 20)) ≤
        Subgroup.centralizer {rootDiagUnit TwistTag.E6.tag b} := by
    refine sup_le (fun h hh => ?_) (iSup₂_le fun γ hγ => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (rootDiagUnit_mul_comm_of_mem_torusGroup b hh).symm
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h := rootDiagUnit_conj_pinnedX b hγ.1 c
      rw [rootChar_eq_one_of_mem_kernelRoots_twenty h0 h1 h3 h5 h24 hγ, Units.val_one,
        one_mul] at h
      calc pinnedX TwistTag.E6.tag L γ c * rootDiagUnit TwistTag.E6.tag b =
          (rootDiagUnit TwistTag.E6.tag b * pinnedX TwistTag.E6.tag L γ c *
            (rootDiagUnit TwistTag.E6.tag b)⁻¹) * rootDiagUnit TwistTag.E6.tag b := by rw [h]
        _ = rootDiagUnit TwistTag.E6.tag b * pinnedX TwistTag.E6.tag L γ c := by group
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem rootSL2_simple_eq (i : Fin TwistTag.E6.tag.rank)
    (A : SL2 L) : rootSL2 TwistTag.E6.tag L (Pi.single i 1) A =
      simpleRootSL2 TwistTag.E6.tag L i A := by
  rw [rootSL2_apply, pinnedData_single]
  simp [pinnedWeyl, pinnedData_single]


theorem toralCentralizer_le_normalizer_e6Two (hL : ringChar L ≠ 2) :
    toralCentralizer TwistTag.E6.tag L (signTuple TwistTag.E6.tag L (t1Node 2)) ≤
      Subgroup.normalizer ((rootSubgroup TwistTag.E6.tag L (Pi.single (t1Node 2) 1) ⊔
        rootSubgroup TwistTag.E6.tag L (-Pi.single (t1Node 2) 1) :
          Subgroup (ModGL TwistTag.E6.tag L)) : Set (ModGL TwistTag.E6.tag L)) := by
  have hγ : IsRoot TwistTag.E6.tag (Pi.single (t1Node 2) 1) := isRoot_single TwistTag.E6.tag _
  have hlong : ∀ ε, IsRoot TwistTag.E6.tag ε →
      iform ε ε ≤ iform (Pi.single (t1Node 2) 1) (Pi.single (t1Node 2) 1) := by
    intro ε hε
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hε
    rw [hj, iform_single_single]
    linarith [symmetrizer_le_one TwistTag.E6.tag rfl (t1Node 2) j]
  have hC1 : ∀ α ∈ rootCharKernel (signTuple TwistTag.E6.tag L (t1Node 2)),
      α ≠ Pi.single (t1Node 2) 1 → α ≠ -Pi.single (t1Node 2) 1 →
        iform α (Pi.single (t1Node 2) 1) = 0 :=
    fun α hα hne hne' => iform_eq_zero_of_mem_rootCharKernel_signTuple hL hlong hα hne hne'
  exact toralCentralizer_le_normalizer_pair hγ
    (fun α hα hne hne' =>
      commute_pair_of_iform_eq_zero noG2_E6' hα.1 hγ hlong (hC1 α hα hne hne') hne hne')
    fun w hw => smul_eq_or_eq_neg_of_mem_rootCharStabilizer
      (single_mem_rootCharKernel_signTuple hL _) hC1
      (fun δ hδ hne hne' => exists_of_isolatedCheck hL isolatedCheck_E6_two hδ hne hne') hw

theorem exists_conj_rootSL2_three (hL : ringChar L ≠ 2) {y : ModGL TwistTag.E6.tag L}
    (hy : y ∈ adjointGroup TwistTag.E6.tag L)
    (hyt : y * rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 2) 1) (-1) =
      rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 2) 1) (-1) * y) (A : SL2 L) :
    ∃ A' : SL2 L, y * rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 2) 1) A * y⁻¹ =
      rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 2) 1) A' := by
  have hd : rootSL2 TwistTag.E6.tag L (Pi.single (t1Node 2) 1) (-1) =
      rootDiagUnit TwistTag.E6.tag (signTuple TwistTag.E6.tag L (t1Node 2)) := by
    rw [rootSL2_simple_eq, neg_one_eq_HSL_neg_one, simpleRootSL2_HSL, torusElt_neg_one_eq]
  have hyd : rootDiagUnit TwistTag.E6.tag (signTuple TwistTag.E6.tag L (t1Node 2)) * y *
      (rootDiagUnit TwistTag.E6.tag (signTuple TwistTag.E6.tag L (t1Node 2)))⁻¹ = y := by
    rw [← hd, ← hyt, mul_inv_cancel_right]
  have hN := toralCentralizer_le_normalizer_e6Two hL (mem_toralCentralizer.2 ⟨hy, hyd⟩)
  rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2] at hN
  obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.1 hN
    (simpleRootSL2 TwistTag.E6.tag L (t1Node 2) A)).1 ⟨A, rfl⟩
  exact ⟨A', by rw [rootSL2_simple_eq, rootSL2_simple_eq, hA']⟩

end Field

end CFSG.ComponentClassification.Burgoyne.E2.TwE6T1
