module

public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneE2TwE7CentData
public import CFSG.LieType.HighestRoot.CentChevalleyData

public noncomputable section

namespace CFSG.ComponentClassification.Burgoyne.E2.TwE7

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LieType.HighestRoot CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups

@[expose] def e7Beta0 : Fin (Tag.rank .E7) → ℤ := ![0, 1, 0, 1, 1, 1, 1]

@[expose] def witE7One : List ℕ :=
  [143165832, 0, 143165577, 0, 144214152, 143231112, 144214152, 143165832, 143165577, 0, 0,
    143165577, 0, 0, 0, 144214152, 143231112, 143231112, 143231112, 144214152, 143165577, 0, 0, 0,
    0, 0, 0, 0, 0, 143231112, 143231112, 143231112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143231112, 0,
    0, 0, 0, 0, 0, 143165577, 0, 0, 0, 0, 0, 0, 0, 143165577, 0, 0, 143165577, 0, 0, 143165577, 0,
    0, 143165577, 0, 0, 143165832, 143165577, 0, 143165577, 0, 143165577, 143165577, 143165832,
    143165577, 0, 143165832, 143165577, 143165577, 143165577, 143165577, 143165577, 143165832,
    143165577, 143165577, 143165832, 143165832, 143165577, 143165577, 143165577, 143165832,
    143165832, 143165577, 0, 143165832, 143165577, 143165577, 0, 143165832, 143165577, 0, 0,
    143165832, 0, 0, 143165832, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 143165832, 143165832, 143165577,
    143165577, 143165577, 143165577]

theorem isolatedCheck_E7_one : isolatedCheck .E7 (e7Node 1) witE7One = true := by
  decide +kernel

theorem kernel_three_check : ∀ γ ∈ rootFinset .E7,
    maskPairing (natBits 3) γ % 2 = 0 → γ (e7Node 0) = γ (e7Node 1) := by
  decide +kernel

theorem pinnedData_e7Beta0 : (pinnedData .E7 e7Beta0).1 = e7Node 1 := by
  have h1 : ¬ ∃ j, e7Beta0 = Pi.single j 1 := by decide
  have h2 : ¬ ∃ j, e7Beta0 = -Pi.single j 1 := by decide
  rw [pinnedData, dite_eq_right h1, dite_eq_right h2]
  decide +kernel


theorem isRoot_e7Beta0 : IsRoot .E7 e7Beta0 :=
  mem_rootFinset.1 (by decide +kernel)

theorem wordElt_e7Word2_1_e7Beta0 : ToralSign.wordElt .E7 e7Word2_1 • e7Beta0 = -e7Beta0 := by
  have h1 : e7Certificate.root 52 = e7Beta0 := by decide +kernel
  have h2 : applyWordIdx e7Certificate e7Word2_1 52 = 63 := by decide +kernel
  have h3 : e7Certificate.root 63 = -e7Beta0 := by decide +kernel
  obtain ⟨-, he⟩ := applyWordIdx_spec e7Certificate_check e7Word2_1 (k := 52) (by decide +kernel)
  rw [h2, h3, h1] at he
  exact he.symm

section Field

variable {L : Type} [Field L]

theorem rootChar_three_e7Beta0 :
    rootChar (signCharTuple (k := L) (signMaskChar .E7 3)) e7Beta0 = -1 := by
  rw [rootChar_signCharTuple, signMaskChar, maskChar_apply]
  have h : maskPairing (natBits 3) e7Beta0 = 1 := by decide +kernel
  rw [h, zpow_one]
  ext
  simp

theorem rootChar_e7Beta0 {b : Fin (Tag.rank .E7) → Lˣ}
    (hb : ∀ j : Fin 7, 2 ≤ j.val → b (e7Node j) = 1) : rootChar b e7Beta0 = b (e7Node 1) := by
  rw [rootChar_E7, hb 2 (by decide), hb 3 (by decide), hb 4 (by decide), hb 5 (by decide),
    hb 6 (by decide)]
  have e0 : e7Beta0 (e7Node 0) = 0 := rfl
  have e1 : e7Beta0 (e7Node 1) = 1 := rfl
  rw [e0, e1]
  simp

theorem rootChar_eq_one_of_mem_kernelRoots_three {b : Fin (Tag.rank .E7) → Lˣ}
    (hb : ∀ j : Fin 7, 2 ≤ j.val → b (e7Node j) = 1) (hb01 : b (e7Node 0) * b (e7Node 1) = 1)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : γ ∈ kernelRoots (signMaskChar .E7 3)) :
    rootChar b γ = 1 := by
  rw [signMaskChar, mem_kernelRoots_maskChar] at hγ
  have h := kernel_three_check γ (mem_rootFinset.2 hγ.1) (Int.even_iff.1 hγ.2)
  rw [rootChar_E7, hb 2 (by decide), hb 3 (by decide), hb 4 (by decide), hb 5 (by decide),
    hb 6 (by decide), h]
  simp only [one_zpow, mul_one]
  rw [← mul_zpow, hb01, one_zpow]

theorem rootDiagUnit_commute_levi_three {b : Fin (Tag.rank .E7) → Lˣ}
    (hb : ∀ j : Fin 7, 2 ≤ j.val → b (e7Node j) = 1) (hb01 : b (e7Node 0) * b (e7Node 1) = 1)
    {y : ModGL .E7 L}
    (hy : y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (kernelRoots (signMaskChar .E7 3))) :
    rootDiagUnit .E7 b * y = y * rootDiagUnit .E7 b := by
  have hle : torusGroup .E7 L ⊔ rootSpan .E7 L (kernelRoots (signMaskChar .E7 3)) ≤
      Subgroup.centralizer {rootDiagUnit .E7 b} := by
    refine sup_le (fun h hh => ?_) (iSup₂_le fun γ hγ => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (rootDiagUnit_mul_comm_of_mem_torusGroup b hh).symm
    · rw [rootSubgroup, Subgroup.closure_le]
      rintro _ ⟨c, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have h := rootDiagUnit_conj_pinnedX b hγ.1 c
      rw [rootChar_eq_one_of_mem_kernelRoots_three hb hb01 hγ, Units.val_one, one_mul] at h
      calc pinnedX .E7 L γ c * rootDiagUnit .E7 b =
          (rootDiagUnit .E7 b * pinnedX .E7 L γ c * (rootDiagUnit .E7 b)⁻¹) *
            rootDiagUnit .E7 b := by rw [h]
        _ = rootDiagUnit .E7 b * pinnedX .E7 L γ c := by group
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem toralCentralizer_le_normalizer_e7One (hL : ringChar L ≠ 2) :
    toralCentralizer .E7 L (signTuple .E7 L (e7Node 1)) ≤ Subgroup.normalizer
      ((rootSubgroup .E7 L (Pi.single (e7Node 1) 1) ⊔
        rootSubgroup .E7 L (-Pi.single (e7Node 1) 1) : Subgroup (ModGL .E7 L)) :
          Set (ModGL .E7 L)) := by
  have hγ : IsRoot .E7 (Pi.single (e7Node 1) 1) := isRoot_single .E7 _
  have hlong : ∀ ε, IsRoot .E7 ε →
      iform ε ε ≤ iform (Pi.single (e7Node 1) 1) (Pi.single (e7Node 1) 1) := by
    intro ε hε
    obtain ⟨j, hj⟩ := iform_self_of_isRoot hε
    rw [hj, iform_single_single]
    linarith [symmetrizer_le_one .E7 rfl (e7Node 1) j]
  have hC1 : ∀ α ∈ rootCharKernel (signTuple .E7 L (e7Node 1)), α ≠ Pi.single (e7Node 1) 1 →
      α ≠ -Pi.single (e7Node 1) 1 → iform α (Pi.single (e7Node 1) 1) = 0 :=
    fun α hα hne hne' => iform_eq_zero_of_mem_rootCharKernel_signTuple hL hlong hα hne hne'
  exact toralCentralizer_le_normalizer_pair hγ
    (fun α hα hne hne' =>
      commute_pair_of_iform_eq_zero noG2_E7' hα.1 hγ hlong (hC1 α hα hne hne') hne hne')
    fun w hw => smul_eq_or_eq_neg_of_mem_rootCharStabilizer
      (single_mem_rootCharKernel_signTuple hL _) hC1
      (fun δ hδ hne hne' => exists_of_isolatedCheck hL isolatedCheck_E7_one hδ hne hne') hw

theorem exists_conj_rootSL2_e7Beta0 (hL : ringChar L ≠ 2) {y : ModGL .E7 L}
    (hy : y ∈ adjointGroup .E7 L)
    (hyt : y * rootSL2 .E7 L e7Beta0 (-1) = rootSL2 .E7 L e7Beta0 (-1) * y) (A : SL2 L) :
    ∃ A' : SL2 L, y * rootSL2 .E7 L e7Beta0 A * y⁻¹ = rootSL2 .E7 L e7Beta0 A' := by
  set W := pinnedWeyl .E7 L e7Beta0 with hW
  have hWG : W ∈ adjointGroup .E7 L := pinnedWeyl_mem_adjointGroup e7Beta0
  have hρ : ∀ B, rootSL2 .E7 L e7Beta0 B = W * simpleRootSL2 .E7 L (e7Node 1) B * W⁻¹ :=
    fun B => by rw [rootSL2_apply, pinnedData_e7Beta0]
  have hd : simpleRootSL2 .E7 L (e7Node 1) (-1) = rootDiagUnit .E7 (signTuple .E7 L (e7Node 1)) :=
    by rw [neg_one_eq_HSL_neg_one, simpleRootSL2_HSL, torusElt_neg_one_eq]
  set y' := W⁻¹ * y * W with hy'
  have hy'G : y' ∈ adjointGroup .E7 L := mul_mem (mul_mem (inv_mem hWG) hy) hWG
  have hyt' := hyt
  rw [hρ] at hyt'
  have hy'd : rootDiagUnit .E7 (signTuple .E7 L (e7Node 1)) * y' *
      (rootDiagUnit .E7 (signTuple .E7 L (e7Node 1)))⁻¹ = y' := by
    rw [← hd, hy']
    calc simpleRootSL2 .E7 L (e7Node 1) (-1) * (W⁻¹ * y * W) *
          (simpleRootSL2 .E7 L (e7Node 1) (-1))⁻¹ =
        W⁻¹ * ((W * simpleRootSL2 .E7 L (e7Node 1) (-1) * W⁻¹) * y) * W *
          (simpleRootSL2 .E7 L (e7Node 1) (-1))⁻¹ := by group
      _ = W⁻¹ * (y * (W * simpleRootSL2 .E7 L (e7Node 1) (-1) * W⁻¹)) * W *
          (simpleRootSL2 .E7 L (e7Node 1) (-1))⁻¹ := by rw [← hyt']
      _ = W⁻¹ * y * W := by group
  have hN := toralCentralizer_le_normalizer_e7One hL (mem_toralCentralizer.2 ⟨hy'G, hy'd⟩)
  rw [← closure_xUnit_yUnit_eq_rootSubgroup_sup, ← range_simpleRootSL2] at hN
  obtain ⟨A', hA'⟩ := (Subgroup.mem_normalizer_iff.1 hN (simpleRootSL2 .E7 L (e7Node 1) A)).1
    ⟨A, rfl⟩
  refine ⟨A', ?_⟩
  rw [hρ, hρ, hA', hy']
  group

end Field

end CFSG.ComponentClassification.Burgoyne.E2.TwE7
