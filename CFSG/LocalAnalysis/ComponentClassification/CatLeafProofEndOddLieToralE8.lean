module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofEndOddLieToralRows
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE8Inner

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.LocalAnalysis.ComponentInitial
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

theorem e8_toral_D8_quat
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    QuatComponentForm (toralCentralizer .E8 K (bitsTuple e8BitsD8)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E8 K hK2 _
      (bitsTuple_mem (K := K) e8BitsD8)
  obtain ⟨-, -, -, hqs, -⟩ := exists_psi_D8_E8 hp hp2 hK
  let e₁ : ↥(⨆ k, e8D8Chain K k) ≃*
      rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsD8)) :=
    ((⨆ k, e8D8Chain K k).equivMapOfInjective _ (adjointGroup .E8 K).subtype_injective).trans
      (MulEquiv.subgroupCongr (map_subtype_iSup_e8D8Chain hK2))
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁.symm).symm hqs
  have hker : rootCharKernel (bitsTuple (K := K) e8BitsD8) =
      kernelRoots (maskChar (τ := .E8) e8BitsD8) := by
    rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  have hmem : ∀ γ : Fin (Tag.rank .E8) → ℤ, IsRoot .E8 γ → γ (e8Node 0) = 0 →
      rootSubgroup .E8 K γ ≤ rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsD8)) := by
    intro γ hγ h0
    have hγS : γ ∈ rootCharKernel (bitsTuple (K := K) e8BitsD8) := by
      rw [hker, mem_kernelRoots_maskChar, maskPairing_e8BitsD8, h0]
      exact ⟨hγ, ⟨0, rfl⟩⟩
    exact le_biSup (f := fun γ => rootSubgroup .E8 K γ) hγS
  intro M hM
  obtain rfl := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  exact exists_quaternion_of_rootPair_le hK2 (isRoot_single _ (e8Node 1)) hSX
    (sup_le (hmem _ (isRoot_single _ _) (by decide))
      (hmem _ (IsRoot.neg (isRoot_single _ _)) (by decide)))

theorem e8_toral_E7_quat
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f) :
    QuatComponentForm (toralCentralizer .E8 K (bitsTuple e8BitsE7)) := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p := finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have : Finite (ModGL .E8 K) := finite_modGL
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E8 K hK2 _ (bitsTuple_mem _)
  set H := subsystemGroup .E8 K e8LeviE7 with hH_def
  set Q := rootSubgroup .E8 K hiE8 ⊔ rootSubgroup .E8 K (-hiE8) with hQ_def
  have hS : rootSpan .E8 K (rootCharKernel (bitsTuple (K := K) e8BitsE7)) = H ⊔ Q := by
    rw [rootCharKernel_e8BitsE7 hK2, rootSpan_union_pair, ← subsystemGroup_eq_rootSpan]
  obtain ⟨hqH, -⟩ := e8_levi_E7_recognition hp hp2 hK
  obtain ⟨-, ⟨eQ⟩, -, -⟩ := odd_arbitrary_root_pair_SL2_p_components .E8 K hK2 isRoot_hiE8
  have hQmap : (rootGroup (rootOperatorFamily .E8) K hiE8 ⊔
      rootGroup (rootOperatorFamily .E8) K (-hiE8)).map (adjointGroup .E8 K).subtype = Q := by
    rw [Subgroup.map_sup, map_subtype_rootGroup _ isRoot_hiE8,
      map_subtype_rootGroup _ (IsRoot.neg isRoot_hiE8)]
  have hcomm' : Commutes (⨆ k, rankOne (adjDatum (rootOperatorFamily .E8) K).rootGroup
      (e8E7Node k)) (rootGroup (rootOperatorFamily .E8) K hiE8 ⊔
        rootGroup (rootOperatorFamily .E8) K (-hiE8)) :=
    ClassicalInvolution.RouteD.commutes_iSup_left.2 fun k =>
      commutes_rootPair_of_noG2 noG2_E8 (isRoot_single _ _) isRoot_hiE8
        (e8E7Node_ne_hiE8 k).1 (e8E7Node_ne_hiE8 k).2 (iform_e8E7Node_hiE8 k)
        (not_isRoot_e8E7Node_hiE8 k).1 (not_isRoot_e8E7Node_hiE8 k).2
  have hcomm : Commutes H Q := by
    rw [hH_def, show e8LeviE7 = Set.range e8E7Node from rfl,
      ← map_subtype_iSup_rankOne e8E7Node, ← hQmap]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm' x hx y hy]
  have hHX : H ≤ toralCentralizer .E8 K (bitsTuple e8BitsE7) :=
    (le_sup_left.trans hS.symm.le).trans hSX
  intro M hM
  rcases eq_or_SL_of_two_factors hS hSX hsolv hcomm hqH eQ
      (rootPair_quasisimple_or_solvable hp hp2 hK hK2 isRoot_hiE8) hM with h | he
  · subst h
    exact exists_quaternion_of_rootPair_le hK2 (isRoot_single _ _) hHX
      (rootPair_le_subsystemGroup (i := e8E7Node 0) ⟨0, rfl⟩)
  · obtain ⟨e⟩ := he
    exact exists_quaternion_of_mulEquiv_SL hK2 e

theorem oddExcInnerDiagQuatForm_E8
    : OddExcInnerDiagQuatForm .E8 := by
  refine oddExcInnerDiagQuatForm_of_toral (Or.inr (Or.inr (Or.inr rfl)))
    fun K _ _ p f hp hp2 hKp b hb hb1 => ?_
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hKp
  have : CharP K p := finite_field_prime_power_characteristic hp hf hKp
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  refine toralCentralizer_quat_of_orbitCheck hK2 e8SignOrbit_check (fun ρ hρ hne => ?_) hb hb1
  have hlen : e8SignReps.length = 3 := rfl
  rw [hlen] at hρ
  interval_cases ρ
  · exact absurd (by funext i; revert i; decide) hne
  · exact e8_toral_D8_quat hp hp2 hKp
  ·
    have hmap := map_conj_toralCentralizer_of_maskAct (K := K) hK2 e8MaskWord e8BitsE7
    rw [maskAct_e8MaskWord] at hmap
    let e : toralCentralizer .E8 K (bitsTuple e8BitsE7) ≃*
        toralCentralizer .E8 K (bitsTuple (listMask (e8SignReps.getD 2 []))) :=
      ((toralCentralizer .E8 K _).equivMapOfInjective _ (MulAut.conj _).injective).trans
        (MulEquiv.subgroupCongr hmap)
    exact quatComponentForm_of_mulEquiv e.symm (e8_toral_E7_quat hp hp2 hKp)

end CFSG.ComponentClassification.CatLeafProof
