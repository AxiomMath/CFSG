module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6Levi
public import CFSG.LieType.Chevalley.E7SupportedBruhat
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddPSp

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Generic (Commutes)
open scoped MatrixGroups

@[expose] def e6BitsD5 : Fin (Tag.rank .E6) → Bool :=
  listMask [true, false, false, false, false, false]

theorem e6BitsD5_eq_false : ∀ j : Fin (Tag.rank .E6), j ≠ e6Node 0 → e6BitsD5 j = false := by
  decide

theorem maskPairing_e6BitsD5 (α : Fin (Tag.rank .E6) → ℤ) :
    maskPairing e6BitsD5 α = α (e6Node 0) := by
  rw [maskPairing, Finset.sum_eq_single (e6Node 0)]
  · simp [show e6BitsD5 (e6Node 0) = true from by decide]
  · intro j _ hj
    simp [e6BitsD5_eq_false j hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem e6_even_zero_cases : ∀ α ∈ rootFinset .E6, Even (α (e6Node 0)) → α (e6Node 0) = 0 := by
  decide +kernel

theorem e6D5Node_ne_zero : ∀ k : Fin 5, e6D5Node k ≠ e6Node 0 := by decide

theorem eq_zero_of_forall_e6D5Node_ne :
    ∀ i : Fin (Tag.rank .E6), (∀ k, e6D5Node k ≠ i) → i = e6Node 0 := by
  decide

theorem mem_parabolicRoots_e6LeviD5 {α : Fin (Tag.rank .E6) → ℤ} :
    α ∈ parabolicRoots .E6 e6LeviD5 ↔ IsRoot .E6 α ∧ α (e6Node 0) = 0 := by
  refine and_congr_right fun _ => ⟨fun h => h _ ?_, fun h i hi => ?_⟩
  · rintro ⟨k, hk⟩
    exact e6D5Node_ne_zero k hk
  · rw [eq_zero_of_forall_e6D5Node_ne i fun k hk => hi ⟨k, hk⟩]
    exact h

theorem rootCharKernel_e6BitsD5
    {K : Type} [Field K] (hK2 : ringChar K ≠ 2) :
    rootCharKernel (bitsTuple (K := K) e6BitsD5) = parabolicRoots .E6 e6LeviD5 := by
  rw [rootCharKernel_eq_kernelRoots hK2 (bitsTuple_mem _), signTupleBits_bitsTuple hK2]
  ext α
  rw [mem_kernelRoots_maskChar, maskPairing_e6BitsD5, mem_parabolicRoots_e6LeviD5]
  constructor
  · rintro ⟨hα, hev⟩
    exact ⟨hα, e6_even_zero_cases α (mem_rootFinset.2 hα) hev⟩
  · rintro ⟨hα, h⟩
    exact ⟨hα, by rw [h]; decide⟩

theorem e6_toral_D5_component
    {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p ^ f)
    {M : Subgroup (toralCentralizer .E6 K (bitsTuple e6BitsD5))} (hM : IsComponent M) :
    OddLieCentralQuotient p M := by
  classical
  obtain ⟨hf, -⟩ := one_le_and_three_le_of_card hp hp2 hK
  have : CharP K p :=
    LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K p]; exact hp2
  have hadm : StatedLieAdmissible .POmegaPlus 5 p f := ⟨hp, hf, by norm_num⟩
  obtain ⟨hSX, hSn, hsolv, -, -⟩ :=
    odd_toral_involution_centralizer_p_component_root_reduction .E6 K hK2 _
      (bitsTuple_mem (K := K) e6BitsD5)
  obtain ⟨hqs, hlie⟩ := e6_levi_D5_recognition hp hp2 hK
  have hS : rootSpan .E6 K (rootCharKernel (bitsTuple (K := K) e6BitsD5)) =
      subsystemGroup .E6 K e6LeviD5 := by
    rw [rootCharKernel_e6BitsD5 hK2, ← subsystemGroup_eq_rootSpan]
  let e₁ := MulEquiv.subgroupCongr hS
  let e₂ := Subgroup.subgroupOfEquivOfLe hSX
  have hq := LocalCores.isQuasisimple_of_mulEquiv (e₂.trans e₁).symm hqs
  have hMeq := eq_of_isComponent_of_normal_quasisimple hq hsolv hM
  let e : M ≃* subsystemGroup .E6 K e6LeviD5 := (MulEquiv.subgroupCongr hMeq).trans (e₂.trans e₁)
  exact ⟨.POmegaPlus, 5, f, hadm, lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) hlie⟩

end CFSG.ComponentClassification.CatLeafProof
