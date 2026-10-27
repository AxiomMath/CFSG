module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviDom

import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailEqClosure
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailWeylLift

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open scoped Pointwise

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

private lemma distribSMulToLinearMap_eq_coe_H03 {M : Type} [AddCommGroup M] [Module K M]
    (e : M ≃ₗ[K] M) :
    DistribSMul.toLinearMap K M e = (e : M →ₗ[K] M) :=
  LinearMap.ext fun x => by
    rw [DistribSMul.toLinearMap_apply, LinearEquiv.smul_def, LinearEquiv.coe_coe]

theorem tailRankOneParabolic_le_orthElementaryGroup (i : Fin r) :
    tailRankOneParabolic qA a₀ i ≤ orthElementaryGroup (quadTail r qA) := by
  rw [tailRankOneParabolic, Subgroup.closure_le]
  rintro _ (hb | rfl)
  · exact tailBorel_le hb
  · exact tailWeylElt_mem a₀ i

theorem tailRankOneParabolic_le_tailLeviDom {i : Fin r} (hi : i.val + 1 < r)
    (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) :
    tailRankOneParabolic qA a₀ i ≤ tailLeviDom r qA i := by
  rw [tailRankOneParabolic, Subgroup.closure_le]
  rintro _ (hb | rfl)
  · exact tailBorel_le_tailLeviDom i hb
  · change tailWeylElt r qA a₀ i ∈ tailLeviDom r qA i
    rw [mem_tailLeviDom]
    refine ⟨tailWeylElt_mem a₀ i, ?_⟩
    intro k hk1 hkr hkne
    let j : Fin r := ⟨k - 1, by omega⟩
    have hjk : (j : ℕ) + 1 = k := by simp only [j]; omega
    have hji : i ≠ j := fun hij => hkne (by rw [← hjk, hij])
    have hs : tailWeylElt r qA a₀ i • tailFlag K A r k = tailFlag K A r k := by
      simpa only [hjk] using (tailWeylElt_smul_tailFlag (qA := qA) hani ha₀ j i).2 hji
    simpa only [Submodule.pointwise_smul_def, distribSMulToLinearMap_eq_coe_H03] using hs

theorem tailRankOneParabolic_eq_tailLeviDom [FiniteDimensional K A] {i : Fin r}
    (hi : i.val + 1 < r) (hani : qA.Anisotropic) (ha₀ : a₀ ≠ 0) :
    tailRankOneParabolic qA a₀ i = tailLeviDom r qA i := by
  refine le_antisymm (tailRankOneParabolic_le_tailLeviDom hi hani ha₀) ?_
  have hgen := tail_eq_closure_of_borel_le (qA := qA) hani ha₀
    (tailLeviDom_le i) (tailBorel_le_tailLeviDom i)
  rw [hgen, tailRankOneParabolic]
  apply Subgroup.closure_mono
  apply Set.union_subset_union_right
  rw [Set.image_subset_iff]
  intro j hj
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  by_cases hji : j = i
  · rw [hji]
  · exfalso
    have hk1 : 1 ≤ (j : ℕ) + 1 := Nat.le_add_left 1 _
    have hkr : (j : ℕ) + 1 ≤ r := by have := j.isLt; omega
    have hkne : (j : ℕ) + 1 ≠ (i : ℕ) + 1 :=
      fun h => hji (Fin.ext (Nat.succ.inj h))
    have hmap := (mem_tailLeviDom.1 hj).2 ((j : ℕ) + 1) hk1 hkr hkne
    have hfix : tailWeylElt r qA a₀ j • tailFlag K A r ((j : ℕ) + 1) =
        tailFlag K A r ((j : ℕ) + 1) := by
      rw [Submodule.pointwise_smul_def, distribSMulToLinearMap_eq_coe_H03]
      exact hmap
    exact (tailWeylElt_smul_tailFlag (qA := qA) hani ha₀ j j).1 hfix rfl

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
