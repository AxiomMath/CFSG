module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeBadPlaneToralClass
public import CFSG.LieType.Steinberg.CentralExt.AdjointCentrallyClosed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.ExceptionalCover
open CFSG.LieType.Steinberg.CentralExt.AdjointClosed
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

@[expose] def e6FourToralExponent : Fin Tag.E6.rank → ℤ := ![0, 1, 1, 2, 2, 2]

@[expose] def e6FourToralParam : Fin Tag.E6.rank → Kˣ :=
  cartanChar (tvec omegaUnit e6FourToralExponent)

theorem rootChar_e6FourToralParam (β : Fin Tag.E6.rank → ℤ) :
    rootChar e6FourToralParam β = omegaUnit ^ ∑ k, e6FourToralExponent k * cartanCoord β k := by
  rw [e6FourToralParam, rootChar_cartanChar_prod, zpow_sum_eq_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  change (omegaUnit ^ e6FourToralExponent j) ^ cartanCoord β j = _
  rw [← zpow_mul]

section Kernel


private theorem div_iff_coord (k : Fin 72) :
    ((3 : ℤ) ∣ ∑ j, e6FourToralExponent j * cartanCoord (e6Root k) j) ↔
      e6Root k (0 : Fin 6) = 0 ∧ e6Root k (5 : Fin 6) = 0 := by
  fin_cases k <;> decide

theorem rootCharKernel_e6FourToralParam :
    rootCharKernel e6FourToralParam =
      {β : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 β ∧ β (0 : Fin 6) = 0 ∧ β (5 : Fin 6) = 0} := by
  ext β
  constructor
  · rintro ⟨hβ, hχ⟩
    have h3 : (3 : ℤ) ∣ ∑ k, e6FourToralExponent k * cartanCoord β k := by
      rw [← omegaUnit_zpow_eq_one_iff, ← rootChar_e6FourToralParam]
      exact hχ
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hβ
    exact ⟨isRoot_e6Root k, (div_iff_coord k).1 h3⟩
  · rintro ⟨hβ, h0, h5⟩
    refine ⟨hβ, ?_⟩
    rw [rootChar_e6FourToralParam, omegaUnit_zpow_eq_one_iff]
    obtain ⟨k, rfl⟩ := exists_e6Root_eq hβ
    exact (div_iff_coord k).2 ⟨h0, h5⟩

theorem e6FourToralElement_mem_torusGroup :
    rootDiagUnit Tag.E6 e6FourToralParam ∈ torusGroup Tag.E6 K := by
  have h := list_prod_torusElt_eq_rootDiagUnit (τ := Tag.E6) (K := K)
    (tvec omegaUnit e6FourToralExponent)
  rw [← e6FourToralParam] at h
  rw [← h]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact torusElt_mem_torusGroup j _

theorem e6FourToralElement_mem_adjointGroup :
    rootDiagUnit Tag.E6 e6FourToralParam ∈ adjointGroup Tag.E6 K :=
  ((torusGroup_le_borelGroup (τ := Tag.E6) (R := K)).trans
    (borelGroup_le_adjointGroup' (τ := Tag.E6) (K := K)))
    e6FourToralElement_mem_torusGroup

end Kernel

section RootSpan


theorem rootSpan_rootCharKernel_e6FourToralParam :
    rootSpan Tag.E6 K (rootCharKernel e6FourToralParam) =
      subsystemGroup Tag.E6 K setD := by
  have hmem : ∀ i : Fin 6, i ∉ setD ↔ i = 0 ∨ i = 5 := by
    intro i
    change i ∉ ({1, 2, 3, 4} : Set (Fin 6)) ↔ i = 0 ∨ i = 5
    fin_cases i <;> decide
  have hset : {β : Fin Tag.E6.rank → ℤ | IsRoot Tag.E6 β ∧ β (0 : Fin 6) = 0 ∧
      β (5 : Fin 6) = 0} = parabolicRoots Tag.E6 setD := by
    ext β
    constructor
    · rintro ⟨hβ, h0, h5⟩
      refine ⟨hβ, fun i hi => ?_⟩
      rcases (hmem i).1 hi with rfl | rfl
      · exact h0
      · exact h5
    · rintro ⟨hβ, h⟩
      exact ⟨hβ, h (0 : Fin 6) ((hmem 0).2 (Or.inl rfl)),
        h (5 : Fin 6) ((hmem 5).2 (Or.inr rfl))⟩
  rw [rootCharKernel_e6FourToralParam, hset,
    ← subsystemGroup_eq_rootSpan (τ := Tag.E6) (K := K) setD]

end RootSpan

end CFSG.LocalAnalysis.GLTheoremA.Y10F
