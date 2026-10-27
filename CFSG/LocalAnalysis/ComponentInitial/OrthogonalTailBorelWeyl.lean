module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailUnipotentGroup

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

theorem signedPermAut_neg_one_neg {r : ℕ} (α : Fin r → ℤ) :
    signedPermAut r 1 (fun _ => -1) (-α) = α := by
  funext j
  simp [signedPermAut_apply]

theorem orthogonal_geometry_tail_Borel_Weyl_generation {K : Type*} [Field K] {A : Type*}
    [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} {qA : QuadraticForm K A}
    (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) :
    orthElementaryGroup (quadTail r qA) =
      Subgroup.closure ((tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)) ∪
        Set.range (tailWeylElt r qA a₀)) := by
  set H := Subgroup.closure ((tailBorel r qA : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)) ∪
    Set.range (tailWeylElt r qA a₀))
  refine le_antisymm ?_ ((Subgroup.closure_le _).2 ?_)
  · have hB : tailBorel r qA ≤ H := fun b hb => Subgroup.subset_closure (Or.inl hb)
    have hN : tailTorusWeyl r qA a₀ ≤ H := by
      rw [tailTorusWeyl, Subgroup.closure_le]
      rintro _ (ht | ⟨i, rfl⟩)
      · exact hB (tailTorus_le_tailBorel ht)
      · exact Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
    have hU : tailUnipotent r qA ≤ H := (tailUnipotent_le_tailBorel hani).trans hB
    rw [(orthogonal_geometry_tail_root_generation hani ⟨a₀, ha₀⟩).1, tailRootSupr]
    refine iSup₂_le fun α hα => ?_
    rcases (mem_posRootsB_or_neg_mem_posRootsB hα).1 with hpos | hneg
    · exact (tailRootGroup_le_tailUnipotent hpos).trans hU
    · obtain ⟨n, hn⟩ := tailTorusWeylNu_surjective hani ha₀
        ⟨signedPermAut r 1 (fun _ => -1), signedPermAut_mem_weylGroupB _ _⟩
      have hmap := map_conj_tailRootGroup hani ha₀ n (posRootsB_subset_rootsB hneg)
      rw [hn] at hmap
      change _ = tailRootGroup r qA (signedPermAut r 1 (fun _ => -1) (-α)) at hmap
      rw [signedPermAut_neg_one_neg] at hmap
      rw [← hmap]
      rintro _ ⟨x, hx, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact mul_mem (mul_mem (hN n.2) (hU (tailRootGroup_le_tailUnipotent hneg hx)))
        (inv_mem (hN n.2))
  · rintro _ (hb | ⟨i, rfl⟩)
    · exact tailBorel_le hb
    · exact tailWeylElt_mem a₀ i

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
