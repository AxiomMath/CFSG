module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeTwNotAll24CentreD5Kind
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacShape

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KSGen

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6UniqAbs
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSConn
open Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000


section Position

@[expose] def d5NodesA : Set (Fin Tag.E6.rank) := {j | 1 ≤ j.val}

@[expose] def d5NodesB : Set (Fin Tag.E6.rank) := {j | j.val ≤ 4}

@[expose] def d5WordC : List (Fin Tag.E6.rank) := [0, 2, 3, 4, 1, 3, 2, 0]

theorem rootsOf_sD5a : kacE6.rootsOf (↑sD5a : Set (Option (Fin Tag.E6.rank))) =
    parabolicRoots Tag.E6 d5NodesA :=
  rootsOf_eq_parabolicRoots kacE6 facts_E6 (by decide) (fun j => by
    revert j
    show ∀ j : Fin Tag.E6.rank, (some j ∈ sD5a ↔ 1 ≤ j.val)
    decide)

theorem rootsOf_sD5b : kacE6.rootsOf (↑sD5b : Set (Option (Fin Tag.E6.rank))) =
    parabolicRoots Tag.E6 d5NodesB :=
  rootsOf_eq_parabolicRoots kacE6 facts_E6 (by decide) (fun j => by
    revert j
    show ∀ j : Fin Tag.E6.rank, (some j ∈ sD5b ↔ j.val ≤ 4)
    decide)

theorem sD5c_check : ∀ γ ∈ R6, kacTest θ6 sD5c γ ↔
    (wordMat Tag.E6 d5WordC *ᵥ γ) 0 = 0 := by
  decide +kernel

theorem eq_zero_of_notMem_d5NodesA {i : Fin Tag.E6.rank} (hi : i ∉ d5NodesA) : i = 0 := by
  rw [d5NodesA, Set.mem_setOf_eq, not_le] at hi
  have h0 : i.val = 0 := by omega
  exact Fin.ext (by rw [h0]; rfl)

theorem rootsOf_sD5c :
    (fun α => (coxeterSystem Tag.E6).wordProd d5WordC • α) ''
        kacE6.rootsOf (↑sD5c : Set (Option (Fin Tag.E6.rank))) =
      parabolicRoots Tag.E6 d5NodesA := by
  set u := (coxeterSystem Tag.E6).wordProd d5WordC with hu
  have hmat : ∀ γ, u • γ = wordMat Tag.E6 d5WordC *ᵥ γ := fun γ =>
    wordProd_smul_eq_wordMat_mulVec Tag.E6 d5WordC γ
  ext β
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨hr, hk⟩ := (mem_rootsOf_iff kacE6 facts_E6 ⟨some 0, by decide⟩).1 hγ
    refine ⟨IsRoot.smul hr u, fun i hi => ?_⟩
    have h := (sD5c_check γ (mem_R6_of_isRoot hr)).1 hk
    show (u • γ) i = 0
    rw [eq_zero_of_notMem_d5NodesA hi, hmat]
    exact h
  · rintro ⟨hβ, hvan⟩
    refine ⟨u⁻¹ • β, ?_, smul_inv_smul u β⟩
    have hr : IsRoot Tag.E6 (u⁻¹ • β) := IsRoot.smul hβ u⁻¹
    refine (mem_rootsOf_iff kacE6 facts_E6 ⟨some 0, by decide⟩).2 ⟨hr, ?_⟩
    refine (sD5c_check _ (mem_R6_of_isRoot hr)).2 ?_
    rw [← hmat, smul_inv_smul]
    exact hvan 0 (fun h0 => by
      rw [d5NodesA, Set.mem_setOf_eq] at h0
      exact absurd h0 (by decide))

end Position

section Class

variable {L : Type} [Field L] [IsAlgClosed L]

theorem d5_position (h3 : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.E6.rank → Lˣ}
    (hap : ∀ i, a i ^ 3 = 1) (hk : (kernelRoots (rootCharHom a)).ncard = 40) :
    ∃ (v : WeylGroup Tag.E6) (J : Set (Fin Tag.E6.rank)),
      (J = d5NodesA ∨ J = d5NodesB) ∧
      kernelRoots (rootCharHom a) = (fun α => v • α) '' parabolicRoots Tag.E6 J := by
  classical
  have hfin : (kernelRoots (rootCharHom a)).Finite :=
    (CFSG.Blueprint.Chevalley.finite_setOf_isRoot Tag.E6).subset fun γ hγ => hγ.1
  obtain ⟨α, hα⟩ : (kernelRoots (rootCharHom a)).Nonempty := by
    rw [← Set.ncard_pos hfin, hk]
    norm_num
  let i : KernelComponent (rootCharHom a) := ⟦⟨α, hα⟩⟧
  obtain ⟨v, C, hC, hΨ, hn, -⟩ := d5_class_data h3 hap hk i
  have hΨk : componentRoots (rootCharHom a) i = kernelRoots (rootCharHom a) :=
    Set.eq_of_subset_of_ncard_le (fun γ hγ => hγ.1) (by rw [hk, hn]) hfin
  rw [hΨk] at hΨ
  rcases hC with rfl | rfl | rfl
  · exact ⟨v, d5NodesA, Or.inl rfl, by rw [hΨ, rootsOf_sD5a]⟩
  · exact ⟨v, d5NodesB, Or.inr rfl, by rw [hΨ, rootsOf_sD5b]⟩
  · refine ⟨v * ((coxeterSystem Tag.E6).wordProd d5WordC)⁻¹, d5NodesA, Or.inl rfl, ?_⟩
    rw [hΨ, ← rootsOf_sD5c, Set.image_image]
    refine Set.image_congr fun γ _ => ?_
    rw [mul_smul, inv_smul_smul]

end Class

end KSGen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three
