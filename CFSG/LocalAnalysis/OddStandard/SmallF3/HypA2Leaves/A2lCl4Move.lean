module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2Leaves.A2lCl4Eps
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple

public section

namespace CFSG.OddStandard.SmallF3.HypA2Leaves

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem cl24_exists_move (hQ : (polarBilin Q).Nondegenerate) {P₁ P₂ : HypPair Q}
    (h : P₁.Orth P₂) {X : Type*} [MulAction (elementaryGroup Q) X]
    [MulAction.IsPretransitive (elementaryGroup Q) X] (hX : 2 ≤ Nat.card X) :
    ∃ (y : X) (w : P₁.perp), cl24_eps P₁ w • y ≠ y := by
  by_contra hcon
  push_neg at hcon
  have hsub : ((rootGroup Q P₁.e).subgroupOf (elementaryGroup Q) : Set (elementaryGroup Q)) ⊆
      (MulAction.toPermHom (elementaryGroup Q) X).ker := by
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hg
    obtain ⟨w, hw⟩ := (cl24_mem_rootGroup_iff P₁).1 hg
    have hgy : g = cl24_eps P₁ w := Subtype.ext hw.symm
    have hfix : (MulAction.toPermHom (elementaryGroup Q) X) g = 1 := by
      apply Equiv.ext
      intro y
      rw [hgy]
      change cl24_eps P₁ w • y = y
      exact hcon y w
    exact MonoidHom.mem_ker.mpr hfix
  have hclosure := Subgroup.normalClosure_le_normal hsub
  have htop := normalClosure_rootGroup_eq_top hQ h
  have hker : (MulAction.toPermHom (elementaryGroup Q) X).ker = ⊤ :=
    eq_top_iff.mpr (by rwa [htop] at hclosure)
  have htriv : ∀ (g : elementaryGroup Q) (y : X), g • y = y := by
    intro g y
    have hg : g ∈ (MulAction.toPermHom (elementaryGroup Q) X).ker := by
      rw [hker]; exact Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hg
    have h2 := congrArg (fun e : Equiv.Perm X => e y) hg
    change g • y = y at h2
    exact h2
  haveI : Subsingleton X := ⟨fun x y => by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (elementaryGroup Q) x y
    rw [← hg, htriv g x]⟩
  have hcard : Nat.card X ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr inferInstance
  omega

end CFSG.OddStandard.SmallF3.HypA2Leaves
