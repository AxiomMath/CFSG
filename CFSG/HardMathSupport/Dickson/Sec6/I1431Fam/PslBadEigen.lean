module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LinearBlocks

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section Eigen

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem eigen_twist_false (G : Module.End K V) (hG : Function.Injective G)
    (hV : Module.finrank K V ≤ 3) {M : V →ₗ[K] V} (hM : Function.Injective M) {μ : K}
    (hμ : μ ≠ 1) (hMG : ∀ v, G (M v) = μ • M (G v)) {c : K}
    (hc : 2 ≤ Module.finrank K (Module.End.eigenspace G c)) : False := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    have : Module.End.eigenspace G 0 = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Module.End.mem_eigenspace_iff, zero_smul] at hv
      have := hG (hv.trans (map_zero G).symm)
      simp [this]
    rw [this, finrank_bot] at hc
    omega
  have hmap : ∀ v ∈ Module.End.eigenspace G c, M v ∈ Module.End.eigenspace G (μ * c) := by
    intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hMG, hv, map_smul, smul_smul]
  let M' : Module.End.eigenspace G c →ₗ[K] Module.End.eigenspace G (μ * c) :=
    M.restrict hmap
  have hM' : Function.Injective M' := fun a b hab =>
    Subtype.ext (hM (congrArg Subtype.val hab))
  have h2 : 2 ≤ Module.finrank K (Module.End.eigenspace G (μ * c)) :=
    hc.trans (LinearMap.finrank_le_finrank_of_injective hM')
  have hne : μ * c ≠ c := by
    intro h
    apply hμ
    have : (μ - 1) * c = 0 := by rw [sub_mul, h, one_mul, sub_self]
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd h1 hc0
  have hdisj : Disjoint (Module.End.eigenspace G c) (Module.End.eigenspace G (μ * c)) := by
    exact (Module.End.eigenspaces_iSupIndep G).pairwiseDisjoint (Ne.symm hne)
  have := Submodule.finrank_add_finrank_le_of_disjoint hdisj
  omega

end Eigen

section Good

variable {K : Type*} [Field K] [Finite K]

theorem exists_eigenspace_two_of_good {A : GL (Fin 3) K}
    (hsq : Squarefree (minpoly K (glA A : Module.End K (Fin 3 → K)))) {h : K[X]}
    (hh : h ∈ primaryFactors (glA A : Module.End K (Fin 3 → K))) (hgood : IsGoodFactor A h) :
    ∃ c : K, 2 ≤ Module.finrank K
      (Module.End.eigenspace (glA A : Module.End K (Fin 3 → K)) c) := by
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm2 : 2 ≤ primaryMultiplicity (glA A : Module.End K (Fin 3 → K)) h := by
    rcases hgood with h3 | ⟨h2, -⟩
    · omega
    · exact h2
  have hdeg : 1 ≤ h.natDegree := (Fact.out : Irreducible h).natDegree_pos
  have hrk := finrank_primaryComponent (glA A : Module.End K (Fin 3 → K)) (a := h)
  have hle : Module.finrank K (primaryComponent (glA A : Module.End K (Fin 3 → K)) h) ≤ 3 := by
    have := Submodule.finrank_le (primaryComponent (glA A : Module.End K (Fin 3 → K)) h)
    simpa using this
  have hd1 : h.natDegree = 1 := by
    rw [hrk] at hle
    by_contra hne
    have : 2 ≤ h.natDegree := by omega
    nlinarith
  have hmonic := monic_of_mem_primaryFactors hh
  have hform : h = X + C (h.coeff 0) := hmonic.eq_X_add_C hd1
  refine ⟨-(h.coeff 0), ?_⟩
  have hcomp : primaryComponent (glA A : Module.End K (Fin 3 → K)) h =
      Module.End.eigenspace (glA A : Module.End K (Fin 3 → K)) (-(h.coeff 0)) := by
    ext v
    rw [mem_primaryComponent, Module.End.mem_eigenspace_iff]
    conv_lhs => rw [hform]
    simp only [map_add, aeval_X, aeval_C, LinearMap.add_apply, Module.algebraMap_end_apply]
    constructor
    · intro h0
      rw [neg_smul]
      exact eq_neg_of_add_eq_zero_left h0
    · intro h0
      rw [neg_smul] at h0
      rw [h0]
      simp
  rw [← hcomp, hrk, hd1, one_mul]
  exact hm2

end Good

end CFSG.HardMathSupport.Dickson.Sec6.I1431
