module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition

public section

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

namespace CFSG.HardMathSupport.Curtis.Coordinator.SPLCell

section Mult

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [Module.Finite K V]

omit [Module.Finite K V] in
theorem aeval_mem_of_stable (z : Module.End K V) (M : Submodule K V) (hz : ∀ v ∈ M, z v ∈ M)
    (q : K[X]) {v : V} (hv : v ∈ M) : aeval z q v ∈ M := by
  have hpow : ∀ (m : ℕ) (w : V), w ∈ M → (z ^ m) w ∈ M := by
    intro m
    induction m with
    | zero => intro w hw; simpa using hw
    | succ m ih =>
      intro w hw
      rw [pow_succ', Module.End.mul_apply]
      exact hz _ (ih w hw)
  induction q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, LinearMap.add_apply]; exact M.add_mem hp hq
  | monomial m a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact M.smul_mem a (hpow m v hv)

theorem five_le_primaryMultiplicity (z : Module.End K V) {h : K[X]} (hirr : Irreducible h)
    (M : Fin 5 → Submodule K V) (hne : ∀ i, M i ≠ ⊥)
    (hh : ∀ i, ∀ v ∈ M i, aeval z h v = 0) (hz : ∀ i, ∀ v ∈ M i, z v ∈ M i)
    (hind : iSupIndep M) : 5 ≤ primaryMultiplicity z h := by
  have : Fact (Irreducible h) := ⟨hirr⟩
  choose v hvM hv0 using fun i => Submodule.exists_mem_ne_zero_of_ne_bot (hne i)
  let u : Fin 5 → primaryComponent z h := fun i =>
    ⟨v i, mem_primaryComponent.2 (hh i (v i) (hvM i))⟩
  have hsmul : ∀ (j : Fin 5) (e : AdjoinRoot h), (((e • u j : primaryComponent z h)) : V) ∈ M j := by
    intro j e
    induction e using AdjoinRoot.induction_on with
    | ih q =>
      rw [coe_mk_smul_primaryComponent]
      exact aeval_mem_of_stable z (M j) (hz j) q (hvM j)
  have hlin : LinearIndependent (AdjoinRoot h) u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hsum : ∑ j : Fin 5, (((g j • u j : primaryComponent z h)) : V) = 0 := by
      have := congrArg (fun w : primaryComponent z h => (w : V)) hg
      simpa [Submodule.coe_sum] using this
    have hzero := (iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero M).1 hind Finset.univ
      (fun j => (((g j • u j : primaryComponent z h)) : V)) (fun j _ => hsmul j (g j)) hsum i
      (Finset.mem_univ i)
    have h1 : g i • u i = 0 := Subtype.ext hzero
    rcases smul_eq_zero.1 h1 with h2 | h2
    · exact h2
    · exact absurd (congrArg Subtype.val h2) (hv0 i)
  have := hlin.fintype_card_le_finrank
  simpa using this

omit [Module.Finite K V] in
theorem dvd_minpoly_of_aeval_eq_zero (z : Module.End K V) {h : K[X]} (hirr : Irreducible h)
    {v : V} (hv : v ≠ 0) (hh : aeval z h v = 0) : h ∣ minpoly K z := by
  by_contra hnd
  obtain ⟨a, b, hab⟩ := (Irreducible.coprime_iff_not_dvd hirr).2 hnd
  have h1 := congrArg (fun q : K[X] => aeval z q v) hab
  simp only [map_add, map_mul, LinearMap.add_apply, Module.End.mul_apply, hh, map_zero,
    minpoly.aeval, LinearMap.zero_apply, add_zero, map_one, Module.End.one_apply] at h1
  exact hv h1.symm

end Mult

end CFSG.HardMathSupport.Curtis.Coordinator.SPLCell
