module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Solomon.LocalBalance.I1433.F4TwoRoots

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped Matrix

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

theorem prod_rank_F4 {M : Type*} [CommMonoid M] (f : Fin Tag.F4.rank → M) :
    ∏ i, f i = f (idx 0) * f (idx 1) * f (idx 2) * f (idx 3) := by
  have h := Fintype.prod_equiv (finCongr rank_F4) f
    (fun i : Fin 4 => f ((finCongr rank_F4).symm i)) (fun i => by simp)
  rw [h, Fin.prod_univ_four]
  rfl

section Param

variable {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]

theorem exists_primitive_cube_root :
    ∃ ω : Lˣ, ω ^ 3 = 1 ∧ ω ≠ 1 ∧ (ω : L) ^ 2 + (ω : L) + 1 = 0 := by
  have hdeg : (Polynomial.C (1 : L) * Polynomial.X ^ 2 + Polynomial.C (1 : L) * Polynomial.X +
      Polynomial.C (1 : L)).degree ≠ 0 := by
    rw [Polynomial.degree_quadratic one_ne_zero]
    norm_num
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  simp only [Polynomial.IsRoot.def, map_one, one_mul, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one] at hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  have hz3 : z ^ 3 = 1 := by
    have : z ^ 3 - 1 = (z - 1) * (z ^ 2 + z + 1) := by ring
    rw [hz, mul_zero] at this
    exact sub_eq_zero.1 this
  have hz1 : z ≠ 1 := by
    rintro rfl
    have h3 : (3 : L) = 0 := by linear_combination hz
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (1 : L) = 0 := by linear_combination h3 - h2
    exact one_ne_zero this
  refine ⟨Units.mk0 z hz0, Units.ext (by simpa using hz3), fun h => hz1 (by simpa using congrArg Units.val h), ?_⟩
  simpa using hz

theorem eq_pow_of_cube_eq_one {ω : Lˣ} (hω : (ω : L) ^ 2 + (ω : L) + 1 = 0) (hω3 : ω ^ 3 = 1)
    {u : Lˣ} (hu : u ^ 3 = 1) : ∃ n : ℕ, n < 3 ∧ u = ω ^ n := by
  have hω3' : (ω : L) ^ 3 = 1 := by simpa using congrArg Units.val hω3
  have hu3 : (u : L) ^ 3 = 1 := by simpa using congrArg Units.val hu
  have hprod : ((u : L) - 1) * (((u : L) - ω) * ((u : L) - (ω : L) ^ 2)) = 0 := by
    linear_combination hu3 + ((u : L) - (u : L) ^ 2) * hω + ((u : L) - 1) * hω3'
  rcases mul_eq_zero.1 hprod with h1 | h2
  · exact ⟨0, by norm_num, Units.ext (by simpa [sub_eq_zero] using h1)⟩
  · rcases mul_eq_zero.1 h2 with h2 | h3
    · exact ⟨1, by norm_num, Units.ext (by simpa [sub_eq_zero] using h2)⟩
    · exact ⟨2, by norm_num, Units.ext (by simpa [sub_eq_zero] using h3)⟩

theorem exists_omega_param {a : Fin Tag.F4.rank → Lˣ} (hap : ∀ i, a i ^ 3 = 1) :
    ∃ (ω : Lˣ) (k : Fin Tag.F4.rank → ℕ), ω ^ 3 = 1 ∧ ω ≠ 1 ∧ (∀ i, k i < 3) ∧
      ∀ i, a i = ω ^ k i := by
  obtain ⟨ω, hω3, hω1, hω⟩ := exists_primitive_cube_root (L := L)
  have h : ∀ i, ∃ n : ℕ, n < 3 ∧ a i = ω ^ n := fun i => eq_pow_of_cube_eq_one hω hω3 (hap i)
  choose k hk hak using h
  exact ⟨ω, k, hω3, hω1, hk, hak⟩

end Param

section Chars

variable {L : Type} [Field L]

theorem rootChar_eq_pow_kdot {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}
    (hak : ∀ i, a i = ω ^ k i) (γ : V4) : rootChar a γ = ω ^ kdot k γ := by
  simp only [rootChar, prod_rank_F4, hak, kdot, zpow_add, ← zpow_natCast, ← zpow_mul]

theorem rootChar_eq_one_iff {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ} {k : Fin Tag.F4.rank → ℕ}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i) (γ : V4) :
    rootChar a γ = 1 ↔ kdot k γ % 3 = 0 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  rw [rootChar_eq_pow_kdot hak, ← orderOf_dvd_iff_zpow_eq_one, hord]
  omega

end Chars

section Classes


theorem componentRoots_eq_sameLength {L : Type} [Field L] {a : Fin Tag.F4.rank → Lˣ} {ω : Lˣ}
    {k : Fin Tag.F4.rank → ℕ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) (hak : ∀ i, a i = ω ^ k i)
    (hk : KernelA2A2 k) {γ₀ : V4} (hγ₀ : γ₀ ∈ kernelRoots (rootCharHom a)) :
    componentRoots (rootCharHom a)
        (⟦⟨γ₀, hγ₀⟩⟧ : KernelComponent (rootCharHom a)) =
      {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 γ₀ γ₀} := by
  have hker : ∀ γ ∈ kernelRoots (rootCharHom a), kdot k γ % 3 = 0 := fun γ hγ =>
    (rootChar_eq_one_iff hω3 hω1 hak γ).1 hγ.2
  ext γ
  constructor
  · rintro ⟨hγ, heq⟩
    refine ⟨hγ, ?_⟩
    have hrel := Quotient.exact heq
    have key : ∀ x y : kernelRoots (rootCharHom a),
        Relation.EqvGen (fun α β : kernelRoots (rootCharHom a) =>
          (α : V4) ⬝ᵥ (Tag.symmetrizedCartan Tag.F4 *ᵥ (β : V4)) ≠ 0) x y →
          ipF4 (x : V4) x = ipF4 (y : V4) y := by
      intro x y hxy
      induction hxy with
      | rel x y hxy =>
        by_contra hne
        apply hxy
        rw [dotProduct_mulVec_eq_iform, iform_F4]
        exact hk.diff x y x.2.1 y.2.1 (hker x x.2) (hker y y.2) hne
      | refl x => rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    exact key ⟨γ, hγ⟩ ⟨γ₀, hγ₀⟩ hrel
  · rintro ⟨hγ, hlen⟩
    refine ⟨hγ, ?_⟩
    by_cases hne : γ = γ₀
    · subst hne
      rfl
    · exact mk_eq_of_iform_ne_zero (α := ⟨γ, hγ⟩) (β := ⟨γ₀, hγ₀⟩) (by
        show iform γ γ₀ ≠ 0
        rw [iform_F4]
        exact hk.same γ γ₀ hγ.1 hγ₀.1 (hker γ hγ) (hker γ₀ hγ₀) hlen)

end Classes

section Rho

variable
  {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

theorem rho_image_sameLength (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) {γ₀ : V4}
    (hfin : {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 γ₀ γ₀}.Finite) :
    (S.ρ : V4 → V4) '' {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 γ₀ γ₀} =
      {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 γ₀ γ₀} := by
  have hsub : (S.ρ : V4 → V4) '' {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 γ₀ γ₀} ⊆
      {γ | γ ∈ kernelRoots (rootCharHom a) ∧ ipF4 γ γ = ipF4 γ₀ γ₀} := by
    rintro _ ⟨γ, ⟨hγ, hlen⟩, rfl⟩
    refine ⟨outer_rho_mem_kernelRoots S hT hγ, ?_⟩
    have h := iform_rho S γ γ
    rw [iform_F4, iform_F4] at h
    rw [h, hlen]
  refine Set.eq_of_subset_of_ncard_le hsub ?_ hfin
  rw [Set.ncard_image_of_injective _ S.ρ.injective]

theorem componentOrbitLength_eq_one (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hT : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (hρ : (S.ρ : V4 → V4) '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) i) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 := by
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hT i
  refine le_antisymm ?_ hs0
  exact Nat.sInf_le ⟨Nat.one_pos, by simpa using hρ⟩

end Rho

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433


