module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.F4ThreeLangInner

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups

set_option linter.unusedSectionVars false


variable {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup τ L p)
  {w : WeylGroup τ} (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ) {a : Fin τ.rank → Lˣ}
  (hE : rootDiagUnit τ a ∈ S.E)

include hE in
theorem steinbergLang_coord_pow (i : Fin τ.rank) : a i ^ p = 1 := by
  have h := rootChar_pow_eq_one_of_mem_E S hE (isRoot_single τ i)
  rwa [Tables.T1b.rootChar_single] at h

include hρ hE in
theorem steinbergLang_rootChar_smul {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    rootChar a (w • γ) = rootChar a γ ^ S.D.q := by
  rw [← hρ γ hγ]
  exact S.frob.rootChar_eq a (Subgroup.mem_inf.1 (S.E_le hE)).1 γ hγ

include hρ hE in
theorem steinbergLang_mem_kernelReflectionGroup_one
    (hst : ∀ b : Fin τ.rank → Lˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    (hq : S.D.q % p = 1) : w ∈ kernelReflectionGroup a := by
  refine hst a (steinbergLang_coord_pow S hE)
    (f4Three_mem_rootCharStabilizer_of_roots fun γ hγ => ?_)
  rw [steinbergLang_rootChar_smul S hρ hE hγ,
    pow_eq_pow_mod _ (rootChar_pow_eq_one_of_mem_E S hE hγ), hq, pow_one]

include hρ hE in
theorem steinbergLang_mem_kernelReflectionGroup_neg
    (hst : ∀ b : Fin τ.rank → Lˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) (hp1 : 1 ≤ p)
    (hq : S.D.q % p = p - 1) : w₀ * w ∈ kernelReflectionGroup a := by
  refine hst a (steinbergLang_coord_pow S hE)
    (f4Three_mem_rootCharStabilizer_of_roots fun γ hγ => ?_)
  have hp := rootChar_pow_eq_one_of_mem_E S hE hγ
  rw [mul_smul, hw₀, show -(w • γ) = (-1 : ℤ) • (w • γ) by rw [neg_one_smul],
    rootChar_zsmul, zpow_neg_one, steinbergLang_rootChar_smul S hρ hE hγ, pow_eq_pow_mod _ hp, hq]
  have hm : rootChar a γ ^ (p - 1) * rootChar a γ = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hp1, hp]
  rw [eq_inv_of_mul_eq_one_left hm, inv_inv]

include hρ hE in
theorem steinbergLang_twistInner_one
    (hst : ∀ b : Fin τ.rank → Lˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    (hq : S.D.q % p = 1) (i : KernelComponent (rootCharHom a)) :
    twistInner (componentRoots (rootCharHom a) i) ((S.ρ : (Fin τ.rank → ℤ) → _)^[1]) := by
  obtain ⟨u, huC, hu⟩ :=
    f4Three_exists_restrict i (steinbergLang_mem_kernelReflectionGroup_one S hρ hE hst hq)
  refine ⟨u, huC, fun γ hγ => ?_⟩
  rw [Function.iterate_one, hρ γ (isRoot_of_mem_componentRoots hγ), hu γ hγ]

include hρ hE in
theorem steinbergLang_twist_neg
    (hst : ∀ b : Fin τ.rank → Lˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u) (hp1 : 1 ≤ p)
    (hq : S.D.q % p = p - 1) (i : KernelComponent (rootCharHom a)) :
    ∃ u ∈ Subgroup.closure {s : WeylGroup τ | ∃ γ ∈ componentRoots (rootCharHom a) i,
        s = rootReflection γ},
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ = -(u • γ) := by
  obtain ⟨u, huC, hu⟩ := f4Three_exists_restrict i
    (steinbergLang_mem_kernelReflectionGroup_neg S hρ hE hst hw₀ hp1 hq)
  refine ⟨u, huC, fun γ hγ => ?_⟩
  have h := hu γ hγ
  rw [mul_smul, hw₀] at h
  rw [hρ γ (isRoot_of_mem_componentRoots hγ), ← h, neg_neg]

end CFSG.HardMathSupport.Timmesfeld.CrossChar
