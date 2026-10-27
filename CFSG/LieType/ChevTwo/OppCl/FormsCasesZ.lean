module

public import CFSG.LieType.ChevTwo.OppCl.FormsCasesDual

public section

namespace CFSG.LieType.ChevTwo.OppCl

open CFSG.Open CFSG.LieType.BorelTits

namespace FormsCases

section CaseZ

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Finite V] {H : Type} [Group H]

variable {Φ : ReflForm F V} {Sing : V → Prop} {TS : Submodule F V → Prop}
  {ρ : H →* Module.End F V} {p : ℕ} [Fact p.Prime]
  {Rh : Subgroup (Equiv.Perm V)} {X : ℕ → Submodule F V} {m : ℕ} {M W' : Submodule F V}

theorem realize_siegel_core (C : RaiseCtx Φ Sing TS ρ p Rh X m M W') (c : V →ₗ[F] V)
    (hcW' : ∀ v, c v ∈ W') (hc0 : ∀ v ∈ M ⊔ W', c v = 0)
    (hsa : ∀ u v, Φ.β (c u) v = Φ.β u (c v))
    (hdiag : EA2 Φ Sing ρ ∨ ∀ u, Φ.β u (c u) = 0) :
    ∃ u : H, ∀ v, ρ u v = v + c v := by
  haveI : FiniteDimensional F V := Module.Finite.of_finite
  have hW : Φ.IsTotallyIsotropic (X m) := C.hTS _ (C.hXts m)
  have hW' : Φ.IsTotallyIsotropic W' := C.hTS _ C.hsplit.ts_W'
  have hW'0 : ∀ x ∈ W', ∀ y ∈ W', Φ.β x y = 0 := fun x hx y hy => (Φ.mem_perp.mp (hW' hy)) x hx
  have hsing : ∀ x ∈ W', Sing x := C.hTSsing _ C.hsplit.ts_W'
  let 𝓢 : AddSubmonoid (V →ₗ[F] V) :=
    { carrier := {c' | (∀ v, c' v ∈ W') ∧ (∀ v ∈ W', c' v = 0) ∧ ∃ h : H, ∀ v, ρ h v = v + c' v}
      zero_mem' := ⟨fun v => by simp, fun v _ => by simp, 1, fun v => by simp⟩
      add_mem' := by
        rintro c₁ c₂ ⟨h₁W, h₁0, h₁, hh₁⟩ ⟨h₂W, h₂0, h₂, hh₂⟩
        refine ⟨fun v => ?_, fun v hv => ?_, h₁ * h₂, fun v => ?_⟩
        · rw [LinearMap.add_apply]
          exact add_mem (h₁W v) (h₂W v)
        · rw [LinearMap.add_apply, h₁0 v hv, h₂0 v hv, add_zero]
        · rw [map_mul, Module.End.mul_apply, hh₂, hh₁, map_add, h₁0 _ (h₂W v), add_zero,
            LinearMap.add_apply]
          abel }
  have hpair : ∀ x ∈ W', ∀ y ∈ W', ∀ g : V →ₗ[F] V,
      (∀ v, g v = Φ.β x v • y + Φ.β y v • x) → g ∈ 𝓢 := by
    intro x hx y hy g hg
    obtain ⟨h, hh⟩ := C.hE0 x y (hsing x hx) (hsing y hy) (hW'0 x hx y hy)
    refine ⟨fun v => ?_, fun v hv => ?_, h, fun v => ?_⟩
    · rw [hg]
      exact add_mem (W'.smul_mem _ hy) (W'.smul_mem _ hx)
    · rw [hg, hW'0 x hx v hv, hW'0 y hy v hv, zero_smul, zero_smul, add_zero]
    · rw [hh v, hg, sub_eq_add_neg, ← neg_smul, CharTwo.neg_eq, add_assoc]
  have htrans : EA2 Φ Sing ρ → ∀ x ∈ W', ∀ c₀ : F, Φ.σ c₀ = c₀ → ∀ g : V →ₗ[F] V,
      (∀ v, g v = (c₀ * Φ.β x v) • x) → g ∈ 𝓢 := by
    intro hE2 x hx c₀ hc₀ g hg
    obtain ⟨h, hh⟩ := hE2 x c₀ (hsing x hx) hc₀
    refine ⟨fun v => ?_, fun v hv => ?_, h, fun v => ?_⟩
    · rw [hg]
      exact W'.smul_mem _ hx
    · rw [hg, hW'0 x hx v hv, mul_zero, zero_smul]
    · rw [hh v, hg]
  obtain ⟨ι, _, _, f, e, -, he, -, -, hexp⟩ := split3_exists_dual_bases C.hσ C.hsplit hW hW'
  obtain ⟨μ, hμ⟩ : ∃ μ : ι → ι → F, ∀ k l, μ k l = Φ.β (c (f k)) (f l) := ⟨_, fun _ _ => rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : ι → ι → (V →ₗ[F] V), ∀ l k v, T l k v = Φ.β (e l) v • e k :=
    ⟨fun l k => (Φ.toDual (e l)).smulRight (e k), fun _ _ _ => rfl⟩
  have hμsymm : ∀ k l, μ l k = Φ.σ (μ k l) := by
    intro k l
    rw [hμ, hμ, hsa]
    exact C.hsymm _ _
  have hsumL : ∀ (g : ι → V) (v : V), Φ.β (∑ i, g i) v = ∑ i, Φ.β (g i) v := fun g v =>
    map_sum (AddMonoidHom.mk' (fun x => Φ.β x v) (fun a b => Φ.add_left a b v)) g Finset.univ
  have hcexp : ∀ u, c u = ∑ k, Φ.β (c (f k)) u • e k := by
    intro u
    rw [hexp (c u) (hcW' u)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsa, ← C.hsymm u (c (f k))]
  have hβexp : ∀ k u, Φ.β (c (f k)) u = ∑ l, μ k l * Φ.β (e l) u := by
    intro k u
    rw [hexp (c (f k)) (hcW' (f k)), hsumL]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Φ.smul_left, C.hσ, hμ]
  have hcsum : c = ∑ k, ∑ l, μ k l • T l k := by
    refine LinearMap.ext fun u => ?_
    rw [hcexp u, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.sum_apply, hβexp k u, Finset.sum_smul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [LinearMap.smul_apply, hT, smul_smul]
  have hJ : ∀ J : Finset ι, ∑ k ∈ J, ∑ l ∈ J, μ k l • T l k ∈ 𝓢 := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty]
      exact 𝓢.zero_mem
    | insert a J ha ih =>
      have hD : μ a a • T a a ∈ 𝓢 := by
        rcases hdiag with hE2 | h0
        · exact htrans hE2 (e a) (he a) (μ a a) (hμsymm a a).symm _ fun v => by
            rw [LinearMap.smul_apply, hT, smul_smul]
        · have h00 : μ a a = 0 := by
            rw [hμ, hsa]
            exact h0 (f a)
          rw [h00, zero_smul]
          exact 𝓢.zero_mem
      have hP : ∀ l, μ a l • T l a + μ l a • T a l ∈ 𝓢 := fun l =>
        hpair (Φ.σ (μ a l) • e l) (W'.smul_mem _ (he l)) (e a) (he a) _ fun v => by
          rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, hT, hT,
            Φ.smul_left, C.hσ, hμsymm a l, smul_smul, smul_smul, smul_smul,
            mul_comm (Φ.β (e a) v)]
      have e1 : ∑ k ∈ insert a J, ∑ l ∈ insert a J, μ k l • T l k =
          μ a a • T a a + ∑ l ∈ J, (μ a l • T l a + μ l a • T a l) +
            ∑ k ∈ J, ∑ l ∈ J, μ k l • T l k := by
        simp only [Finset.sum_insert ha, Finset.sum_add_distrib]
        abel
      rw [e1]
      exact add_mem (add_mem hD (sum_mem fun l _ => hP l)) ih
  have hc : c ∈ 𝓢 := by
    rw [hcsum]
    exact hJ Finset.univ
  obtain ⟨-, -, u, hu⟩ := hc
  exact ⟨u, hu⟩

end CaseZ

end FormsCases

end CFSG.LieType.ChevTwo.OppCl
