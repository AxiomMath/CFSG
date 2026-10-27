module

public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1CaseII
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Eigen
public import CFSG.ClassicalGroups.Orthogonal.SiegelRT1Additive

public section

namespace CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.ClassicalGroups.Alternating CFSG.HardMathSupport.Kantor79 QuadraticMap Module

section Generic

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N]
  {BN : LinearMap.BilinForm K N}

theorem gsp_app_ne_zero (g : Gsp BN) {x : N} (hx : x ≠ 0) : g.app x ≠ 0 := by
  intro h
  apply hx
  rw [← Gsp.app_inv_app g x, h, Gsp.map_zero']

end Generic

section AxisMap

variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {N : Type*} [AddCommGroup N] [Module K N] [FiniteDimensional K N]
  {BN : LinearMap.BilinForm K N}
  {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {hBN : BN.IsAlt} {Qf : QuadraticForm K V} {ρ : Gsp BN →* (V ≃ₗ[K] V)}

variable (hs : Setting hBN Qf ρ)

include hs

theorem axisMap_smul {a : N} (ha : a ≠ 0) {u : V} {σ : K ≃+* K} {F : N →+ V} (hFa : F a = u)
    (hF : ∀ (g : Gsp BN) (x : N), F (g.app x) = ρ g (F x))
    (hσ : ∀ (g : Gsp BN) (c : K), g.app a = c • a → ρ g u = σ c • u) (c : K) (x : N) :
    F (c • x) = σ c • F x := by
  by_cases hx : x = 0
  · subst hx
    simp
  by_cases hc : c = 0
  · subst hc
    simp
  obtain ⟨g, rfl⟩ := CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hs.nondegN ha hx
  obtain ⟨h, hh⟩ := CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hs.nondegN ha
    (smul_ne_zero hc ha)
  have e : c • g.app a = (g * h).app a := by
    rw [Gsp.app_mul, hh, Gsp.map_smul]
  rw [e, hF, hF, map_mul, LinearEquiv.mul_apply, hFa, hσ h c hh, map_smul]

variable (hII : ∀ a c : N, LinearIndependent K ![a, c] → BN a c = 0 →
  axis hBN ρ a 1 ⊓ axis hBN ρ c 1 = ⊥)

include hII

theorem exists_equivariantMap {a : N} (ha : a ≠ 0) {u : V} (hu : u ∈ rootSpace hBN ρ a) :
    ∃ F : N → V, F 0 = 0 ∧ F a = u ∧ ∀ (g : Gsp BN) (x : N), F (g.app x) = ρ g (F x) := by
  classical
  have hex : ∀ x : N, x ≠ 0 → ∃ g : Gsp BN, g.app a = x := fun x hx =>
    CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hs.nondegN ha hx
  let F : N → V := fun x => if hx : x = 0 then 0 else ρ (Classical.choose (hex x hx)) u
  have hF0 : F 0 = 0 := by simp [F]
  have key : ∀ g : Gsp BN, F (g.app a) = ρ g u := by
    intro g
    have hga : g.app a ≠ 0 := gsp_app_ne_zero g ha
    show (if hx : g.app a = 0 then 0 else ρ (Classical.choose (hex _ hx)) u) = ρ g u
    rw [dif_neg hga]
    set g' := Classical.choose (hex _ hga) with hg'def
    have hg' : g'.app a = g.app a := Classical.choose_spec (hex _ hga)
    have hfix : (g'⁻¹ * g).app a = a := by rw [Gsp.app_mul, ← hg', Gsp.app_inv_app]
    have h2 : ρ (g'⁻¹ * g) u = u := apply_eq_of_app_eq_of_mem_rootSpace hs hII hfix hu
    calc ρ g' u = ρ g' (ρ (g'⁻¹ * g) u) := by rw [h2]
      _ = ρ g u := by rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
  refine ⟨F, hF0, ?_, ?_⟩
  · simpa [Gsp.app_one] using key 1
  · intro g x
    by_cases hx : x = 0
    · subst hx
      rw [Gsp.map_zero', hF0, map_zero]
    · obtain ⟨k, rfl⟩ := hex x hx
      rw [← Gsp.app_mul, key (g * k), key k, map_mul]
      rfl

theorem exists_axisMap {a : N} (ha : a ≠ 0) {u : V} (hu : u ∈ rootSpace hBN ρ a) :
    ∃ F : N →+ V, F a = u ∧ ∀ (g : Gsp BN) (x : N), F (g.app x) = ρ g (F x) := by
  obtain ⟨F, hF0, hFa, hFeq⟩ := exists_equivariantMap hs hII ha hu
  have hadd : ∀ x y : N, BN x y ≠ 0 → F (x + y) = F x + F y := by
    intro x y hxy
    set κ : K := BN x y with hκ
    obtain ⟨b, hb⟩ : ∃ b : N, BN a b = 1 := by
      obtain ⟨z, hz⟩ : ∃ z, BN a z ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact ha (hs.nondegN.1 a hcon)
      exact ⟨(BN a z)⁻¹ • z, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hz]⟩
    have hab : BN a b ≠ 0 := by
      rw [hb]
      exact one_ne_zero
    have hrel : κ⁻¹ * κ * BN a b ^ 2 = 1 := by
      rw [hb, inv_mul_cancel₀ hxy]
      norm_num
    obtain ⟨hsub, -⟩ := rootSpace_sub_one_eq hs hII hab hxy hrel hu
    have hform : BN a (κ • b) = κ := by
      rw [map_smul, smul_eq_mul, hb, mul_one]
    obtain ⟨g, hga, hgb⟩ := exists_gsp_apply_eq_of_form_eq hBN hs.nondegN hxy hform rfl
    have e1 : (Tsp hBN b κ).app a = a + κ • b := by
      rw [Tsp_app, hb, mul_one]
    have e2 : (Tsp hBN a κ⁻¹ * Tsp hBN b κ * Tsp hBN a κ⁻¹).app a = κ • b := by
      rw [app_Tsp_mul_Tsp_mul_Tsp_left hBN hrel, hb, mul_one]
    have h1 : F (a + κ • b) = F a + F (κ • b) := by
      calc F (a + κ • b) = F ((Tsp hBN b κ).app a) := by rw [e1]
        _ = ρ (Tsp hBN b κ) u := by rw [hFeq, hFa]
        _ = u + ρ (Tsp hBN a κ⁻¹ * Tsp hBN b κ * Tsp hBN a κ⁻¹) u := by
          rw [← hsub]
          abel
        _ = F a + F (κ • b) := by rw [hFa, ← e2, hFeq, hFa]
    have hxy' : x + y = g.app (a + κ • b) := by
      rw [Gsp.map_add, hga, hgb]
    rw [hxy', hFeq, h1, map_add, ← hFeq, ← hFeq, hga, hgb]
  have hadd' := add_of_add_of_form_ne_zero hBN hs.nondegN hs.card F hF0 hadd
  exact ⟨AddMonoidHom.mk' F fun x y => hadd' x y, hFa, hFeq⟩

theorem exists_twisted_basis {a : N} (ha : a ≠ 0) :
    ∃ (u₁ u₂ : V) (σ₁ σ₂ : K ≃+* K), u₁ ∈ rootSpace hBN ρ a ∧ u₂ ∈ rootSpace hBN ρ a ∧
      LinearIndependent K ![u₁, u₂] ∧
      ∀ (g : Gsp BN) (c : K), g.app a = c • a → ρ g u₁ = σ₁ c • u₁ ∧ ρ g u₂ = σ₂ c • u₂ := by
  classical
  have hAfin : finrank K (rootSpace hBN ρ a) = 2 := (finrank_rootSpace hs hII ha).1
  have hex : ∀ ν : K, ν ≠ 0 → ∃ h : Gsp BN, h.app a = ν • a := fun ν hν =>
    CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq hBN hs.nondegN ha (smul_ne_zero hν ha)
  have hmaps : ∀ (h : Gsp BN) (ν : K), ν ≠ 0 → h.app a = ν • a →
      ∀ u ∈ rootSpace hBN ρ a, ρ h u ∈ rootSpace hBN ρ a := by
    intro h ν hν hh u hu
    have hmem := Submodule.mem_map_of_mem (f := (ρ h : V →ₗ[K] V)) hu
    rwa [map_rootSpace_eq, hh, rootSpace_smul_of_ne_zero hν] at hmem
  have hwell : ∀ (h h' : Gsp BN), h.app a = h'.app a →
      ∀ u ∈ rootSpace hBN ρ a, ρ h u = ρ h' u := by
    intro h h' hh u hu
    have hfix : (h'⁻¹ * h).app a = a := by rw [Gsp.app_mul, hh, Gsp.app_inv_app]
    have h2 := apply_eq_of_app_eq_of_mem_rootSpace hs hII hfix hu
    calc ρ h u = ρ h' (ρ (h'⁻¹ * h) u) := by
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel_left]
      _ = ρ h' u := by rw [h2]
  let f₀ : K → Module.End K (rootSpace hBN ρ a) := fun ν =>
    if hν : ν = 0 then 0 else
      (ρ (Classical.choose (hex ν hν)) : V →ₗ[K] V).restrict
        (hmaps _ ν hν (Classical.choose_spec (hex ν hν)))
  have hf_zero : f₀ 0 = 0 := by simp [f₀]
  have hf_apply : ∀ (ν : K) (hν : ν ≠ 0) (h : Gsp BN), h.app a = ν • a →
      ∀ u : rootSpace hBN ρ a, ((f₀ ν u : rootSpace hBN ρ a) : V) = ρ h (u : V) := by
    intro ν hν h hh u
    simp only [f₀, dif_neg hν]
    rw [LinearMap.restrict_coe_apply]
    exact hwell _ _ (by rw [Classical.choose_spec (hex ν hν), hh]) u u.2
  have hFval : ∀ (u : rootSpace hBN ρ a) (F : N →+ V), F a = u →
      (∀ (g : Gsp BN) (x : N), F (g.app x) = ρ g (F x)) →
      ∀ ν : K, F (ν • a) = ((f₀ ν u : rootSpace hBN ρ a) : V) := by
    intro u F hFa hF ν
    by_cases hν : ν = 0
    · subst hν
      simp [hf_zero]
    · obtain ⟨h, hh⟩ := hex ν hν
      rw [← hh, hF, hFa, hf_apply ν hν h hh u]
  have hadd : ∀ ν ν' : K, f₀ (ν + ν') = f₀ ν + f₀ ν' := by
    intro ν ν'
    refine LinearMap.ext fun u => Subtype.ext ?_
    obtain ⟨F, hFa, hF⟩ := exists_axisMap hs hII ha u.2
    have h1 := hFval u F hFa hF (ν + ν')
    have h2 := hFval u F hFa hF ν
    have h3 := hFval u F hFa hF ν'
    rw [LinearMap.add_apply, Submodule.coe_add, ← h1, add_smul, map_add, h2, h3]
  have hmul : ∀ ν ν' : K, f₀ (ν * ν') = f₀ ν * f₀ ν' := by
    intro ν ν'
    by_cases hν : ν = 0
    · subst hν
      simp [hf_zero]
    by_cases hν' : ν' = 0
    · subst hν'
      simp [hf_zero]
    obtain ⟨h, hh⟩ := hex ν hν
    obtain ⟨h', hh'⟩ := hex ν' hν'
    have hhh : (h * h').app a = (ν * ν') • a := by
      rw [Gsp.app_mul, hh', Gsp.map_smul, hh, smul_smul, mul_comm]
    refine LinearMap.ext fun u => Subtype.ext ?_
    rw [hf_apply (ν * ν') (mul_ne_zero hν hν') (h * h') hhh u, Module.End.mul_apply,
      hf_apply ν hν h hh (f₀ ν' u), hf_apply ν' hν' h' hh' u, map_mul, LinearEquiv.mul_apply]
  have hone : f₀ 1 = 1 := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    rw [hf_apply 1 one_ne_zero 1 (by rw [Gsp.app_one, one_smul]) u]
    simp
  let f : K →+* Module.End K (rootSpace hBN ρ a) :=
    { toFun := f₀
      map_one' := hone
      map_mul' := hmul
      map_zero' := hf_zero
      map_add' := hadd }
  obtain ⟨u₁, u₂, σ₁, σ₂, hli, hσ⟩ := exists_twisted_eigenbasis hAfin f
  refine ⟨u₁, u₂, σ₁, σ₂, u₁.2, u₂.2, ?_, ?_⟩
  · have h := hli.map' (rootSpace hBN ρ a).subtype (Submodule.ker_subtype _)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  · intro g c hg
    have hc : c ≠ 0 := by
      rintro rfl
      exact gsp_app_ne_zero g ha (by rw [hg, zero_smul])
    refine ⟨?_, ?_⟩
    · have h1 := hf_apply c hc g hg u₁
      have h2 : f₀ c u₁ = σ₁ c • u₁ := (hσ c).1
      rw [← h1, h2]
      rfl
    · have h1 := hf_apply c hc g hg u₂
      have h2 : f₀ c u₂ = σ₂ c • u₂ := (hσ c).2
      rw [← h1, h2]
      rfl

end AxisMap

end CFSG.ClassicalGroups.Orthogonal.SiegelRT1
