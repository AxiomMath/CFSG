module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81Orth.Weights

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.Cls

open CFSG.LocalAnalysis.GLTheoremA.H81Orth.Wt

variable {K : Type*} [Field K] {A : Type*} [CommGroup A] {p : ℕ}
variable {V : Type*} [AddCommGroup V] [Module K V] {σ : K →+* K}

@[expose] def IsIsomRep (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V) : Prop :=
  ∀ a x y, β (ρ a x) (ρ a y) = β x y

@[expose] def IsMaxElem (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V) (p : ℕ)
    (𝒮 : Set (V →+ V)) : Prop :=
  ∀ g : V ≃ₗ[K] V, (∀ x y, β (g x) (g y) = β x y) → (∀ a v, g (ρ a v) = ρ a (g v)) →
    (∀ s ∈ 𝒮, ∀ v, g (s v) = s (g v)) → (∀ v, (g ^ p) v = v) → ∃ a : A, ∀ v, ρ a v = g v

section Projections

variable (ρ : Representation K A V) [Finite A]
variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hp hA hpK

theorem eps_apply_of_mem (i : Option (Hyperplane A p)) {v : V}
    (hv : v ∈ weightFamily (p := p) ρ i) : ρ.asAlgebraHom (eps K A p i) v = v := by
  obtain ⟨v', rfl⟩ := hv
  rw [← Module.End.mul_apply, ((orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK).idem i).eq]

theorem eps_apply_of_mem_ne {i j : Option (Hyperplane A p)} (hij : i ≠ j) {v : V}
    (hv : v ∈ weightFamily (p := p) ρ j) : ρ.asAlgebraHom (eps K A p i) v = 0 := by
  obtain ⟨v', rfl⟩ := hv
  rw [← Module.End.mul_apply, (orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK).ortho hij,
    LinearMap.zero_apply]

theorem sum_eps_apply [Fintype (Option (Hyperplane A p))] (v : V) :
    ∑ i, ρ.asAlgebraHom (eps K A p i) v = v := by
  have h := congrArg (fun f : Module.End K V => f v) (sum_asAlgebraHom_eps ρ hp hA hpK)
  simpa [LinearMap.sum_apply] using h

theorem eps_comm_of_preserves (f : V →+ V)
    (hf : ∀ i, ∀ v ∈ weightFamily (p := p) ρ i, f v ∈ weightFamily (p := p) ρ i)
    (i : Option (Hyperplane A p)) (v : V) :
    ρ.asAlgebraHom (eps K A p i) (f v) = f (ρ.asAlgebraHom (eps K A p i) v) := by
  classical
  haveI : Fintype (Option (Hyperplane A p)) := Fintype.ofFinite _
  conv_lhs => rw [← sum_eps_apply ρ hp hA hpK v, map_sum, map_sum]
  rw [Finset.sum_eq_single i]
  · exact eps_apply_of_mem ρ hp hA hpK i (hf i _ ⟨v, rfl⟩)
  · intro j _ hji
    exact eps_apply_of_mem_ne ρ hp hA hpK (Ne.symm hji) (hf j _ ⟨v, rfl⟩)
  · intro h
    exact absurd (Finset.mem_univ i) h

end Projections

section Orthogonal

variable (β : V →ₗ[K] V →ₛₗ[σ] K) (ρ : Representation K A V) (hρ : IsIsomRep β ρ)

include hρ in
theorem apply_left (a : A) (x y : V) : β (ρ a x) y = β x (ρ a⁻¹ y) := by
  have h := hρ a x (ρ a⁻¹ y)
  rwa [Representation.self_inv_apply] at h

variable [Finite A]

include hρ in
theorem eSub_left (U : Subgroup A) (x y : V) :
    β (ρ.asAlgebraHom (eSub U) x) y = β x (ρ.asAlgebraHom (eSub U) y) := by
  haveI : Fintype U := Fintype.ofFinite U
  have hc : σ ((Nat.card U : K))⁻¹ = ((Nat.card U : K))⁻¹ := by rw [map_inv₀, map_natCast]
  rw [asAlgebraHom_eSub, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, map_smulₛₗ, hc,
    LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.sum_apply, map_sum, map_sum,
    LinearMap.sum_apply]
  congr 1
  calc ∑ u : U, β (ρ (u : A) x) y = ∑ u : U, β x (ρ ((u : A)⁻¹) y) :=
        Finset.sum_congr rfl fun u _ => apply_left β ρ hρ _ x y
    _ = ∑ u : U, β x (ρ (u : A) y) := Fintype.sum_equiv (Equiv.inv U) _ _ (fun u => by simp)

include hρ in
theorem eps_left (i : Option (Hyperplane A p)) (x y : V) :
    β (ρ.asAlgebraHom (eps K A p i) x) y = β x (ρ.asAlgebraHom (eps K A p i) y) := by
  rcases i with _ | H
  · exact eSub_left β ρ hρ ⊤ x y
  · show β (ρ.asAlgebraHom (eSub H.1 - eSub ⊤) x) y = β x (ρ.asAlgebraHom (eSub H.1 - eSub ⊤) y)
    rw [map_sub, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, LinearMap.sub_apply, map_sub,
      eSub_left β ρ hρ, eSub_left β ρ hρ]

variable (hp : p.Prime) (hA : ∀ a : A, a ^ p = 1) (hpK : (p : K) ≠ 0)

include hρ hp hA hpK in
theorem weightFamily_orthogonal {i j : Option (Hyperplane A p)} (hij : i ≠ j) {v w : V}
    (hv : v ∈ weightFamily (p := p) ρ i) (hw : w ∈ weightFamily (p := p) ρ j) : β v w = 0 := by
  obtain ⟨v', rfl⟩ := hv
  obtain ⟨w', rfl⟩ := hw
  rw [eps_left β ρ hρ i, ← Module.End.mul_apply,
    (orthogonalIdempotents_asAlgebraHom_eps ρ hp hA hpK).ortho hij, LinearMap.zero_apply,
    map_zero]

include hρ hp hA hpK in
theorem weightFamily_nondeg (hβ : β.SeparatingLeft) (i : Option (Hyperplane A p)) {v : V}
    (hv : v ∈ weightFamily (p := p) ρ i) (h : ∀ w ∈ weightFamily (p := p) ρ i, β v w = 0) :
    v = 0 := by
  refine hβ v fun w => ?_
  calc β v w = β (ρ.asAlgebraHom (eps K A p i) v) w := by rw [eps_apply_of_mem ρ hp hA hpK i hv]
    _ = β v (ρ.asAlgebraHom (eps K A p i) w) := eps_left β ρ hρ i v w
    _ = 0 := h _ ⟨w, rfl⟩

end Orthogonal

end CFSG.LocalAnalysis.GLTheoremA.S267.Cls
