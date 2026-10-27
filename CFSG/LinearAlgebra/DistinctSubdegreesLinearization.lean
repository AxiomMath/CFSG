module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Algebra.Field.ZMod
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.LinearAlgebra

open MulAction

section Extension

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem exists_linearMap_extend_of_bilin (b : LinearMap.BilinForm R V)
    (hb : LinearMap.SeparatingLeft b) {X : Set V} (hX : Submodule.span R X = ⊤) (f : X → V)
    (hf : ∀ u v : X, b (f u) (f v) = b u v) (hfX : Submodule.span R (Set.range f) = ⊤) :
    ∃ L : V →ₗ[R] V, ∀ x : X, L x = f x := by
  set c := Finsupp.linearCombination R (Subtype.val : X → V) with hcdef
  set c' := Finsupp.linearCombination R f with hc'def
  have hc : Function.Surjective c := by
    rw [← LinearMap.range_eq_top, hcdef, Finsupp.range_linearCombination, Subtype.range_coe]
    exact hX
  have key : ∀ l y, b (c' l) (f y) = b (c l) y := by
    intro l y
    induction l using Finsupp.induction_linear with
    | zero => simp
    | add l₁ l₂ h₁ h₂ => rw [map_add, map_add, map_add, map_add, LinearMap.add_apply,
        LinearMap.add_apply, h₁, h₂]
    | single x r => simp [hcdef, hc'def, Finsupp.linearCombination_single, hf]
  have hker : LinearMap.ker c ≤ LinearMap.ker c' := by
    intro l hl
    rw [LinearMap.mem_ker] at hl ⊢
    have hsub : Set.range f ⊆ LinearMap.ker (b (c' l)) := by
      rintro _ ⟨y, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, key, hl, map_zero, LinearMap.zero_apply]
    have h2 := Submodule.span_le.2 hsub
    rw [hfX] at h2
    exact hb _ fun w => h2 Submodule.mem_top
  refine ⟨((LinearMap.ker c).liftQ c' hker).comp
    (c.quotKerEquivOfSurjective hc).symm.toLinearMap, fun x => ?_⟩
  have hx : c (Finsupp.single x 1) = x := by simp [hcdef]
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ← hx,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  simp [hc'def]

end Extension

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

section Orbit

variable {G : Subgroup (V ≃ₗ[ZMod 2] V)} {x₀ : V}

theorem coe_toPermHom_orbit_apply (g : G) (x : orbit G x₀) :
    ((toPermHom G (orbit G x₀) g x : orbit G x₀) : V) = (g : V ≃ₗ[ZMod 2] V) x := rfl

end Orbit

variable (q : QuadraticForm (ZMod 2) V)

theorem polar_apply_eq_of_mem_orthogonalGroup {g : V ≃ₗ[ZMod 2] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup q) (u v : V) :
    QuadraticMap.polar q (g u) (g v) = QuadraticMap.polar q u v := by
  simp only [QuadraticMap.polar, ← map_add, TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 hg]

section Normalizer

variable {G : Subgroup (V ≃ₗ[ZMod 2] V)} {x₀ : V}

local notation "X" => orbit G x₀

theorem polar_perm_eq_of_mem_normalizer (hG : G ≤ TauCeti.QuadraticMap.orthogonalGroup q)
    [Finite V]
    (hsub : ∀ y ∈ X, ∀ y' ∈ X,
      Nat.card (orbit (stabilizer G x₀) y) = Nat.card (orbit (stabilizer G x₀) y') →
        orbit (stabilizer G x₀) y = orbit (stabilizer G x₀) y')
    (σ : Equiv.Perm X)
    (hσ : σ ∈ Subgroup.normalizer ((toPermHom G X).range : Set (Equiv.Perm X))) (u v : X) :
    QuadraticMap.polar q (σ u) (σ v) = QuadraticMap.polar q u v := by
  classical
  set ρ := toPermHom G X with hρdef
  have hpolG : ∀ g : G, ∀ u v : V, QuadraticMap.polar q ((g : V ≃ₗ[ZMod 2] V) u)
      ((g : V ≃ₗ[ZMod 2] V) v) = QuadraticMap.polar q u v :=
    fun g => polar_apply_eq_of_mem_orthogonalGroup q (hG g.2)
  have hnorm : ∀ π ∈ Subgroup.normalizer (ρ.range : Set (Equiv.Perm X)), ∀ g : G,
      ∃ g' : G, ρ g' = π * ρ g * π⁻¹ := by
    intro π hπ g
    have h := (Subgroup.mem_normalizer_iff.1 hπ (ρ g)).1 ⟨g, rfl⟩
    obtain ⟨g', hg'⟩ := h
    exact ⟨g', hg'⟩
  have hinv : ∀ (π : Equiv.Perm X) (w : X), π⁻¹ (π w) = w := fun π w => π.symm_apply_apply w
  set p₀ : X := ⟨x₀, mem_orbit_self x₀⟩ with hp₀
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : G, g₀ • ((σ p₀ : X) : V) = x₀ := by
    obtain ⟨h, hh⟩ := mem_orbit_iff.1 (σ p₀).2
    exact ⟨h⁻¹, by rw [← hh, inv_smul_smul]⟩
  set τ := ρ g₀ * σ with hτdef
  have hτx : τ p₀ = p₀ := Subtype.ext hg₀
  have hτn : τ ∈ Subgroup.normalizer (ρ.range : Set (Equiv.Perm X)) :=
    Subgroup.mul_mem _ (Subgroup.le_normalizer ⟨g₀, rfl⟩) hσ
  have hmaps : ∀ π ∈ Subgroup.normalizer (ρ.range : Set (Equiv.Perm X)), π p₀ = p₀ →
      ∀ y : X, ∀ w : X, (w : V) ∈ orbit (stabilizer G x₀) (y : V) →
        ((π w : X) : V) ∈ orbit (stabilizer G x₀) ((π y : X) : V) := by
    intro π hπ hπx y w hw
    obtain ⟨s, hs⟩ := mem_orbit_iff.1 hw
    obtain ⟨s', hs'⟩ := hnorm π hπ s
    have hπx' : π⁻¹ p₀ = p₀ := by rw [Equiv.Perm.inv_eq_iff_eq, hπx]
    have hs'x : (s' : G) • x₀ = x₀ := by
      have h := congrArg (fun φ : Equiv.Perm X => ((φ p₀ : X) : V)) hs'
      simp only [Equiv.Perm.mul_apply, hπx'] at h
      have hsx : ρ s p₀ = p₀ := Subtype.ext (mem_stabilizer_iff.1 s.2)
      rw [hsx, hπx] at h
      exact h
    have hw' : w = ρ s y := Subtype.ext (by rw [← hs]; rfl)
    have hπw : π w = ρ s' (π y) := by
      rw [hw', hs', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv]
    refine mem_orbit_iff.2 ⟨⟨s', mem_stabilizer_iff.2 hs'x⟩, ?_⟩
    rw [hπw]
    rfl
  have horbit : ∀ y : X, ((τ y : X) : V) ∈ orbit (stabilizer G x₀) (y : V) := by
    intro y
    have hτinv : τ⁻¹ ∈ Subgroup.normalizer (ρ.range : Set (Equiv.Perm X)) := inv_mem hτn
    have hτinvx : τ⁻¹ p₀ = p₀ := by rw [Equiv.Perm.inv_eq_iff_eq, hτx]
    have hsubX : ∀ z : X, orbit (stabilizer G x₀) (z : V) ⊆ X := by
      intro z w hw
      obtain ⟨s, rfl⟩ := mem_orbit_iff.1 hw
      obtain ⟨h, hh⟩ := mem_orbit_iff.1 z.2
      exact mem_orbit_iff.2 ⟨(s : G) * h, by rw [mul_smul, hh]; rfl⟩
    have hle₁ : Nat.card (orbit (stabilizer G x₀) (y : V)) ≤
        Nat.card (orbit (stabilizer G x₀) ((τ y : X) : V)) := by
      refine Nat.card_le_card_of_injective
        (fun w => ⟨((τ ⟨w, hsubX y w.2⟩ : X) : V), hmaps τ hτn hτx y _ w.2⟩) ?_
      intro w w' h
      simp only [Subtype.mk.injEq] at h
      have h2 := τ.injective (Subtype.ext h)
      simp only [Subtype.mk.injEq] at h2
      exact Subtype.ext h2
    have hle₂ : Nat.card (orbit (stabilizer G x₀) ((τ y : X) : V)) ≤
        Nat.card (orbit (stabilizer G x₀) (y : V)) := by
      refine Nat.card_le_card_of_injective
        (fun w => ⟨((τ⁻¹ ⟨w, hsubX (τ y) w.2⟩ : X) : V), by
          have := hmaps τ⁻¹ hτinv hτinvx (τ y) ⟨w, hsubX (τ y) w.2⟩ w.2
          rwa [hinv] at this⟩) ?_
      intro w w' h
      simp only [Subtype.mk.injEq] at h
      have h2 := (τ⁻¹).injective (Subtype.ext h)
      simp only [Subtype.mk.injEq] at h2
      exact Subtype.ext h2
    have heq := hsub (τ y) (τ y).2 y y.2 (le_antisymm hle₂ hle₁)
    rw [heq.symm]
    exact mem_orbit_self _
  have hbase : ∀ y : X, QuadraticMap.polar q ((σ p₀ : X) : V) ((σ y : X) : V) =
      QuadraticMap.polar q x₀ y := by
    intro y
    obtain ⟨s, hs⟩ := mem_orbit_iff.1 (horbit y)
    have hτy : ((τ y : X) : V) = (g₀ : V ≃ₗ[ZMod 2] V) ((σ y : X) : V) := rfl
    have h1 : QuadraticMap.polar q ((σ p₀ : X) : V) ((σ y : X) : V) =
        QuadraticMap.polar q x₀ ((τ y : X) : V) := by
      rw [hτy, ← hpolG g₀ ((σ p₀ : X) : V)]
      congr 1
    have h2 : QuadraticMap.polar q x₀ ((τ y : X) : V) = QuadraticMap.polar q x₀ y := by
      rw [← hs]
      have hsx : ((s : G) : V ≃ₗ[ZMod 2] V) x₀ = x₀ := mem_stabilizer_iff.1 s.2
      change QuadraticMap.polar q x₀ (((s : G) : V ≃ₗ[ZMod 2] V) y) = _
      have h3 := hpolG (s : G) x₀ y
      rw [hsx] at h3
      exact h3
    exact h1.trans h2
  obtain ⟨h, hh⟩ := mem_orbit_iff.1 u.2
  have hu : u = ρ h p₀ := Subtype.ext hh.symm
  obtain ⟨h', hh'⟩ := hnorm σ hσ h
  have hσu : σ u = ρ h' (σ p₀) := by
    rw [hu]
    have := congrArg (fun φ : Equiv.Perm X => φ (σ p₀)) hh'
    simp only [Equiv.Perm.mul_apply, hinv] at this
    exact this.symm
  have hσv : σ (ρ h⁻¹ v) = ρ h'⁻¹ (σ v) := by
    have hh'inv : ρ h'⁻¹ = σ * ρ h⁻¹ * σ⁻¹ := by
      rw [map_inv, hh', map_inv]
      group
    rw [hh'inv, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv]
  calc QuadraticMap.polar q ((σ u : X) : V) ((σ v : X) : V)
      = QuadraticMap.polar q ((σ p₀ : X) : V) ((ρ h'⁻¹ (σ v) : X) : V) := by
        rw [hσu, coe_toPermHom_orbit_apply, coe_toPermHom_orbit_apply,
          ← hpolG h' ((σ p₀ : X) : V)]
        congr 1
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
        rfl
    _ = QuadraticMap.polar q ((σ p₀ : X) : V) ((σ (ρ h⁻¹ v) : X) : V) := by rw [hσv]
    _ = QuadraticMap.polar q x₀ ((ρ h⁻¹ v : X) : V) := hbase _
    _ = QuadraticMap.polar q ((u : X) : V) ((v : X) : V) := by
        rw [coe_toPermHom_orbit_apply, ← hpolG h x₀, ← hh]
        congr 1
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel]
        rfl

theorem distinct_subdegrees_spanning_orbit_linearizes_normalizer [FiniteDimensional (ZMod 2) V]
    (hb : (QuadraticMap.polarBilin q).Nondegenerate)
    (hG : G ≤ TauCeti.QuadraticMap.orthogonalGroup q) (hspan : Submodule.span (ZMod 2) X = ⊤)
    (hsub : ∀ y ∈ X, ∀ y' ∈ X,
      Nat.card (orbit (stabilizer G x₀) y) = Nat.card (orbit (stabilizer G x₀) y') →
        orbit (stabilizer G x₀) y = orbit (stabilizer G x₀) y')
    (σ : Equiv.Perm X)
    (hσ : σ ∈ Subgroup.normalizer ((toPermHom G X).range : Set (Equiv.Perm X))) :
    (∀ u v : X, QuadraticMap.polar q (σ u) (σ v) = QuadraticMap.polar q u v) ∧
    ∃ L : V ≃ₗ[ZMod 2] V, L ∈ TauCeti.QuadraticMap.orthogonalGroup q ∧
      (∀ x : X, L x = σ x) ∧
      (∀ L' : V →ₗ[ZMod 2] V, (∀ x : X, L' x = σ x) → L' = L.toLinearMap) ∧
      L ∈ Subgroup.normalizer (G : Set (V ≃ₗ[ZMod 2] V)) ∧
      ∀ g : G, ∃ hg : L * g * L⁻¹ ∈ G,
        toPermHom G X ⟨L * g * L⁻¹, hg⟩ = σ * toPermHom G X g * σ⁻¹ := by
  classical
  have : Finite V := Module.finite_of_finite (ZMod 2)
  set ρ := toPermHom G X with hρdef
  have hpol := polar_perm_eq_of_mem_normalizer q hG hsub σ hσ
  refine ⟨hpol, ?_⟩
  have hinv : ∀ (π : Equiv.Perm X) (w : X), π⁻¹ (π w) = w := fun π w => π.symm_apply_apply w
  have hinv' : ∀ (π : Equiv.Perm X) (w : X), π (π⁻¹ w) = w := fun π w => π.apply_symm_apply w
  have hext : ∀ π : Equiv.Perm X, (∀ u v : X, QuadraticMap.polar q (π u) (π v) =
      QuadraticMap.polar q u v) → ∃ M : V →ₗ[ZMod 2] V, ∀ x : X, M x = π x := by
    intro π hπ
    refine exists_linearMap_extend_of_bilin (QuadraticMap.polarBilin q) hb.1 hspan
      (fun x => (π x : V)) hπ ?_
    have hrange : Set.range (fun x : X => ((π x : X) : V)) = X := by
      ext v
      constructor
      · rintro ⟨x, rfl⟩
        exact (π x).2
      · intro hv
        refine ⟨π⁻¹ ⟨v, hv⟩, ?_⟩
        change ((π (π⁻¹ ⟨v, hv⟩) : X) : V) = v
        rw [hinv']
    rw [hrange]
    exact hspan
  have hpolinv : ∀ u v : X, QuadraticMap.polar q (σ⁻¹ u) (σ⁻¹ v) = QuadraticMap.polar q u v := by
    intro u v
    rw [← hpol (σ⁻¹ u) (σ⁻¹ v), hinv', hinv']
  obtain ⟨L₁, hL₁⟩ := hext σ hpol
  obtain ⟨L₂, hL₂⟩ := hext σ⁻¹ hpolinv
  have h12 : L₁.comp L₂ = LinearMap.id := LinearMap.ext_on hspan fun x hx => by
    rw [LinearMap.comp_apply, hL₂ ⟨x, hx⟩, hL₁, hinv', LinearMap.id_apply]
  have h21 : L₂.comp L₁ = LinearMap.id := LinearMap.ext_on hspan fun x hx => by
    rw [LinearMap.comp_apply, hL₁ ⟨x, hx⟩, hL₂, hinv, LinearMap.id_apply]
  set L : V ≃ₗ[ZMod 2] V := LinearEquiv.ofLinearMap L₁ L₂ h12 h21 with hLdef
  have hLx : ∀ x : X, L x = σ x := hL₁
  have hLinvx : ∀ x : X, L⁻¹ x = σ⁻¹ x := hL₂
  have hLpol : ∀ u v, QuadraticMap.polar q (L u) (L v) = QuadraticMap.polar q u v := by
    have hB : (QuadraticMap.polarBilin q).compl₁₂ L.toLinearMap L.toLinearMap =
        QuadraticMap.polarBilin q := by
      refine LinearMap.ext_on hspan fun x hx => LinearMap.ext_on hspan fun y hy => ?_
      rw [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
        hLx ⟨x, hx⟩, hLx ⟨y, hy⟩, hpol]
    intro u v
    have h := congrArg (fun B : LinearMap.BilinForm (ZMod 2) V => B u v) hB
    simpa only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
      QuadraticMap.polarBilin_apply_apply] using h
  have hqX : ∀ x : X, q x = q x₀ := by
    intro x
    obtain ⟨g, hg⟩ := mem_orbit_iff.1 x.2
    rw [← hg]
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.1 (hG g.2) x₀
  have hLq : L ∈ TauCeti.QuadraticMap.orthogonalGroup q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    have hv : v ∈ Submodule.span (ZMod 2) X := hspan ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem x hx => rw [hLx ⟨x, hx⟩, hqX, hqX ⟨x, hx⟩]
    | zero => rw [map_zero]
    | add u w _ _ hu hw =>
      rw [map_add, ← sub_eq_zero]
      have h1 : q (L u + L w) = QuadraticMap.polar q (L u) (L w) + q (L u) + q (L w) := by
        simp only [QuadraticMap.polar]
        abel
      have h2 : q (u + w) = QuadraticMap.polar q u w + q u + q w := by
        simp only [QuadraticMap.polar]
        abel
      rw [h1, h2, hLpol, hu, hw, sub_self]
    | smul c u _ hu => rw [map_smul, QuadraticMap.map_smul, QuadraticMap.map_smul, hu]
  have hconj : ∀ π ∈ Subgroup.normalizer (ρ.range : Set (Equiv.Perm X)),
      ∀ M : V ≃ₗ[ZMod 2] V, (∀ x : X, M x = π x) → (∀ x : X, M⁻¹ x = π⁻¹ x) →
      ∀ g : G, ∃ g' : G, M * g * M⁻¹ = g' ∧ ρ g' = π * ρ g * π⁻¹ := by
    intro π hπ M hM hMinv g
    obtain ⟨g', hg'⟩ := (Subgroup.mem_normalizer_iff.1 hπ (ρ g)).1 ⟨g, rfl⟩
    refine ⟨g', ?_, hg'⟩
    apply LinearEquiv.toLinearMap_injective
    refine LinearMap.ext_on hspan fun x hx => ?_
    have hgx := coe_toPermHom_orbit_apply g (π⁻¹ ⟨x, hx⟩)
    have hg'x := coe_toPermHom_orbit_apply g' ⟨x, hx⟩
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
      hMinv ⟨x, hx⟩, ← hgx, hM, ← hg'x, hg']
    rfl
  refine ⟨L, hLq, hLx, fun L' hL' => LinearMap.ext_on hspan fun x hx => ?_, ?_, fun g => ?_⟩
  · rw [hL' ⟨x, hx⟩, LinearEquiv.coe_coe, hLx ⟨x, hx⟩]
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨g', hg', -⟩ := hconj σ hσ L hLx hLinvx ⟨h, hh⟩
      rw [show L * h * L⁻¹ = L * (⟨h, hh⟩ : G) * L⁻¹ from rfl, hg']
      exact g'.2
    · intro hh
      have hLinv' : ∀ x : X, L⁻¹⁻¹ x = σ⁻¹⁻¹ x := by
        intro x
        rw [inv_inv, inv_inv, hLx]
      obtain ⟨g', hg', -⟩ := hconj σ⁻¹ (inv_mem hσ) L⁻¹ hLinvx hLinv' ⟨_, hh⟩
      have : h = L⁻¹ * (L * h * L⁻¹) * L⁻¹⁻¹ := by group
      rw [this, show L⁻¹ * (L * h * L⁻¹) * L⁻¹⁻¹ =
        L⁻¹ * ((⟨L * h * L⁻¹, hh⟩ : G) : V ≃ₗ[ZMod 2] V) * L⁻¹⁻¹ from rfl, hg']
      exact g'.2
  · obtain ⟨g', hg', hρ⟩ := hconj σ hσ L hLx hLinvx g
    refine ⟨hg' ▸ g'.2, ?_⟩
    rw [← hρ]
    congr 1
    exact Subtype.ext hg'

end Normalizer

end CFSG.LinearAlgebra
