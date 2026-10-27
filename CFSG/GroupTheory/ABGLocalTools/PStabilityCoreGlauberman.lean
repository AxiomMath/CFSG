module

public import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Algebra.Field.ZMod
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.Lemma6_2
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate42
public import Certificates.Certificate43

public section

open Subgroup CFSG.LinearGroups

namespace CFSG.ABGLocalTools

@[expose] def HasSL2Quotient (p : ℕ) (X : Type*) [Group X] : Prop :=
  (∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K p)
      (φ : X →* Matrix.SpecialLinearGroup (Fin 2) K), Function.Surjective φ) ∨
    ∃ φ : X →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), Function.Surjective φ

theorem HasSL2Quotient.of_surjective {p : ℕ} {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Surjective f) (h : HasSL2Quotient p Y) : HasSL2Quotient p X := by
  rcases h with ⟨K, hK, hKf, hKc, φ, hφ⟩ | ⟨φ, hφ⟩
  · exact Or.inl ⟨K, hK, hKf, hKc, φ.comp f, hφ.comp hf⟩
  · exact Or.inr ⟨φ.comp f, hφ.comp hf⟩

universe u

variable {p : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem isPGroup_zpowers_of_pow_eq_one {G : Type*} [Group G] {b : G} (hb : b ^ p = 1) :
    IsPGroup p (zpowers b) := by
  rintro ⟨y, hy⟩
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  refine ⟨1, Subtype.ext ?_⟩
  change (b ^ k) ^ p ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb, one_zpow]

theorem closure_pair_preimage_eq_top {G : Type*} [Group G] (a b : G) :
    closure ({⟨a, subset_closure (Set.mem_insert _ _)⟩,
      ⟨b, subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩} :
        Set (closure ({a, b} : Set G))) = ⊤ := by
  rw [← closure_preimage_eq_top ({a, b} : Set G)]
  congr 1
  ext y
  simp [Subtype.ext_iff]

variable {V : Type u} [AddCommGroup V] [Module (ZMod p) V]

theorem quadratic_restrict (Γ : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) V))
    (W : Submodule (ZMod p) V) (hW : ∀ g ∈ Γ, ∀ w ∈ W, (g : V →ₗ[ZMod p] V) w ∈ W) (g : Γ)
    (hg : ((g.1 : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) :
    ((invariantRestrict Γ W hW g : W →ₗ[ZMod p] W) - 1) ^ 2 = 0 := by
  ext w
  have h := congrArg (fun φ : V →ₗ[ZMod p] V => φ w) hg
  simp only [sq, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply] at h ⊢
  rw [Submodule.coe_sub, coe_invariantRestrict_apply, Submodule.coe_sub,
    coe_invariantRestrict_apply]
  simpa using h

theorem quadratic_quotient (Γ : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) V))
    (W : Submodule (ZMod p) V) (hW : ∀ g ∈ Γ, ∀ w ∈ W, (g : V →ₗ[ZMod p] V) w ∈ W) (g : Γ)
    (hg : ((g.1 : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) :
    ((invariantQuotient Γ W hW g : (V ⧸ W) →ₗ[ZMod p] V ⧸ W) - 1) ^ 2 = 0 := by
  refine LinearMap.ext fun v => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective W v
  have h := congrArg (fun φ : V →ₗ[ZMod p] V => φ v) hg
  simp only [sq, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
    LinearMap.zero_apply] at h
  have h1 : ∀ w : V, ((invariantQuotient Γ W hW g : (V ⧸ W) →ₗ[ZMod p] V ⧸ W) - 1)
      (Submodule.Quotient.mk w) = Submodule.Quotient.mk ((g.1 : V →ₗ[ZMod p] V) w - w) := by
    intro w
    rw [LinearMap.sub_apply, Module.End.one_apply, invariantQuotient_apply_mk,
      Submodule.Quotient.mk_sub]
  rw [sq, Module.End.mul_apply, h1, h1, LinearMap.zero_apply, h, Submodule.Quotient.mk_zero]

theorem range_eq_closure_pair {G M : Type*} [Group G] [Group M] {Γ : Subgroup G} {a b : G}
    (hΓ : closure {a, b} = Γ) (f : Γ →* M) (ha : a ∈ Γ) (hb : b ∈ Γ) :
    closure {f ⟨a, ha⟩, f ⟨b, hb⟩} = f.range := by
  subst hΓ
  rw [MonoidHom.range_eq_map, ← closure_pair_preimage_eq_top a b, MonoidHom.map_closure,
    Set.image_pair]

theorem hasSL2Quotient_of_quadratic_generators
    (hp : p ≠ 2) (n : ℕ) :
    ∀ {V : Type u} [AddCommGroup V] [Module (ZMod p) V] [FiniteDimensional (ZMod p) V],
      Module.finrank (ZMod p) V = n →
      ∀ (Γ : Subgroup (LinearMap.GeneralLinearGroup (ZMod p) V))
        (a b : LinearMap.GeneralLinearGroup (ZMod p) V), closure {a, b} = Γ →
        ((a : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 → ((b : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 →
        ¬ IsPGroup p Γ → HasSL2Quotient p Γ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn Γ a b hΓ ha hb hnp
  have haΓ : a ∈ Γ := hΓ ▸ subset_closure (Set.mem_insert _ _)
  have hbΓ : b ∈ Γ := hΓ ▸ subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have : Finite V := Module.finite_of_finite (ZMod p)
  have : Finite (LinearMap.GeneralLinearGroup (ZMod p) V) :=
    Finite.of_injective (fun g : LinearMap.GeneralLinearGroup (ZMod p) V =>
      fun v : V => (g : V →ₗ[ZMod p] V) v) (fun g h hgh => Units.ext (LinearMap.ext
        fun v => congrFun hgh v))
  by_cases hirr : ∀ W : Submodule (ZMod p) V,
      (∀ g ∈ Γ, ∀ w ∈ W, (g : V →ₗ[ZMod p] V) w ∈ W) → W = ⊥ ∨ W = ⊤
  ·
    have hne : ∀ c : LinearMap.GeneralLinearGroup (ZMod p) V,
        ((c : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 → ∀ d, closure {c, d} = Γ ∨ closure {d, c} = Γ →
        ((d : V →ₗ[ZMod p] V) - 1) ^ 2 = 0 → (c : V →ₗ[ZMod p] V) - 1 ≠ 0 := by
      intro c _ d hcd hd hc1
      have hc : c = 1 := Units.ext (sub_eq_zero.mp hc1)
      have hdp : d ^ p = 1 := (quadratic_linear_p_elements p d hd).1
      have hΓd : Γ = zpowers d := by
        rcases hcd with h | h
        · rw [← h, hc, closure_insert_one, zpowers_eq_closure]
        · rw [← h, hc, Set.pair_comm, closure_insert_one, zpowers_eq_closure]
      apply hnp
      rw [hΓd]
      exact isPGroup_zpowers_of_pow_eq_one hdp
    let D : CFSG.Glauberman.Lemma62Data p hp V Γ :=
      { ρ := Γ.subtype
        faithful := subtype_injective Γ
        irreducible := fun W hW => hirr W fun g hg w hw => hW ⟨g, hg⟩ w hw
        two_generators := by
          refine ⟨⟨a, haΓ⟩, ⟨b, hbΓ⟩, ?_, ha, hne a ha b (Or.inl hΓ) hb, hb,
            hne b hb a (Or.inr hΓ) ha⟩
          subst hΓ
          exact closure_pair_preimage_eq_top a b }
    obtain ⟨K, hK, hAlg, φ, hφinj, -, -, hiso⟩ := CFSG.Glauberman.lemma6_2_part_c hp D
    let := hK
    let := hAlg
    have hKfin : Finite K := Finite.of_injective (fun k : K => fun v : V => φ k v)
      (fun k l hkl => hφinj (LinearMap.ext fun v => congrFun hkl v))
    have hKchar : CharP K p := charP_of_injective_algebraMap (algebraMap (ZMod p) K).injective p
    rcases hiso with hne | ⟨-, hne⟩
    · obtain ⟨e⟩ := hne
      exact Or.inl ⟨K, hK, hKfin, hKchar, e.toMonoidHom, e.surjective⟩
    · obtain ⟨e⟩ := hne
      exact Or.inr ⟨e.toMonoidHom, e.surjective⟩
  ·
    simp only [not_forall, not_or] at hirr
    obtain ⟨W, hW, hW0, hWt⟩ := hirr
    set ρW := invariantRestrict Γ W hW with hρW
    set ρQ := invariantQuotient Γ W hW with hρQ
    by_cases hWp : IsPGroup p ρW.range
    · by_cases hQp : IsPGroup p ρQ.range
      · exact absurd (linear_p_extension Γ W p hW hWp hQp) hnp
      · have hlt : Module.finrank (ZMod p) (V ⧸ W) < n := by
          have h1 := Submodule.finrank_quotient_add_finrank W
          have h2 : Module.finrank (ZMod p) W ≠ 0 := fun h0 =>
            hW0 (Submodule.finrank_eq_zero.mp h0)
          omega
        have h := ih _ hlt rfl ρQ.range (ρQ ⟨a, haΓ⟩) (ρQ ⟨b, hbΓ⟩)
          (range_eq_closure_pair hΓ ρQ haΓ hbΓ) (quadratic_quotient Γ W hW ⟨a, haΓ⟩ ha)
          (quadratic_quotient Γ W hW ⟨b, hbΓ⟩ hb) hQp
        exact h.of_surjective ρQ.rangeRestrict ρQ.rangeRestrict_surjective
    · have hlt : Module.finrank (ZMod p) W < n := hn ▸ Submodule.finrank_lt hWt
      have h := ih _ hlt rfl ρW.range (ρW ⟨a, haΓ⟩) (ρW ⟨b, hbΓ⟩)
        (range_eq_closure_pair hΓ ρW haΓ hbΓ) (quadratic_restrict Γ W hW ⟨a, haΓ⟩ ha)
        (quadratic_restrict Γ W hW ⟨b, hbΓ⟩ hb) hWp
      exact h.of_surjective ρW.rangeRestrict ρW.rangeRestrict_surjective

theorem hasSL2Quotient_of_rep
    (hp : p ≠ 2) {X : Type*} [Group X]
    [FiniteDimensional (ZMod p) V] (σ : X →* LinearMap.GeneralLinearGroup (ZMod p) V) {a b : X}
    (hab : closure {a, b} = (⊤ : Subgroup X)) (ha : ((σ a : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (hb : ((σ b : V →ₗ[ZMod p] V) - 1) ^ 2 = 0) (hnp : ¬ IsPGroup p σ.range) :
    HasSL2Quotient p X := by
  have hcl : closure {σ a, σ b} = σ.range := by
    rw [MonoidHom.range_eq_map, ← hab, MonoidHom.map_closure, Set.image_pair]
  exact (hasSL2Quotient_of_quadratic_generators hp _ rfl σ.range (σ a) (σ b) hcl ha hb
    hnp).of_surjective σ.rangeRestrict σ.rangeRestrict_surjective

end CFSG.ABGLocalTools
