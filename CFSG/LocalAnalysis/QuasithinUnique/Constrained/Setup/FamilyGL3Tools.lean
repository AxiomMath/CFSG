module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.QuasithinUnique.Setup.Family

section Fixed

variable {G E : Type*} [Group G] [AddCommMonoid E] [Module (ZMod 2) E]

theorem add_self_eq_zero_of_zmod_two (x : E) : x + x = 0 := by
  rw [← two_smul (ZMod 2) x, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem two_dvd_natCard_of_ne_bot [Finite E] (B : Submodule (ZMod 2) E) (hB : B ≠ ⊥) :
    2 ∣ Nat.card B := by
  classical
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff B).1 hB
  have hxx : x + x = 0 := add_self_eq_zero_of_zmod_two x
  let σ : Function.End B := fun b => b + ⟨x, hx⟩
  have hfp : ∀ b : B, σ b ≠ b := by
    intro b h
    have h1 : b.1 + x = b.1 := congrArg Subtype.val h
    have h2 : b.1 + b.1 = 0 := add_self_eq_zero_of_zmod_two b.1
    have : x = 0 := by
      calc x = (b.1 + b.1) + x := by rw [h2, zero_add]
        _ = b.1 + (b.1 + x) := by rw [add_assoc]
        _ = b.1 + b.1 := by rw [h1]
        _ = 0 := h2
    exact hx0 this
  have hsq : σ ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two]
    funext b
    apply Subtype.ext
    change b.1 + x + x = b.1
    rw [add_assoc, hxx, add_zero]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype B := Fintype.ofFinite B
  have hmod := Equiv.Perm.card_fixedPoints_modEq (α := B) (f := σ) (p := 2) (n := 1) hsq
  have hempty : IsEmpty (Function.fixedPoints σ) := ⟨fun ⟨b, hb⟩ => hfp b hb⟩
  have h0 : Fintype.card (Function.fixedPoints σ) = 0 := Fintype.card_eq_zero
  rw [h0] at hmod
  rw [Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd).1 hmod

theorem exists_ne_zero_fixed [Finite E] (ρ : G →* (E ≃ₗ[ZMod 2] E)) (T : Subgroup G)
    (hT : IsPGroup 2 T) (B : Submodule (ZMod 2) E) (hB : B ≠ ⊥)
    (hinv : ∀ g ∈ T, ∀ x ∈ B, ρ g x ∈ B) : ∃ e ∈ B, e ≠ 0 ∧ ∀ t ∈ T, ρ t e = e := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB' : ∀ t : T, ∀ x : E, x ∈ B ↔ ρ t x ∈ B := by
    intro t x
    refine ⟨hinv t t.2 x, fun h => ?_⟩
    have h1 := hinv (t : G)⁻¹ (T.inv_mem t.2) _ h
    have h2 : ρ ((t : G)⁻¹) (ρ t x) = x := by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rwa [h2] at h1
  let φ : T →* Equiv.Perm B :=
    { toFun := fun t => Equiv.subtypeEquiv (ρ t).toEquiv (hB' t)
      map_one' := by
        refine Equiv.ext fun x => Subtype.ext ?_
        simp
      map_mul' := by
        intro s t
        refine Equiv.ext fun x => Subtype.ext ?_
        simp }
  let _inst : MulAction T B := MulAction.compHom B φ
  have hcard : 2 ∣ Nat.card B := two_dvd_natCard_of_ne_bot B hB
  have h0 : (0 : B) ∈ MulAction.fixedPoints T B := fun t => Subtype.ext (map_zero (ρ t))
  obtain ⟨b, hb, hne⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point B hcard h0
  refine ⟨b, b.2, ?_, fun t ht => ?_⟩
  · intro hb0
    exact hne (Subtype.ext hb0.symm)
  · have := hb ⟨t, ht⟩
    exact congrArg Subtype.val this

end Fixed

section Actions

variable {G E E' E'' : Type*} [AddCommMonoid E] [Module (ZMod 2) E] [AddCommMonoid E']
  [Module (ZMod 2) E'] [AddCommMonoid E''] [Module (ZMod 2) E'']

@[expose] def IsInvAct (act : G → E → E) (N : Submodule (ZMod 2) E) : Prop :=
  ∀ g x, x ∈ N → act g x ∈ N

@[expose] def IsIrrAct (act : G → E → E) : Prop :=
  Nontrivial E ∧ (∀ g, act g 0 = 0) ∧ ∀ N : Submodule (ZMod 2) E, IsInvAct act N → N = ⊥ ∨ N = ⊤

@[expose] def IsEquivAct (act : G → E → E) (act' : G → E' → E') (f : E →ₗ[ZMod 2] E') : Prop :=
  ∀ g x, f (act g x) = act' g (f x)

@[expose] def ActIso (act : G → E → E) (act' : G → E' → E') : Prop :=
  ∃ f : E ≃ₗ[ZMod 2] E', ∀ g x, f (act g x) = act' g (f x)

theorem ActIso.refl (act : G → E → E) : ActIso act act :=
  ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩

theorem ActIso.symm {act : G → E → E} {act' : G → E' → E'} (h : ActIso act act') :
    ActIso act' act := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.symm, fun g x => ?_⟩
  apply f.injective
  rw [hf, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem ActIso.trans {act : G → E → E} {act' : G → E' → E'} {act'' : G → E'' → E''}
    (h : ActIso act act') (h' : ActIso act' act'') : ActIso act act'' := by
  obtain ⟨f, hf⟩ := h
  obtain ⟨f', hf'⟩ := h'
  exact ⟨f.trans f', fun g x => by simp [hf, hf']⟩

theorem IsIrrAct.of_actIso {act : G → E → E} {act' : G → E' → E'} (h : ActIso act act')
    (hρ : IsIrrAct act) : IsIrrAct act' := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(f.toEquiv.nontrivial_congr).1 hρ.1, fun g => ?_, fun N hN => ?_⟩
  · have h0 : f 0 = 0 := map_zero f
    have := hf g 0
    rw [hρ.2.1 g, h0] at this
    exact this.symm
  · have hinv : IsInvAct act (N.comap (f : E →ₗ[ZMod 2] E')) := by
      intro g x hx
      show f (act g x) ∈ N
      rw [hf]
      exact hN g _ hx
    rcases hρ.2.2 _ hinv with h0 | h1
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      have : x ∈ N.comap (f : E →ₗ[ZMod 2] E') := hy
      rw [h0, Submodule.mem_bot] at this
      rw [this, map_zero]
      exact Submodule.zero_mem _
    · right
      rw [eq_top_iff]
      intro y _
      obtain ⟨x, rfl⟩ := f.surjective y
      have : x ∈ N.comap (f : E →ₗ[ZMod 2] E') := by rw [h1]; trivial
      exact this

theorem injective_of_ker_eq_bot (f : E →ₗ[ZMod 2] E') (h : LinearMap.ker f = ⊥) :
    Function.Injective f := by
  intro x y hxy
  have h1 : x + y ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker, map_add, hxy]
    exact add_self_eq_zero_of_zmod_two (f y)
  rw [h, Submodule.mem_bot] at h1
  calc x = x + (y + y) := by rw [add_self_eq_zero_of_zmod_two y, add_zero]
    _ = (x + y) + y := by rw [add_assoc]
    _ = y := by rw [h1, zero_add]

theorem IsIrrAct.bijective_of_ne_zero {act : G → E → E} {act' : G → E' → E'}
    (hρ : IsIrrAct act) (hρ' : IsIrrAct act') {f : E →ₗ[ZMod 2] E'}
    (hf : IsEquivAct act act' f) (hf0 : f ≠ 0) : Function.Bijective f := by
  constructor
  · apply injective_of_ker_eq_bot
    have hker : IsInvAct act (LinearMap.ker f) := by
      intro g x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [hf, hx, hρ'.2.1 g]
    rcases hρ.2.2 _ hker with h | h
    · exact h
    · exact absurd (LinearMap.ker_eq_top.1 h) hf0
  · rw [← LinearMap.range_eq_top]
    have hrange : IsInvAct act' (LinearMap.range f) := by
      rintro g _ ⟨x, rfl⟩
      exact ⟨act g x, hf g x⟩
    rcases hρ'.2.2 _ hrange with h | h
    · exact absurd (LinearMap.range_eq_bot.1 h) hf0
    · exact h

theorem exists_linear_of_ker_le {N : Type*} [AddCommMonoid N] [Module (ZMod 2) N]
    (ψ : N →ₗ[ZMod 2] E) (hψ : Function.Surjective ψ) (φ : N →ₗ[ZMod 2] E')
    (h : LinearMap.ker ψ ≤ LinearMap.ker φ) : ∃ θ : E →ₗ[ZMod 2] E', ∀ n, θ (ψ n) = φ n := by
  classical
  choose s hs using hψ
  have hkey : ∀ a b : N, ψ a = ψ b → φ a = φ b := by
    intro a b hab
    have h1 : a + b ∈ LinearMap.ker ψ := by
      rw [LinearMap.mem_ker, map_add, hab]
      exact add_self_eq_zero_of_zmod_two (ψ b)
    have h2 := h h1
    rw [LinearMap.mem_ker, map_add] at h2
    calc φ a = φ a + (φ b + φ b) := by rw [add_self_eq_zero_of_zmod_two (φ b), add_zero]
      _ = (φ a + φ b) + φ b := by rw [add_assoc]
      _ = φ b := by rw [h2, zero_add]
  refine ⟨{ toFun := fun x => φ (s x)
            map_add' := fun x y => ?_
            map_smul' := fun c x => ?_ }, fun n => ?_⟩
  · have : ψ (s (x + y)) = ψ (s x + s y) := by rw [hs, map_add, hs, hs]
    show φ (s (x + y)) = φ (s x) + φ (s y)
    rw [hkey _ _ this, map_add]
  · have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · have h0 : φ (s ((0 : ZMod 2) • x)) = 0 := by
        rw [zero_smul, hkey (s 0) 0 (by rw [hs, map_zero])]
        exact map_zero φ
      show φ (s ((0 : ZMod 2) • x)) = (RingHom.id (ZMod 2)) 0 • φ (s x)
      rw [h0]
      simp
    · show φ (s ((1 : ZMod 2) • x)) = (RingHom.id (ZMod 2)) 1 • φ (s x)
      rw [one_smul]
      simp
  · show φ (s (ψ n)) = φ n
    exact hkey _ _ (hs (ψ n))

theorem exists_equivAct_of_ker_le {N : Type*} [AddCommMonoid N] [Module (ZMod 2) N]
    {actN : G → N → N} {actX : G → E → E} {actY : G → E' → E'}
    (ψ : N →ₗ[ZMod 2] E) (hψ : Function.Surjective ψ) (hψe : IsEquivAct actN actX ψ)
    (φ : N →ₗ[ZMod 2] E') (hφe : IsEquivAct actN actY φ) (h : LinearMap.ker ψ ≤ LinearMap.ker φ) :
    ∃ θ : E →ₗ[ZMod 2] E', IsEquivAct actX actY θ ∧ ∀ n, θ (ψ n) = φ n := by
  obtain ⟨θ, hθ⟩ := exists_linear_of_ker_le ψ hψ φ h
  refine ⟨θ, fun g x => ?_, hθ⟩
  obtain ⟨n, rfl⟩ := hψ x
  rw [← hψe g n, hθ, hθ, hφe g n]

theorem actIso_of_ker_le {N : Type*} [AddCommMonoid N] [Module (ZMod 2) N]
    {actN : G → N → N} {actX : G → E → E} {actY : G → E' → E'}
    (hX : IsIrrAct actX) (hY : IsIrrAct actY) (ψ : N →ₗ[ZMod 2] E) (hψ : Function.Surjective ψ)
    (hψe : IsEquivAct actN actX ψ) (φ : N →ₗ[ZMod 2] E') (hφe : IsEquivAct actN actY φ)
    (hφ0 : φ ≠ 0) (h : LinearMap.ker ψ ≤ LinearMap.ker φ) : ActIso actX actY := by
  obtain ⟨θ, hθe, hθ⟩ := exists_equivAct_of_ker_le ψ hψ hψe φ hφe h
  have hθ0 : θ ≠ 0 := by
    intro h0
    apply hφ0
    refine LinearMap.ext fun n => ?_
    rw [← hθ, h0]
    rfl
  exact ⟨LinearEquiv.ofBijective θ (hX.bijective_of_ne_zero hY hθe hθ0), fun g x => hθe g x⟩

end Actions

section Reps

variable {G E E' : Type*} [Group G] [AddCommMonoid E] [Module (ZMod 2) E] [AddCommMonoid E']
  [Module (ZMod 2) E']

@[expose] def IsIrrRep (ρ : G →* (E ≃ₗ[ZMod 2] E)) : Prop := IsIrrAct (fun g x => ρ g x)

@[expose] def ModIso (ρ : G →* (E ≃ₗ[ZMod 2] E)) (ρ' : G →* (E' ≃ₗ[ZMod 2] E')) : Prop :=
  ActIso (fun g x => ρ g x) (fun g x => ρ' g x)

theorem isIrrRep_of {ρ : G →* (E ≃ₗ[ZMod 2] E)} (hnt : Nontrivial E)
    (h : ∀ N : Submodule (ZMod 2) E, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤) :
    IsIrrRep ρ :=
  ⟨hnt, fun g => map_zero (ρ g), fun N hN => h N fun g x hx => hN g x hx⟩

theorem IsIrrRep.comp_surjective {H : Type*} [Group H] {ρ : G →* (E ≃ₗ[ZMod 2] E)}
    (hρ : IsIrrRep ρ) {φ : H →* G} (hφ : Function.Surjective φ) : IsIrrRep (ρ.comp φ) := by
  refine ⟨hρ.1, fun g => map_zero ((ρ.comp φ) g), fun N hN => hρ.2.2 N fun g x hx => ?_⟩
  obtain ⟨h, rfl⟩ := hφ g
  exact hN h x hx

end Reps

end CFSG.QuasithinUnique.Setup.Family
