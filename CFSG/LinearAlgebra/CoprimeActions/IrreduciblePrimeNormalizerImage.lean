module

public import CFSG.LinearAlgebra.CoprimeActions.SmallDimensionStableIrreducibleImage
public import CFSG.LinearAlgebra.CoprimeActions.CoprimeIrreducibleConstituentSeparates
public import CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary
public import Mathlib.Order.CompletePartialOrder

public section

open scoped MonoidAlgebra commutatorElement

namespace CFSG.LinearAlgebra.CoprimeActions.IrreduciblePrimeNormalizerImage

open CFSG.LinearAlgebra.CoprimeActions.RepresentationFaithfulImageVocabulary

section aux

variable {F : Type*} [Field F] {W : Type*} [AddCommGroup W] [Module F W]

private theorem irreducible_congr {G G' : Type*} [Group G] [Group G']
    (ρ₁ : Representation F G W) (ρ₂ : Representation F G' W)
    (h₁ : ∀ g, ∃ g', ρ₂ g' = ρ₁ g) (h₂ : ∀ g', ∃ g, ρ₁ g = ρ₂ g') :
    ρ₁.IsIrreducible → ρ₂.IsIrreducible := by
  intro h
  unfold Representation.IsIrreducible at h ⊢
  let e : Subrepresentation ρ₁ ≃o Subrepresentation ρ₂ :=
    { toFun := fun S => ⟨S.toSubmodule, fun g' v hv => by
        obtain ⟨g, hg⟩ := h₂ g'
        rw [← hg]; exact S.apply_mem_toSubmodule g hv⟩
      invFun := fun S => ⟨S.toSubmodule, fun g v hv => by
        obtain ⟨g', hg⟩ := h₁ g
        rw [← hg]; exact S.apply_mem_toSubmodule g' hv⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }
  exact (OrderIso.isSimpleOrder_iff e).1 h

variable {E : Type*} [Group E]

private theorem eq_one_of_equiv {W' : Type*} [AddCommGroup W'] [Module F W']
    (η₁ : Representation F E W) (η₂ : Representation F E W')
    (θ : η₁.asModule ≃ₗ[F[E]] η₂.asModule) (e : E) (h : η₁ e = 1) : η₂ e = 1 := by
  ext v'
  have h1 : ∀ x : η₁.asModule, MonoidAlgebra.of F E e • x = x := by
    intro x
    have := Representation.asModuleEquiv_symm_map_rho η₁ e (η₁.asModuleEquiv x)
    rw [h] at this
    simpa using this.symm
  have h2 := Representation.asModuleEquiv_symm_map_rho η₂ e v'
  set y := η₂.asModuleEquiv.symm v'
  have : MonoidAlgebra.of F E e • y = y := by
    have := congrArg θ (h1 (θ.symm y))
    rwa [map_smul, LinearEquiv.apply_symm_apply] at this
  have h3 : η₂.asModuleEquiv.symm (η₂ e v') = η₂.asModuleEquiv.symm v' := by
    rw [h2]; exact this
  simpa using η₂.asModuleEquiv.symm.injective h3

private theorem exists_simple {V : Type*} [AddCommGroup V] [Module F V]
    (σ : Representation F E V) (W1 : Submodule F V) (hW1 : ∀ g, W1 ≤ W1.comap (σ g))
    (hirr : (Representation.subrepresentation σ W1 hW1).IsIrreducible) :
    ∃ S0 : Submodule F[E] σ.asModule, IsSimpleModule F[E] S0 ∧
      Nonempty ((Representation.subrepresentation σ W1 hW1).asModule ≃ₗ[F[E]] S0) := by
  set η := Representation.subrepresentation σ W1 hW1
  let fI : Representation.IntertwiningMap η σ :=
    { toLinearMap := W1.subtype
      isIntertwining' := fun g => by
        ext w
        rfl }
  let g := Representation.IntertwiningMap.equivLinearMapAsModule _ _ fI
  have hg : Function.Injective g := fun x y hxy => Subtype.ext hxy
  have hs : IsSimpleModule F[E] η.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule η).1 hirr
  let e := LinearEquiv.ofInjective g hg
  exact ⟨LinearMap.range g, IsSimpleModule.congr e.symm, ⟨e⟩⟩

end aux

universe u

theorem exists_image {F : Type*} [Field F] [IsAlgClosed F]
    {H : Type*} [Group H] [Finite H]
    {V : Type u} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ρ : Representation F H V) (hρ : Function.Injective ρ)
    (E D : Subgroup H) (hE : E ≠ ⊥) (hE2 : IsPGroup 2 E)
    (q : ℕ) (hD : Nat.card D = q) (hq : q.Prime) (hq3 : 3 < q)
    (hcomm : ⁅E, D⁆ = E) (h2 : (2 : F) ≠ 0) (hdim : Module.finrank F V < q) :
    ∃ (J : Type u) (_ : Group J) (_ : Finite J) (W : Type u) (_ : AddCommGroup W)
      (_ : Module F W) (_ : FiniteDimensional F W) (_ : Nontrivial W)
      (τ : Representation F J W) (Q X : Subgroup J),
      Function.Injective τ ∧ Module.finrank F W ≤ Module.finrank F V ∧ Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
        Nat.card X = q ∧ ⁅Q, X⁆ = Q ∧ Representation.IsIrreducible (τ.comp Q.subtype) := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fact (Nat.card D).Prime := ⟨hD ▸ hq⟩
  haveI : IsCyclic D := isCyclic_of_prime_card hD
  obtain ⟨d0, hd0⟩ := IsCyclic.exists_generator (α := D)
  set d : H := (d0 : H) with hd
  have hdD : d ∈ D := d0.2
  have hDz : D = Subgroup.zpowers d := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := hd0 ⟨x, hx⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    · rintro ⟨k, rfl⟩
      exact D.zpow_mem hdD k
  have hdq : d ^ q = 1 := by
    have := pow_card_eq_one' (G := D) (x := d0)
    rw [hD] at this
    simpa using congrArg Subtype.val this
  have hnorm : ∀ x ∈ D, ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    have h1 : ⁅x, e⁆ ∈ ⁅D, E⁆ := Subgroup.commutator_mem_commutator hx he
    rw [Subgroup.commutator_comm, hcomm] at h1
    have : x * e * x⁻¹ = ⁅x, e⁆ * e := by simp [commutatorElement_def, mul_assoc]
    rw [this]
    exact E.mul_mem h1 he
  let σ : Representation F E V := ρ.comp E.subtype
  let α : MulAut E :=
    { toFun := fun e => ⟨d * e * d⁻¹, hnorm d hdD e e.2⟩
      invFun := fun e => ⟨d⁻¹ * e * d, by simpa using hnorm d⁻¹ (D.inv_mem hdD) e e.2⟩
      left_inv := fun e => by ext; simp [mul_assoc]
      right_inv := fun e => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  have hαpow : ∀ n : ℕ, ∀ e : E, (((α ^ n) e : E) : H) = d ^ n * e * (d ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      rw [pow_succ, MulAut.mul_apply, ih]
      show d ^ n * (d * e * d⁻¹) * (d ^ n)⁻¹ = _
      simp [pow_succ, mul_assoc]
  have hα : α ^ q = 1 := by
    ext e
    rw [hαpow, hdq]; simp
  let T : V ≃ₗ[F] V := LinearMap.GeneralLinearGroup.generalLinearEquiv F V (ρ.toHomUnits d)
  have hTv : ∀ v, T v = ρ d v := fun v => rfl
  have hT : T ^ q = 1 := by
    rw [← map_pow, ← map_pow, hdq, map_one, map_one]
  have hcov : ∀ e v, T (σ e v) = σ (α e) (T v) := by
    intro e v
    rw [hTv, hTv]
    show ρ d (ρ e v) = ρ (d * e * d⁻¹) (ρ d v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp
  obtain ⟨n, hn⟩ := hE2.exists_card_eq
  have hcard : (Nat.card E : F) ≠ 0 := by
    rw [hn]; push_cast; exact pow_ne_zero _ h2
  obtain ⟨e0, he0⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE
  have hσe0 : σ (e0 : E) ≠ 1 := fun h => he0 (Subtype.ext (hρ (by simpa [σ] using h)))
  obtain ⟨W1, hW1, hW1n, hW1irr, hW1e⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.CoprimeIrreducibleConstituentSeparates.exists_constituent σ hcard _ hσe0
  obtain ⟨S0, hS0, ⟨θ⟩⟩ := exists_simple σ W1 hW1 hW1irr
  obtain ⟨W, hWne, hWE, hWT, hWE', hWirr, ⟨θ2⟩⟩ :=
    CFSG.LinearAlgebra.CoprimeActions.SmallDimensionStableIrreducibleImage.exists_image σ hcard α q
      hα T hT hcov hdim S0
  have hWe0 : Representation.subrepresentation σ W hWE' e0 ≠ 1 :=
    fun h => hW1e (eq_one_of_equiv _ _ (θ2.trans θ.symm) _ h)

  have hstabE : ∀ e ∈ E, ∀ w ∈ W, ρ e w ∈ W := fun e he w hw => hWE ⟨e, he⟩ hw
  have hpow : ∀ h : H, (∀ w ∈ W, ρ h w ∈ W) → ∀ n : ℕ, ∀ w ∈ W, ρ (h ^ n) w ∈ W := by
    intro h hh n
    induction n with
    | zero => intro w hw; simpa using hw
    | succ n ih =>
      intro w hw
      rw [pow_succ', map_mul, Module.End.mul_apply]
      exact hh _ (ih w hw)
  have hstabD : ∀ x ∈ D, ∀ w ∈ W, ρ x w ∈ W := by
    intro x hx w hw
    rw [hDz, ← mem_powers_iff_mem_zpowers] at hx
    obtain ⟨k, rfl⟩ := hx
    exact hpow d (fun w hw => hWT hw) k w hw
  let S : Subgroup H :=
    { carrier := {h | ∀ w ∈ W, ρ h w ∈ W}
      mul_mem' := fun {a b} ha hb w hw => by
        have := ha _ (hb w hw)
        simpa using this
      one_mem' := fun w hw => by simpa using hw
      inv_mem' := fun {h} hh => by
        have h1 : h⁻¹ = h ^ (Nat.card H - 1) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_succ', Nat.sub_add_cancel Nat.card_pos]
          exact pow_card_eq_one'
        rw [h1]
        exact hpow h hh _ }
  set H0 : Subgroup H := E ⊔ D with hH0
  have hH0S : H0 ≤ S := sup_le (fun e he w hw => hstabE e he w hw) (fun x hx w hw => hstabD x hx w hw)
  have hWH : ∀ h : H0, W ≤ W.comap ((ρ.comp H0.subtype) h) := fun h w hw => hH0S h.2 w hw
  let τ0 : Representation F H0 W := Representation.subrepresentation (ρ.comp H0.subtype) W hWH
  let f : H0 →* imageGroup τ0 := toImage τ0
  let E0 : Subgroup H0 := E.subgroupOf H0
  let D0 : Subgroup H0 := D.subgroupOf H0
  have hcommH0 : ⁅E0, D0⁆ = E0 := by
    apply Subgroup.map_injective H0.subtype_injective
    rw [Subgroup.map_commutator]
    simp only [E0, D0, Subgroup.subgroupOf_map_subtype]
    rw [inf_eq_left.2 (le_sup_left : E ≤ H0), inf_eq_left.2 (le_sup_right : D ≤ H0), hcomm]
  have hE0p : IsPGroup 2 E0 := hE2.comap_subtype
  have hD0card : Nat.card D0 = q := by
    rw [← hD]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : D ≤ H0)).toEquiv
  have hQp : IsPGroup 2 (E0.map f) := hE0p.map f
  let e0' : H0 := ⟨e0, (le_sup_left : E ≤ H0) e0.2⟩
  have hQne : E0.map f ≠ ⊥ := by
    intro h
    have hm : f e0' ∈ E0.map f := Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.2 e0.2)
    rw [h, Subgroup.mem_bot] at hm
    apply hWe0
    have : τ0 e0' = faithful τ0 (f e0') := (faithful_toImage τ0 e0').symm
    rw [hm, map_one] at this
    exact this
  have hcommQ : ⁅E0.map f, D0.map f⁆ = E0.map f := by
    rw [← Subgroup.map_commutator, hcommH0]
  haveI : Fact (Nat.card D0).Prime := ⟨hD0card ▸ hq⟩
  have hXcard : Nat.card (D0.map f) = q := by
    rcases (MonoidHom.ker (f.domRestrict D0)).eq_bot_or_eq_top_of_prime_card with h | h
    · rw [← hD0card]
      have hinj : Function.Injective (f.domRestrict D0) := (MonoidHom.ker_eq_bot_iff _).1 h
      refine (Nat.card_congr (Equiv.ofBijective (f.subgroupMap D0) ⟨?_, ?_⟩)).symm
      · intro x y hxy
        apply hinj
        exact Subtype.ext_iff.1 hxy
      · exact f.subgroupMap_surjective D0
    · exfalso
      have hX : D0.map f = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        have : (⟨x, hx⟩ : D0) ∈ MonoidHom.ker (f.domRestrict D0) := by rw [h]; trivial
        exact (MonoidHom.mem_ker.1 this)
      rw [hX, Subgroup.commutator_bot_right] at hcommQ
      exact hQne hcommQ.symm
  have hirr : Representation.IsIrreducible
      ((faithful τ0).comp (E0.map f).subtype) := by
    refine irreducible_congr (Representation.subrepresentation σ W hWE') _ ?_ ?_ hWirr
    · intro e
      refine ⟨⟨f ⟨e, (le_sup_left : E ≤ H0) e.2⟩, Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.2 e.2)⟩, ?_⟩
      show faithful τ0 (f _) = _
      rw [faithful_toImage]
      ext w
      rfl
    · intro g
      obtain ⟨x, hx, hfx⟩ := Subgroup.mem_map.1 g.2
      refine ⟨⟨x.1, Subgroup.mem_subgroupOf.1 hx⟩, ?_⟩
      show _ = faithful τ0 (g : imageGroup τ0)
      rw [← hfx]
      show _ = faithful τ0 (f x)
      rw [faithful_toImage]
      ext w
      rfl
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hWne
  haveI : Finite (imageGroup τ0) := Finite.of_surjective _ (toImage_surjective τ0)
  exact ⟨imageGroup τ0, inferInstance, inferInstance, W, inferInstance, inferInstance, inferInstance,
    inferInstance, faithful τ0, E0.map f, D0.map f, faithful_injective τ0, Submodule.finrank_le W,
    hQne, hQp, hXcard, hcommQ, hirr⟩

end CFSG.LinearAlgebra.CoprimeActions.IrreduciblePrimeNormalizerImage
