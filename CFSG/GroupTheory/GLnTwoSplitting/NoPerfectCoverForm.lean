module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.GroupTheory.GLnTwoSplitting.FirstCohomology
public import CFSG.GroupTheory.GLnTwoSplitting.NoPerfectCoverAbelian

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Subgroup

variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

@[expose] def contragredient {L : Type*} [Group L] (ρ : L →* (E ≃ₗ[ZMod 2] E)) :
    L →* (Dual (ZMod 2) E ≃ₗ[ZMod 2] Dual (ZMod 2) E) where
  toFun g := (ρ g⁻¹).dualMap
  map_one' := by
    ext f x
    simp [LinearEquiv.dualMap_apply]
  map_mul' g h := by
    ext f x
    simp [LinearEquiv.dualMap_apply, mul_inv_rev]

theorem contragredient_apply {L : Type*} [Group L] (ρ : L →* (E ≃ₗ[ZMod 2] E)) (g : L)
    (f : Dual (ZMod 2) E) (x : E) : contragredient ρ g f x = f (ρ g⁻¹ x) :=
  rfl

theorem exists_contragredient_eq_transvection [FiniteDimensional (ZMod 2) E] {L : Type*}
    [Group L] {ρ : L →* (E ≃ₗ[ZMod 2] E)} (hρ : Function.Surjective ρ)
    (F : Dual (ZMod 2) (Dual (ZMod 2) E)) (d : Dual (ZMod 2) E) (h : F d = 0) :
    ∃ l, contragredient ρ l = LinearEquiv.transvection h := by
  obtain ⟨w, rfl⟩ := (Module.evalEquiv (ZMod 2) E).surjective F
  have hev : ∀ f : Dual (ZMod 2) E, Module.evalEquiv (ZMod 2) E w f = f w := fun _ => rfl
  have hdw : d w = 0 := (hev d).symm.trans h
  obtain ⟨l, hl⟩ := hρ (LinearEquiv.transvection hdw)
  refine ⟨l, LinearEquiv.ext fun f => LinearMap.ext fun x => ?_⟩
  rw [contragredient_apply, map_inv, hl, transvection_inv, transvection_apply, transvection_apply,
    map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hev, smul_eq_mul, smul_eq_mul,
    mul_comm]

namespace NatExt

variable {G : Type*} [Group G] (X : NatExt G E) {C : Type*} [Group C] {p : C →* G}

@[expose] noncomputable def coord (p : C →* G) (v : C) : E :=
  Function.invFun X.ι (p v)

theorem coord_eq {v : C} {e : E} (h : p v = X.ι e) : X.coord p v = e := by
  rw [coord, h]
  exact Function.leftInverse_invFun X.injective e

theorem map_eq_ι_coord {v : C} (hv : X.π (p v) = 1) : p v = X.ι (X.coord p v) := by
  obtain ⟨e, he⟩ := X.exists_eq_ι_of_π_eq_one hv
  rw [X.coord_eq he, he]

theorem coord_mul {u v : C} (hu : X.π (p u) = 1) (hv : X.π (p v) = 1) :
    X.coord p (u * v) = X.coord p u + X.coord p v :=
  X.coord_eq (by rw [map_mul, X.map_eq_ι_coord hu, X.map_eq_ι_coord hv, X.ι_add])

theorem coord_eq_zero {z : C} (hz : z ∈ p.ker) : X.coord p z = 0 :=
  X.coord_eq (by rw [MonoidHom.mem_ker.1 hz, X.ι_zero])

theorem π_eq_one_of_mem_ker {z : C} (hz : z ∈ p.ker) : X.π (p z) = 1 := by
  rw [MonoidHom.mem_ker.1 hz, map_one]

theorem π_conj_eq_one {v : C} (hv : X.π (p v) = 1) (g : C) : X.π (p (g⁻¹ * v * g)) = 1 := by
  simp only [map_mul, map_inv, hv, mul_one, inv_mul_cancel]

theorem coord_conj {v : C} (hv : X.π (p v) = 1) (g : C) :
    X.coord p (g⁻¹ * v * g) = X.π (p g⁻¹) (X.coord p v) := by
  apply X.coord_eq
  have h := X.map_conj_eq_ι (X.map_eq_ι_coord hv) g⁻¹
  rwa [inv_inv] at h

open scoped IsMulCommutative in
theorem exists_section_form (hp : Function.Surjective p)
    (hcomm : ∀ a b : C, X.π (p a) = 1 → X.π (p b) = 1 → a * b = b * a)
    (hsq : ∀ a : C, X.π (p a) = 1 → a * a = 1) {ζ : C} (hζ : ζ ∈ p.ker) (hζ1 : ζ ≠ 1) :
    ∃ (s : E → C) (Φ : C → ZMod 2), (∀ e, p (s e) = X.ι e) ∧
      (∀ e e', s (e + e') = s e * s e') ∧
      (∀ u v, X.π (p u) = 1 → X.π (p v) = 1 → Φ (u * v) = Φ u + Φ v) ∧ Φ ζ = 1 := by
  classical
  let V := (X.π.comp p).ker
  have hV : ∀ v : V, X.π (p v) = 1 := fun v => v.2
  have : IsMulCommutative V := ⟨⟨fun a b => Subtype.ext (hcomm _ _ (hV a) (hV b))⟩⟩
  have : IsElementaryAbelian 2 V :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun v =>
        Subtype.ext (by
          change (v : C) ^ 2 = 1
          rw [pow_two]
          exact hsq _ (hV v)) }
  let θ : Additive V →+ E := AddMonoidHom.mk' (fun v => X.coord p ((Additive.toMul v : V) : C))
    fun u v => X.coord_mul (hV (Additive.toMul u)) (hV (Additive.toMul v))
  obtain ⟨σ, hσ⟩ := (θ.toZModLinearMap 2).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 fun e => by
      obtain ⟨v, hv⟩ := hp (X.ι e)
      exact ⟨Additive.ofMul ⟨v, show X.π (p v) = 1 by rw [hv, X.π_ι]⟩, X.coord_eq hv⟩)
  have hζV : X.π (p ζ) = 1 := X.π_eq_one_of_mem_ker hζ
  obtain ⟨φ, -, hφ⟩ := exists_dual_eq_one_of_notMem (S := ⊥)
    (w := Additive.ofMul (⟨ζ, hζV⟩ : V)) fun h =>
      hζ1 (congrArg (fun a : Additive V => ((Additive.toMul a : V) : C))
        ((Submodule.mem_bot (ZMod 2)).1 h))
  let Φ : C → ZMod 2 := fun v => if hv : X.π (p v) = 1 then φ (Additive.ofMul ⟨v, hv⟩) else 0
  have hΦ : ∀ v (hv : X.π (p v) = 1), Φ v = φ (Additive.ofMul ⟨v, hv⟩) :=
    fun _ hv => dite_eq_left hv
  refine ⟨fun e => ((Additive.toMul (σ e) : V) : C), Φ, fun e => ?_, fun e e' => ?_,
    fun u v hu hv => ?_, by rw [hΦ ζ hζV]; exact hφ⟩
  · show p ((Additive.toMul (σ e) : V) : C) = X.ι e
    rw [X.map_eq_ι_coord (hV (Additive.toMul (σ e)))]
    exact congrArg X.ι (LinearMap.congr_fun hσ e)
  · exact congrArg (fun x : Additive V => ((Additive.toMul x : V) : C)) (map_add σ e e')
  · rw [hΦ (u * v) (by rw [map_mul, map_mul, hu, hv, mul_one]), hΦ u hu, hΦ v hv]
    exact map_add φ (Additive.ofMul ⟨u, hu⟩) (Additive.ofMul ⟨v, hv⟩)

theorem exists_invariant_form [FiniteDimensional (ZMod 2) E] (hE : 4 ≤ finrank (ZMod 2) E)
    (hp : Function.Surjective p) (hcen : p.ker ≤ center C)
    (hcomm : ∀ a b : C, X.π (p a) = 1 → X.π (p b) = 1 → a * b = b * a)
    {s : E → C} {Φ : C → ZMod 2} (hs : ∀ e, p (s e) = X.ι e)
    (hs' : ∀ e e', s (e + e') = s e * s e')
    (hΦ : ∀ u v, X.π (p u) = 1 → X.π (p v) = 1 → Φ (u * v) = Φ u + Φ v) :
    ∃ Ψ : C → ZMod 2, (∀ u v, X.π (p u) = 1 → X.π (p v) = 1 → Ψ (u * v) = Ψ u + Ψ v) ∧
      (∀ z ∈ p.ker, Ψ z = Φ z) ∧ ∀ g v, X.π (p v) = 1 → Ψ (g⁻¹ * v * g) = Ψ v := by
  have hsV : ∀ e, X.π (p (s e)) = 1 := fun e => by rw [hs, X.π_ι]
  have hadd : ∀ g e e', Φ (g⁻¹ * s (e + e') * g) + Φ (s (e + e')) =
      (Φ (g⁻¹ * s e * g) + Φ (s e)) + (Φ (g⁻¹ * s e' * g) + Φ (s e')) := fun g e e' => by
    have h1 : g⁻¹ * s (e + e') * g = g⁻¹ * s e * g * (g⁻¹ * s e' * g) := by rw [hs']; group
    rw [h1, hΦ _ _ (X.π_conj_eq_one (hsV e) g) (X.π_conj_eq_one (hsV e') g), hs',
      hΦ _ _ (hsV e) (hsV e')]
    ring
  let δ : C → Dual (ZMod 2) E := fun g =>
    (AddMonoidHom.mk' (fun e => Φ (g⁻¹ * s e * g) + Φ (s e)) (hadd g)).toZModLinearMap 2
  have hδ : ∀ g e, δ g e = Φ (g⁻¹ * s e * g) + Φ (s e) := fun _ _ => rfl
  have hkey : ∀ g v, X.π (p v) = 1 → δ g (X.coord p v) = Φ (g⁻¹ * v * g) + Φ v := by
    intro g v hv
    have hz : (s (X.coord p v))⁻¹ * v ∈ p.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hs, ← X.map_eq_ι_coord hv, inv_mul_cancel]
    have hzc := mem_center_iff.1 (hcen hz)
    have hzπ := X.π_eq_one_of_mem_ker hz
    have hsc := hsV (X.coord p v)
    have e1 : Φ v = Φ (s (X.coord p v)) + Φ ((s (X.coord p v))⁻¹ * v) := by
      rw [← hΦ _ _ hsc hzπ, mul_inv_cancel_left]
    have e2 : Φ (g⁻¹ * v * g) =
        Φ (g⁻¹ * s (X.coord p v) * g) + Φ ((s (X.coord p v))⁻¹ * v) := by
      rw [← hΦ _ _ (X.π_conj_eq_one hsc g) hzπ]
      congr 1
      calc g⁻¹ * v * g = g⁻¹ * s (X.coord p v) * ((s (X.coord p v))⁻¹ * v * g) := by group
        _ = g⁻¹ * s (X.coord p v) * (g * ((s (X.coord p v))⁻¹ * v)) := by rw [hzc g]
        _ = g⁻¹ * s (X.coord p v) * g * ((s (X.coord p v))⁻¹ * v) := by group
    have key : ∀ a b c : ZMod 2, a + b = a + c + (b + c) := by decide
    rw [hδ, e1, e2]
    exact key _ _ _
  have hcoc : ∀ g h, δ (g * h) = δ g + contragredient (X.π.comp p) g (δ h) := by
    intro g h
    ext e
    have hc : X.π (p g⁻¹) e = X.coord p (g⁻¹ * s e * g) := by
      rw [X.coord_conj (hsV e) g, X.coord_eq (hs e)]
    have hgh : (g * h)⁻¹ * s e * (g * h) = h⁻¹ * (g⁻¹ * s e * g) * h := by group
    have key : ∀ a b c : ZMod 2, a + b = c + b + (a + c) := by decide
    rw [LinearMap.add_apply, contragredient_apply, MonoidHom.comp_apply, hδ (g * h) e, hδ g e, hc,
      hkey h _ (X.π_conj_eq_one (hsV e) g), hgh]
    exact key _ _ _
  have hker : ∀ g, contragredient (X.π.comp p) g = 1 → δ g = 0 := by
    intro g hg
    have hg' : X.π (p g) = 1 := by
      have h0 : ∀ x, X.π (p g⁻¹) x = x := fun x => by
        refine sub_eq_zero.1 ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).1 fun f => ?_)
        have h2 := congrArg (fun F : Dual (ZMod 2) E ≃ₗ[ZMod 2] Dual (ZMod 2) E => F f x) hg
        simp only [contragredient_apply, MonoidHom.comp_apply, LinearEquiv.coe_one, id_eq] at h2
        rw [map_sub, h2, sub_self]
      have h1 : X.π (p g⁻¹) = 1 := LinearEquiv.ext h0
      rwa [map_inv, map_inv, inv_eq_one] at h1
    ext e
    rw [hδ, LinearMap.zero_apply, mul_assoc, hcomm _ _ (hsV e) hg', inv_mul_cancel_left]
    exact zmod_two_add_self _
  have hE' : 4 ≤ finrank (ZMod 2) (Dual (ZMod 2) E) := by
    rw [Subspace.dual_finrank_eq]
    exact hE
  obtain ⟨w, hw⟩ := exists_eq_of_isCocycle hE' (contragredient (X.π.comp p))
    (exists_contragredient_eq_transvection (X.surjective.comp hp)) δ hcoc hker
  let Ψ : C → ZMod 2 := fun v => Φ v + w (X.coord p v)
  have hΨ : ∀ v, Ψ v = Φ v + w (X.coord p v) := fun _ => rfl
  refine ⟨Ψ, fun u v hu hv => ?_, fun z hz => ?_, fun g v hv => ?_⟩
  · rw [hΨ, hΨ, hΨ, hΦ u v hu hv, X.coord_mul hu hv, map_add]
    ring
  · rw [hΨ, X.coord_eq_zero hz, map_zero, add_zero]
  · have h1 := hkey g v hv
    rw [hw g, LinearMap.add_apply, contragredient_apply, MonoidHom.comp_apply] at h1
    have key : ∀ a b c d : ZMod 2, b + c = a + d → a + b = d + c := by decide
    rw [hΨ, hΨ, X.coord_conj hv g]
    exact key _ _ _ _ h1

theorem exists_normal_complement [FiniteDimensional (ZMod 2) E] (hE : 4 ≤ finrank (ZMod 2) E)
    (hp : Function.Surjective p) (hcen : p.ker ≤ center C) (hsq : ∀ z ∈ p.ker, z * z = 1)
    {ζ : C} (hζ : ζ ∈ p.ker) (hζ1 : ζ ≠ 1) :
    ∃ W : Subgroup C, W.Normal ∧ (∀ v ∈ W, X.π (p v) = 1) ∧ ζ ∉ W ∧
      ∀ v, X.π (p v) = 1 → v ∈ W ∨ v * ζ ∈ W := by
  have hE3 : 3 ≤ finrank (ZMod 2) E := by omega
  have hcomm : ∀ a b : C, X.π (p a) = 1 → X.π (p b) = 1 → a * b = b * a :=
    fun _ _ ha hb => X.commute_of_π_eq_one hp hcen hE3 ha hb
  have hsqV : ∀ a : C, X.π (p a) = 1 → a * a = 1 :=
    fun _ ha => X.mul_self_eq_one_of_π_eq_one hp hcen hE3 hsq ha
  obtain ⟨s, Φ, hs, hs', hΦ, hΦζ⟩ := X.exists_section_form hp hcomm hsqV hζ hζ1
  obtain ⟨Ψ, hΨ, hΨk, hΨc⟩ := X.exists_invariant_form hE hp hcen hcomm hs hs' hΦ
  have hmul : ∀ u v, X.π (p u) = 1 → X.π (p v) = 1 → X.π (p (u * v)) = 1 :=
    fun u v hu hv => by rw [map_mul, map_mul, hu, hv, mul_one]
  have hζπ := X.π_eq_one_of_mem_ker hζ
  have hΨζ : Ψ ζ = 1 := by rw [hΨk ζ hζ, hΦζ]
  let W : Subgroup C :=
    { carrier := {v | X.π (p v) = 1 ∧ Ψ v = 0}
      mul_mem' := fun {u v} hu hv => ⟨hmul u v hu.1 hv.1, by rw [hΨ u v hu.1 hv.1, hu.2, hv.2,
        add_zero]⟩
      one_mem' := by
        have h1 : X.π (p 1) = 1 := by rw [map_one, map_one]
        have h2 := hΨ 1 1 h1 h1
        rw [mul_one] at h2
        exact ⟨h1, by
          have key : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
          exact key _ h2⟩
      inv_mem' := fun {v} hv => by rwa [inv_eq_of_mul_eq_one_right (hsqV v hv.1)] }
  have hW : ∀ v, v ∈ W ↔ X.π (p v) = 1 ∧ Ψ v = 0 := fun _ => Iff.rfl
  refine ⟨W, ⟨fun v hv g => ?_⟩, fun v hv => ((hW v).1 hv).1, fun h => ?_, fun v hv => ?_⟩
  · obtain ⟨hv1, hv2⟩ := (hW v).1 hv
    have h1 := X.π_conj_eq_one hv1 g⁻¹
    have h2 := hΨc g⁻¹ v hv1
    rw [inv_inv] at h1 h2
    exact (hW _).2 ⟨h1, h2.trans hv2⟩
  · rw [hW, hΨζ] at h
    exact one_ne_zero h.2
  · by_cases h0 : Ψ v = 0
    · exact Or.inl ((hW v).2 ⟨hv, h0⟩)
    · refine Or.inr ((hW _).2 ⟨hmul v ζ hv hζπ, ?_⟩)
      rw [hΨ v ζ hv hζπ, hΨζ, zmod_two_eq_one_of_ne_zero h0, zmod_two_add_self]

end NatExt

end CFSG.GroupTheory.GLnTwoSplitting
