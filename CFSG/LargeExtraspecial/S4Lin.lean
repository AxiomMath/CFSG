module

public import CFSG.LargeExtraspecial.OrthoF2Fixed

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Module CFSG.RankThree.OrthogonalInvolutions

variable {U A : Type*} [AddCommGroup U] [Module (ZMod 2) U] [FiniteDimensional (ZMod 2) U]
  [Group A]

theorem mem_span_singleton_subtype {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {U : Submodule (ZMod 2) V} {c v : U} :
    v ∈ (ZMod 2) ∙ c ↔ (v : V) ∈ (ZMod 2) ∙ (c : V) := by
  rw [Submodule.mem_span_singleton, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext hk⟩

theorem finite_linearEquiv_of_finite {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Finite (W ≃ₗ[ZMod 2] W) :=
  Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W)) fun _ _ h =>
    LinearEquiv.ext (congrFun h)

theorem commSpace_eq_of_transvections (ψ : A →* (U ≃ₗ[ZMod 2] U)) (c : U)
    (hψ : ∀ x u, ψ x u - u ∈ (ZMod 2) ∙ c) {a : U ≃ₗ[ZMod 2] U} (ha : a ∈ ψ.range)
    (ha1 : a ≠ 1) : commSpace a = (ZMod 2) ∙ c := by
  obtain ⟨x, rfl⟩ := ha
  have hle : commSpace (ψ x) ≤ (ZMod 2) ∙ c := by
    intro w hw
    obtain ⟨u, rfl⟩ := mem_commSpace.mp hw
    exact hψ x u
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  have h1 : finrank (ZMod 2) ((ZMod 2) ∙ c) ≤ 1 := by
    by_cases hc : c = 0
    · rw [hc, Submodule.span_singleton_eq_bot.mpr rfl, finrank_bot]
      exact zero_le_one
    · rw [finrank_span_singleton hc]
  exact h1.trans (one_le_finrank_commSpace ha1)

theorem card_range_of_transvections [Finite A] (hA : IsPGroup 2 A)
    (ψ : A →* (U ≃ₗ[ZMod 2] U)) (c : U) (hψ : ∀ x u, ψ x u - u ∈ (ZMod 2) ∙ c) :
    Nat.card ψ.range = 2 ^ (finrank (ZMod 2) U - finrank (ZMod 2) (fixSpaceOf ψ.range)) ∧
      finrank (ZMod 2) (fixSpaceOf ψ.range) ≤ finrank (ZMod 2) U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ψ.range := Finite.of_surjective _ ψ.rangeRestrict_surjective
  obtain ⟨r, hr⟩ := (hA.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective).exists_card_eq
  have h := timmesfeld_3_1_two ψ.range (r := r) (by rw [← hr]) (x := c)
    (fun a ha ha1 => commSpace_eq_of_transvections ψ c hψ ha ha1)
  refine ⟨?_, ?_⟩
  · rw [show Nat.card ψ.range = Nat.card (ψ.range : Subgroup (U ≃ₗ[ZMod 2] U)) from rfl]
    rw [show (Nat.card (ψ.range : Subgroup (U ≃ₗ[ZMod 2] U))) = 2 ^ r from hr, h.1]
    congr 1
    omega
  · rw [h.1]
    omega

theorem finrank_le_of_transvections [Finite A] (hA : IsPGroup 2 A)
    (ψ : A →* (U ≃ₗ[ZMod 2] U)) (c : U) (hψ : ∀ x u, ψ x u - u ∈ (ZMod 2) ∙ c) {r : ℕ}
    (hr : Nat.card A ≤ 2 ^ r) :
    finrank (ZMod 2) U ≤ finrank (ZMod 2) (fixSpaceOf ψ.range) + r := by
  obtain ⟨h1, h2⟩ := card_range_of_transvections hA ψ c hψ
  have h3 : Nat.card ψ.range ≤ 2 ^ r :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.card_range_dvd ψ)).trans hr
  rw [h1] at h3
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

omit [FiniteDimensional (ZMod 2) U] in
theorem mem_fixSpaceOf_range {ψ : A →* (U ≃ₗ[ZMod 2] U)} {u : U} :
    u ∈ fixSpaceOf ψ.range ↔ ∀ x, ψ x u = u := by
  rw [mem_fixSpaceOf]
  constructor
  · intro h x
    exact h _ ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

omit [FiniteDimensional (ZMod 2) U] in
variable (U) in
@[expose] def centreGroup (c : U) : Subgroup (U ≃ₗ[ZMod 2] U) where
  carrier := {e | ∀ u, e u - u ∈ (ZMod 2) ∙ c}
  mul_mem' := fun {e f} he hf u => by
    have : (e * f) u - u = (e (f u) - f u) + (f u - u) := by
      rw [LinearEquiv.mul_apply]
      abel
    rw [this]
    exact add_mem (he _) (hf u)
  one_mem' := fun u => by simp
  inv_mem' := fun {e} he u => by
    have : e⁻¹ u - u = -(e (e⁻¹ u) - e⁻¹ u) := by
      rw [show e (e⁻¹ u) = u from e.apply_symm_apply u]
      abel
    rw [this]
    exact neg_mem (he _)

omit [FiniteDimensional (ZMod 2) U] in
theorem mem_centreGroup {c : U} {e : U ≃ₗ[ZMod 2] U} :
    e ∈ centreGroup U c ↔ ∀ u, e u - u ∈ (ZMod 2) ∙ c :=
  Iff.rfl

omit [FiniteDimensional (ZMod 2) U] in
theorem transvection_mem_centreGroup {c : U} {φ : Module.Dual (ZMod 2) U} (h : φ c = 0) :
    LinearEquiv.transvection h ∈ centreGroup U c := by
  intro u
  rw [LinearEquiv.transvection.apply, add_sub_cancel_left]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c)

omit [FiniteDimensional (ZMod 2) U] in
theorem apply_centre_of_mem_centreGroup {c : U} (hc : c ≠ 0) {e : U ≃ₗ[ZMod 2] U}
    (he : e ∈ centreGroup U c) : e c = c := by
  rcases OrthoF2.mem_span_singleton_iff.mp (he c) with h | h
  · exact sub_eq_zero.mp h
  · exfalso
    have : e c = 0 := by
      calc e c = (e c - c) + c := (sub_add_cancel _ _).symm
        _ = 0 := by rw [h, OrthoF2.vec_add_self]
    exact hc (e.injective (this.trans (map_zero e).symm))

omit [FiniteDimensional (ZMod 2) U] in
theorem mul_self_of_mem_centreGroup {c : U} (hc : c ≠ 0) {e : U ≃ₗ[ZMod 2] U}
    (he : e ∈ centreGroup U c) : e * e = 1 := by
  refine LinearEquiv.ext fun u => ?_
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp (he u)
  have heu : e u = u + k • c := by rw [hk]; abel
  rw [LinearEquiv.mul_apply, heu, map_add, map_smul, apply_centre_of_mem_centreGroup hc he, heu,
    add_assoc, ← add_smul, CFSG.LargeExtraspecial.OrthoF2.zmod2_add_self, zero_smul, add_zero]
  rfl

theorem card_centreGroup {c : U} (hc : c ≠ 0) :
    Nat.card (centreGroup U c) = 2 ^ (finrank (ZMod 2) U - 1) := by
  have : Finite U := Module.finite_of_finite (ZMod 2)
  have : Finite (U ≃ₗ[ZMod 2] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod 2] U => (e : U → U)) fun _ _ h =>
      LinearEquiv.ext (congrFun h)
  have h2 : IsPGroup 2 (centreGroup U c) := fun e => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, pow_two, mul_self_of_mem_centreGroup hc e.2]; rfl)⟩
  have hψ : ∀ (x : centreGroup U c) u, (centreGroup U c).subtype x u - u ∈ (ZMod 2) ∙ c :=
    fun x u => x.2 u
  obtain ⟨h1, -⟩ := card_range_of_transvections h2 (centreGroup U c).subtype c hψ
  rw [Subgroup.range_subtype] at h1
  have hfix : fixSpaceOf (centreGroup U c) = (ZMod 2) ∙ c := by
    apply le_antisymm
    · intro v hv
      by_contra hvc
      obtain ⟨φ, hφv, hφc⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hvc inferInstance
      have hφc' : φ c = 0 := by
        have : φ c ∈ ((ZMod 2) ∙ c).map φ := ⟨c, Submodule.mem_span_singleton_self c, rfl⟩
        rw [hφc] at this
        exact this
      have := (mem_fixSpaceOf.mp hv) _ (transvection_mem_centreGroup hφc')
      rw [LinearEquiv.transvection.apply, add_eq_left, smul_eq_zero] at this
      rcases this with h | h
      · exact hφv h
      · exact hc h
    · rw [Submodule.span_singleton_le_iff_mem, mem_fixSpaceOf]
      intro e he
      exact apply_centre_of_mem_centreGroup hc he
  rw [h1, hfix, finrank_span_singleton hc]

end CFSG.LargeExtraspecial.S4
