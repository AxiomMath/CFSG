module

public import CFSG.CharacterTheory.Semidihedral.DefiningCharacteristicDimension

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open scoped IsMulCommutative

theorem sq_dvd_card_of_sl2_inverting {G : Type} [Group G] [Finite G] {F : Type} [Field F]
    [Finite F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f) (hF : Nat.card F = p ^ f)
    (hq : 5 ≤ p ^ f) (J Q : Subgroup G) (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hQ : IsPGroup p Q) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hJQ : J ≤ Subgroup.normalizer (Q : Set G))
    (hinv : ∀ x ∈ Q, (e.symm (-1) : G) * x * (e.symm (-1) : G)⁻¹ = x⁻¹) (hQ1 : Q ≠ ⊥) :
    (p ^ f) ^ 2 ∣ Nat.card Q := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let Ω : Subgroup G :=
    { carrier := {x | x ∈ Q ∧ x ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Q.mul_mem ha hb, ?_⟩
        have hc : Commute a b := hQab a ha b hb
        rw [hc.mul_pow, ha', hb', one_mul]
      one_mem' := ⟨Q.one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨Q.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hΩQ : Ω ≤ Q := fun x hx => hx.1
  have hΩea : IsElementaryAbelian p Ω :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hQab a (hΩQ a.2) b (hΩQ b.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a =>
        Subtype.ext (by simpa using a.2.2) }
  obtain ⟨x₀, hx₀⟩ : ∃ x : Q, orderOf x = p := by
    have : Nontrivial Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQ1
    have := Fintype.ofFinite Q
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact (Finite.one_lt_card (α := Q)).ne' hk
    exact exists_prime_orderOf_dvd_card p (by
      rw [← Nat.card_eq_fintype_card, hk]
      exact dvd_pow_self p hk0)
  have hx₀Ω : (x₀ : G) ∈ Ω := ⟨x₀.2, by
    rw [← Subgroup.coe_pow, ← hx₀, pow_orderOf_eq_one, Subgroup.coe_one]⟩
  have hx₀1 : (x₀ : G) ≠ 1 := by
    intro h
    have : x₀ = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx₀
    exact hp.one_lt.ne hx₀
  have hJΩ : ∀ j ∈ J, ∀ x ∈ Ω, j * x * j⁻¹ ∈ Ω := fun j hj x hx =>
    ⟨(Subgroup.mem_normalizer_iff.mp (hJQ hj) x).mp hx.1, by
      rw [conj_pow, hx.2, mul_one, mul_inv_cancel]⟩
  let conjΩ : J → Ω →* Ω := fun j =>
    { toFun := fun x => ⟨j * x * (j : G)⁻¹, hJΩ j j.2 x x.2⟩
      map_one' := by
        ext
        simp
      map_mul' := fun a b => by
        ext
        show (j : G) * (a * b) * (j : G)⁻¹ = (j * a * (j : G)⁻¹) * (j * b * (j : G)⁻¹)
        group }
  let ρ : Representation (ZMod p) (Matrix.SpecialLinearGroup (Fin 2) F) (Additive Ω) :=
    { toFun := fun g => (MonoidHom.toAdditive (conjΩ (e.symm g))).toZModLinearMap p
      map_one' := by
        refine LinearMap.ext fun a => Additive.toMul.injective (Subtype.ext ?_)
        obtain ⟨x, rfl⟩ := Additive.ofMul.surjective a
        show ((e.symm 1 : J) : G) * (x : G) * ((e.symm 1 : J) : G)⁻¹ = (x : G)
        simp
      map_mul' := fun g h => by
        refine LinearMap.ext fun a => Additive.toMul.injective (Subtype.ext ?_)
        obtain ⟨x, rfl⟩ := Additive.ofMul.surjective a
        show ((e.symm (g * h) : J) : G) * (x : G) * ((e.symm (g * h) : J) : G)⁻¹ =
          ((e.symm g : J) : G) * (((e.symm h : J) : G) * (x : G) * ((e.symm h : J) : G)⁻¹) *
            ((e.symm g : J) : G)⁻¹
        simp only [map_mul, Subgroup.coe_mul]
        group }
  have hρ : ρ.asGroupHom (OddFieldSL2.minusIdentity F) ≠ 1 := by
    intro h1
    have h2 := congrArg (fun u : (Additive Ω →ₗ[ZMod p] Additive Ω)ˣ =>
      ((Additive.toMul ((u : Additive Ω →ₗ[ZMod p] Additive Ω)
        (Additive.ofMul ⟨(x₀ : G), hx₀Ω⟩)) : Ω) : G)) h1
    change ((e.symm (OddFieldSL2.minusIdentity F) : J) : G) * (x₀ : G) *
      ((e.symm (OddFieldSL2.minusIdentity F) : J) : G)⁻¹ = (x₀ : G) at h2
    have h3 := hinv (x₀ : G) x₀.2
    change ((e.symm (OddFieldSL2.minusIdentity F) : J) : G) * (x₀ : G) *
      ((e.symm (OddFieldSL2.minusIdentity F) : J) : G)⁻¹ = (x₀ : G)⁻¹ at h3
    rw [h2] at h3
    have h4 : (x₀ : G) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h3]
      exact inv_mul_cancel _
    have h5 := orderOf_dvd_of_pow_eq_one h4
    rw [Subgroup.orderOf_coe, hx₀] at h5
    have h6 := Nat.le_of_dvd (by norm_num) h5
    have := hp.two_le
    have hp2 : p = 2 := by omega
    rw [hp2] at hpodd
    exact absurd hpodd (by decide)
  have : Module.Finite (ZMod p) (Additive Ω) := Module.Finite.of_finite
  obtain ⟨-, -, -, hdim, -⟩ :=
    DefiningCharacteristicDimension.odd_defining_characteristic_SL2_action_minimum_dimension
      (k := ZMod p) (V := Additive Ω) hp hpodd hf hF hq (Nat.card_zmod p) ρ.asGroupHom hρ
  have hcardΩ : Nat.card Ω = p ^ Module.finrank (ZMod p) (Additive Ω) := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive Ω)
    rw [Nat.card_zmod] at h1
    exact h1
  have hΩdvd : Nat.card Ω ∣ Nat.card Q := Subgroup.card_dvd_of_le hΩQ
  rw [hcardΩ] at hΩdvd
  rw [← pow_mul, mul_comm]
  exact (pow_dvd_pow p hdim).trans hΩdvd

end CFSG.Semidihedral.FixedCoreNontrivial
