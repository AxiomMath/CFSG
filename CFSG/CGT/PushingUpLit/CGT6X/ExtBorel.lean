module

public import CFSG.CGT.PushingUpLit.CGT6X.ExtCocycle
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightSL

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open Matrix CFSG.SL2MinimalFaithful CFSG.CGT.PushingUpLit.CGT6.TwoEight

section Borel

variable (K : Type*) [Field K]

@[expose] def borel : Subgroup (SpecialLinearGroup (Fin 2) K) where
  carrier := {A | (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB
    have hA' : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hA
    have hB' : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hB
    show ((A * B : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hA', hB']
  inv_mem' := by
    intro A hA
    have hA' : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hA
    show ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [hA']

@[expose] def diagHom : Kˣ →* SpecialLinearGroup (Fin 2) K where
  toFun a := diagSL (a : K) a.ne_zero
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [coe_diagSL]
  map_mul' a b := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

variable {K}

theorem diagHom_apply (a : Kˣ) : diagHom K a = diagSL (a : K) a.ne_zero := rfl

theorem diagHom_injective : Function.Injective (diagHom K) := by
  intro a b h
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) K =>
    (A : Matrix (Fin 2) (Fin 2) K) 0 0) h
  simpa [diagHom_apply, coe_diagSL, Units.ext_iff] using this

theorem unipotent_mul_diagHom_mem (x : K) (a : Kˣ) :
    unipotent x * diagHom K a ∈ borel K := by
  show ((unipotent x * diagHom K a : SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  simp [diagHom_apply, coe_diagSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]

@[expose] def borelEquiv : K × Kˣ ≃ borel K where
  toFun p := ⟨unipotent p.1 * diagHom K p.2, unipotent_mul_diagHom_mem p.1 p.2⟩
  invFun b :=
    ((b.1 : Matrix (Fin 2) (Fin 2) K) 0 1 * (b.1 : Matrix (Fin 2) (Fin 2) K) 0 0,
      ⟨(b.1 : Matrix (Fin 2) (Fin 2) K) 0 0, (b.1 : Matrix (Fin 2) (Fin 2) K) 1 1, by
        have h := b.1.2
        have h10 : (b.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := b.2
        rw [Matrix.det_fin_two, h10] at h
        linear_combination h, by
        have h := b.1.2
        have h10 : (b.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := b.2
        rw [Matrix.det_fin_two, h10] at h
        linear_combination h⟩)
  left_inv p := by
    obtain ⟨x, a⟩ := p
    simp [diagHom_apply, coe_diagSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two]
  right_inv b := by
    apply Subtype.ext
    have h := b.1.2
    have h10 : (b.1 : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := b.2
    rw [Matrix.det_fin_two, h10] at h
    have h0 : (b.1 : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 :=
      left_ne_zero_of_mul_eq_one (b := (b.1 : Matrix (Fin 2) (Fin 2) K) 1 1) (by
        linear_combination h)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagHom_apply, coe_diagSL, coe_unipotent, Matrix.mul_apply, Fin.sum_univ_two, h10]
    · field_simp
    · field_simp
      linear_combination -h

end Borel

section Index

variable {K : Type*} [Field K] [Finite K]

omit [Finite K] in
theorem card_borel : Nat.card (borel K) = Nat.card K * (Nat.card K - 1) := by
  rw [← Nat.card_congr (borelEquiv (K := K)), Nat.card_prod, Nat.card_units]

theorem borel_index : (borel K).index = Nat.card K + 1 := by
  have h := (borel K).card_mul_index
  rw [card_borel, card_specialLinearGroup_fin_two] at h
  have hq : 1 < Nat.card K := Finite.one_lt_card
  obtain ⟨r, hr⟩ : ∃ r, Nat.card K = r + 1 := ⟨Nat.card K - 1, by omega⟩
  rw [hr] at h ⊢
  have h1 : r + 1 - 1 = r := by omega
  have h2 : (r + 1) ^ 2 - 1 = r * (r + 2) := by
    have : (r + 1) ^ 2 = r * (r + 2) + 1 := by ring
    omega
  rw [h1, h2] at h
  have hpos : 0 < (r + 1) * r := Nat.mul_pos (by omega) (by omega)
  have h3 : (r + 1) * r * (borel K).index = (r + 1) * r * (r + 2) := by
    calc (r + 1) * r * (borel K).index = (r + 1) * (r * (r + 2)) := h
      _ = (r + 1) * r * (r + 2) := by ring
  exact Nat.eq_of_mul_eq_mul_left hpos h3

variable [CharP K 2]

theorem even_card_of_charTwo : Even (Nat.card K) := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact Nat.even_pow.2 ⟨even_two, n.pos.ne'⟩

theorem odd_borel_index : Odd (borel K).index := by
  rw [borel_index]
  exact even_card_of_charTwo.add_one

theorem odd_card_torus : Odd (Nat.card (diagHom K).range) := by
  rw [Nat.card_congr (MonoidHom.ofInjective (diagHom_injective (K := K))).symm.toEquiv,
    Nat.card_units]
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have := even_card_of_charTwo (K := K)
  obtain ⟨m, hm⟩ := this
  exact ⟨m - 1, by omega⟩

end Index

section Reduction

variable {K : Type*} [Field K] [Finite K] [CharP K 2] {V : Type*} [CommGroup V]

theorem coboundary_of_borel (hV : ∀ v : V, v ^ 2 = 1)
    (ρ : SpecialLinearGroup (Fin 2) K →* MulAut V)
    (key : ∀ f : K → V, f 0 = 1 → (∀ x y, f (x + y) = f x * ρ (unipotent x) (f y)) →
      (∀ (t : K) (ht : t ≠ 0) (x : K), f (t * t * x) = ρ (diagSL t ht) (f x)) →
      ∃ m₀ : V, (∀ (t : K) (ht : t ≠ 0), ρ (diagSL t ht) m₀ = m₀) ∧
        ∀ x, f x = ρ (unipotent x) m₀ * m₀⁻¹)
    {c : SpecialLinearGroup (Fin 2) K → V} (hc : IsCocycle ρ c) : IsCoboundary ρ c := by
  set T : Subgroup (SpecialLinearGroup (Fin 2) K) := (diagHom K).range with hT
  have hcT : IsCocycle (ρ.comp T.subtype) (fun t : T => c t) := fun g h => hc g h
  obtain ⟨m₁, hm₁⟩ := coboundary_of_odd_card hV (odd_card_torus (K := K)) hcT
  have hc₁ := hc.div_cobdry m₁
  set c₁ : SpecialLinearGroup (Fin 2) K → V := fun g => c g * (ρ g m₁ * m₁⁻¹)⁻¹ with hc₁def
  have hvanT : ∀ h ∈ T, c₁ h = 1 := by
    intro h hh
    have := hm₁ ⟨h, hh⟩
    simp only [hc₁def]
    rw [show c h = ρ h m₁ * m₁⁻¹ from this]
    simp
  have hconj : ∀ h ∈ T, ∀ g, c₁ (h * g * h⁻¹) = ρ h (c₁ g) := by
    intro h hh g
    have h1 : c₁ h = 1 := hvanT h hh
    have h2 : c₁ h⁻¹ = 1 := hvanT h⁻¹ (T.inv_mem hh)
    rw [mul_assoc, hc₁ h (g * h⁻¹), h1, one_mul, hc₁ g h⁻¹, h2, map_one, mul_one]
  have hmemT : ∀ (t : K) (ht : t ≠ 0), diagSL t ht ∈ T := fun t ht =>
    MonoidHom.mem_range.2 ⟨Units.mk0 t ht, rfl⟩
  obtain ⟨m₀, hm₀fix, hm₀⟩ := key (fun x => c₁ (unipotent x))
    (by simp only [unipotent_zero]; exact hc₁.map_one)
    (fun x y => by simp only [unipotent_add]; exact hc₁ _ _)
    (fun t ht x => by
      have h := diagSL_mul_unipotent t ht x
      have : unipotent (t * t * x) = diagSL t ht * unipotent x * (diagSL t ht)⁻¹ := by
        rw [h, mul_inv_cancel_right]
      rw [this]
      exact hconj _ (hmemT t ht) _)
  have hc₂ := hc₁.div_cobdry m₀
  set c₂ : SpecialLinearGroup (Fin 2) K → V := fun g => c₁ g * (ρ g m₀ * m₀⁻¹)⁻¹ with hc₂def
  have hvanB : ∀ b ∈ borel K, c₂ b = 1 := by
    intro b hb
    obtain ⟨⟨x, a⟩, hxa⟩ := borelEquiv.surjective ⟨b, hb⟩
    have hb' : b = unipotent x * diagHom K a := congrArg Subtype.val hxa.symm
    have hu : c₂ (unipotent x) = 1 := by
      simp only [hc₂def, hm₀ x]
      simp
    have hd : c₂ (diagHom K a) = 1 := by
      have h1 : c₁ (diagHom K a) = 1 := hvanT _ (MonoidHom.mem_range.2 ⟨a, rfl⟩)
      have h2 : ρ (diagHom K a) m₀ = m₀ := hm₀fix (a : K) a.ne_zero
      simp only [hc₂def, h1, h2]
      simp
    rw [hb', hc₂ _ _, hu, hd, map_one, mul_one]
  obtain ⟨m₂, hm₂⟩ := coboundary_of_vanish_on_odd_index hV (borel K) (odd_borel_index (K := K))
    hc₂ hvanB
  exact isCoboundary_of_div_cobdry m₁ (isCoboundary_of_div_cobdry m₀ ⟨m₂, hm₂⟩)

theorem hom_trivial_of_borel (hV : ∀ v : V, v ^ 2 = 1) (hK : ∃ a : K, a ≠ 0 ∧ a ≠ 1)
    (φ : SpecialLinearGroup (Fin 2) K →* V) : φ = 1 := by
  have hc : IsCocycle (1 : SpecialLinearGroup (Fin 2) K →* MulAut V) φ := fun g h => by
    simp
  obtain ⟨m, hm⟩ := coboundary_of_borel hV 1 (key := fun f h0 hadd htor => by
    refine ⟨1, fun t ht => rfl, fun x => ?_⟩
    have hsq : ∀ x : K, ∃ t : K, t * t = x := fun x => by
      obtain ⟨t, ht⟩ := FiniteField.isSquare_of_char_two (F := K) (ringChar.eq _ 2) x
      exact ⟨t, ht.symm⟩
    obtain ⟨a, ha0, ha1⟩ := hK
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h1a : 1 + a ≠ 0 := fun h => ha1 (by linear_combination h - h2)
    have hconst : ∀ y : K, y ≠ 0 → f y = f 1 := by
      intro y hy
      obtain ⟨t, rfl⟩ := hsq y
      have ht : t ≠ 0 := by
        rintro rfl
        exact hy (mul_zero 0)
      have := htor t ht 1
      rw [mul_one] at this
      simpa using this
    have hf1 : f 1 = 1 := by
      have e := hadd 1 a
      rw [hconst (1 + a) h1a, hconst a ha0] at e
      simp only [MonoidHom.one_apply, MulAut.one_apply] at e
      have : f 1 * f 1 = f 1 * 1 := by rw [mul_one]; exact e.symm
      exact mul_left_cancel this
    by_cases hx : x = 0
    · rw [hx, h0]; simp
    · rw [hconst x hx, hf1]; simp) hc
  ext g
  simpa using hm g

end Reduction

end CFSG.CGT.PushingUpLit.CGT6X
