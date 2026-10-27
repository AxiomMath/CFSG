module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk47abShape

public section

namespace CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab

open scoped MatrixGroups

section Abstract

variable {Y : Type*} [Group Y]

theorem e8_commute_sgnHom {a b : Y} (ha : a * a = 1) (hb : b * b = 1) (h : Commute a b) (m n : ℤˣ) :
    Commute (sgnHom a ha m) (sgnHom b hb n) := by
  rcases Int.units_eq_one_or m with rfl | rfl <;> rcases Int.units_eq_one_or n with rfl | rfl <;>
    simp [sgnHom_neg_one, sgnHom_one, h]

theorem e8_sgnHom_mem {a : Y} (ha : a * a = 1) {H : Subgroup Y} (haH : a ∈ H) (m : ℤˣ) :
    sgnHom a ha m ∈ H := by
  rcases Int.units_eq_one_or m with rfl | rfl
  · rw [sgnHom_one]; exact H.one_mem
  · rw [sgnHom_neg_one]; exact haH

theorem exists_elementary_eight_of_involutions {a b c : Y} {H : Subgroup Y}
    (ha : a * a = 1) (hb : b * b = 1) (hc : c * c = 1)
    (hab : Commute a b) (hac : Commute a c) (hbc : Commute b c)
    (haH : a ∈ H) (hbH : b ∈ H) (hcH : c ∈ H)
    (h1 : a ≠ 1) (h2 : b ≠ 1) (h3 : c ≠ 1) (h4 : a * b ≠ 1) (h5 : a * c ≠ 1) (h6 : b * c ≠ 1)
    (h7 : a * (b * c) ≠ 1) :
    ∃ E : Subgroup Y, E ≤ H ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
      Nat.card E = 8 := by
  have c12 : ∀ (m n : ℤˣ), Commute (sgnHom b hb m) (sgnHom c hc n) := e8_commute_sgnHom hb hc hbc
  let f₁₂ : ℤˣ × ℤˣ →* Y := (sgnHom b hb).noncommCoprod (sgnHom c hc) c12
  have c012 : ∀ (m : ℤˣ) (n : ℤˣ × ℤˣ), Commute (sgnHom a ha m) (f₁₂ n) := fun m n =>
    (e8_commute_sgnHom ha hb hab m n.1).mul_right (e8_commute_sgnHom ha hc hac m n.2)
  let φ : ℤˣ × (ℤˣ × ℤˣ) →* Y := (sgnHom a ha).noncommCoprod f₁₂ c012
  have hφ : ∀ m n₁ n₂, φ (m, (n₁, n₂)) = sgnHom a ha m * (sgnHom b hb n₁ * sgnHom c hc n₂) :=
    fun _ _ _ => rfl
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨m, n₁, n₂⟩ hx
    rw [MonoidHom.mem_ker, hφ] at hx
    rw [Subgroup.mem_bot]
    rcases Int.units_eq_one_or m with rfl | rfl <;> rcases Int.units_eq_one_or n₁ with rfl | rfl <;>
      rcases Int.units_eq_one_or n₂ with rfl | rfl <;>
      simp only [sgnHom_neg_one, sgnHom_one, one_mul, mul_one] at hx
    · rfl
    · exact absurd hx h3
    · exact absurd hx h2
    · exact absurd hx h6
    · exact absurd hx h1
    · exact absurd hx h5
    · exact absurd hx h4
    · exact absurd hx h7
  refine ⟨φ.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨⟨m, n₁, n₂⟩, rfl⟩
    rw [hφ]
    exact mul_mem (e8_sgnHom_mem ha haH m)
      (mul_mem (e8_sgnHom_mem hb hbH n₁) (e8_sgnHom_mem hc hcH n₂))
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm x y]
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Prod.ext (Int.units_sq _) (Prod.ext (Int.units_sq _) (Int.units_sq _))
    rw [this, map_one]
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    simp

end Abstract

section Quaternion

variable {F : Type} [Field F]

theorem e8_two_ne_zero [Finite F] (hF : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro h
  have := FiniteField.even_card_iff_char_two.1 h
  rw [← Nat.card_eq_fintype_card] at this
  exact (Nat.not_even_iff_odd.2 hF) (Nat.even_iff.2 this)

theorem e8_exists_sq_add_sq [Finite F] : ∃ a b : F, a ^ 2 + b ^ 2 = -1 := by
  have : NeZero (ringChar F) := ⟨CharP.char_ne_zero_of_finite F (ringChar F)⟩
  obtain ⟨a, b, hab⟩ := CharP.sq_add_sq F (ringChar F) (-1)
  exact ⟨a, b, by exact_mod_cast hab⟩

@[expose] def e8P (F : Type) [Field F] : SL(2, F) :=
  ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[expose] def e8Q {a b : F} (h : a ^ 2 + b ^ 2 = -1) : SL(2, F) :=
  ⟨!![a, b; b, -a], by simp [Matrix.det_fin_two]; linear_combination -h⟩

theorem e8P_mul_self : e8P F * e8P F = -1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [e8P, Matrix.mul_apply, Fin.sum_univ_two]

theorem e8Q_mul_self {a b : F} (h : a ^ 2 + b ^ 2 = -1) : e8Q h * e8Q h = -1 := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [e8Q, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h | linear_combination (-1 : F) * h | ring1

theorem e8P_mul_e8Q {a b : F} (h : a ^ 2 + b ^ 2 = -1) :
    e8P F * e8Q h = -1 * (e8Q h * e8P F) := by
  rw [neg_one_mul]
  ext i j
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
  fin_cases i <;> fin_cases j <;> simp [e8P, e8Q, Matrix.mul_apply, Fin.sum_univ_two]

theorem e8_zpow_neg_one (k : ℤ) : (-1 : SL(2, F)) ^ k = 1 ∨ (-1 : SL(2, F)) ^ k = -1 := by
  rcases Int.even_or_odd k with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem e8_quat [Finite F] (hF : Odd (Nat.card F)) :
    ∃ p q : SL(2, F), p * p = -1 ∧ q * q = -1 ∧ p * q = -1 * (q * p) ∧
      p ∉ Subgroup.zpowers (-1 : SL(2, F)) ∧ q ∉ Subgroup.zpowers (-1 : SL(2, F)) ∧
      p * q ∉ Subgroup.zpowers (-1 : SL(2, F)) := by
  have h2 := e8_two_ne_zero hF
  obtain ⟨a, b, hab⟩ := e8_exists_sq_add_sq (F := F)
  refine ⟨e8P F, e8Q hab, e8P_mul_self, e8Q_mul_self hab, e8P_mul_e8Q hab, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_zpowers_iff]
    rintro ⟨k, hk⟩
    have h01 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hk
    rcases e8_zpow_neg_one (F := F) k with h | h <;> rw [h] at h01 <;> simp [e8P] at h01
  · rw [Subgroup.mem_zpowers_iff]
    rintro ⟨k, hk⟩
    have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hk
    have h11 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 1) hk
    rcases e8_zpow_neg_one (F := F) k with h | h <;> rw [h] at h00 h11 <;> simp [e8Q] at h00 h11 <;>
      first
        | exact h2 (by linear_combination h00 + h11)
        | exact h2 (by linear_combination h11 - h00)
  · rw [Subgroup.mem_zpowers_iff]
    rintro ⟨k, hk⟩
    have h00 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hk
    have h11 := congrArg (fun A : SL(2, F) => (A : Matrix (Fin 2) (Fin 2) F) 1 1) hk
    rw [Matrix.SpecialLinearGroup.coe_mul] at h00 h11
    rcases e8_zpow_neg_one (F := F) k with h | h <;> rw [h] at h00 h11 <;>
      simp [e8P, e8Q, Matrix.mul_apply, Fin.sum_univ_two] at h00 h11 <;>
      first
        | exact h2 (by linear_combination h00 + h11)
        | exact h2 (by linear_combination h11 - h00)

end Quaternion

namespace Shape

variable {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂] (S : Shape Y F₁ F₂)

@[expose] def e8Psi : SL(2, F₁) × SL(2, F₂) →* Y :=
  (S.I₁.subtype.comp S.e₁.symm.toMonoidHom).noncommCoprod
    (S.I₂.subtype.comp S.e₂.symm.toMonoidHom)
    (fun s t => S.comm _ (S.e₁.symm s).2 _ (S.e₂.symm t).2)

theorem e8Psi_apply (s : SL(2, F₁)) (t : SL(2, F₂)) :
    S.e8Psi (s, t) = ((S.e₁.symm s : S.I₁) : Y) * ((S.e₂.symm t : S.I₂) : Y) := rfl

theorem e8_symm_neg_one₁ : ((S.e₁.symm (-1) : S.I₁) : Y) = S.z := by
  rw [(S.e₁.symm_apply_eq).2 S.e₁_z.symm]

theorem e8_symm_neg_one₂ : ((S.e₂.symm (-1) : S.I₂) : Y) = S.z := by
  rw [(S.e₂.symm_apply_eq).2 S.e₂_z.symm]

theorem e8Psi_neg_one_one : S.e8Psi (-1, 1) = S.z := by
  rw [e8Psi_apply, map_one, e8_symm_neg_one₁, Subgroup.coe_one, mul_one]

theorem e8Psi_neg_one_neg_one : S.e8Psi (-1, -1) = 1 := by
  rw [e8Psi_apply, e8_symm_neg_one₁, e8_symm_neg_one₂]
  exact S.z_sq

theorem e8Psi_mem (x : SL(2, F₁) × SL(2, F₂)) : S.e8Psi x ∈ S.I₁ ⊔ S.I₂ := by
  obtain ⟨s, t⟩ := x
  rw [e8Psi_apply]
  exact mul_mem (Subgroup.mem_sup_left (S.e₁.symm s).2) (Subgroup.mem_sup_right (S.e₂.symm t).2)

theorem e8Psi_commute_z (x : SL(2, F₁) × SL(2, F₂)) : Commute S.z (S.e8Psi x) := by
  obtain ⟨s, t⟩ := x
  rw [e8Psi_apply]
  exact (show Commute S.z ((S.e₁.symm s : S.I₁) : Y) from
    (S.comm _ (S.e₁.symm s).2 S.z S.z_mem₂).symm).mul_right
    (S.comm S.z S.z_mem₁ _ (S.e₂.symm t).2)

theorem e8Psi_eq_one {x : SL(2, F₁) × SL(2, F₂)} (hx : S.e8Psi x = 1) :
    x.1 ∈ Subgroup.zpowers (-1 : SL(2, F₁)) := by
  obtain ⟨s, t⟩ := x
  rw [e8Psi_apply] at hx
  have hab : ((S.e₁.symm s : S.I₁) : Y) = ((S.e₂.symm t : S.I₂) : Y)⁻¹ :=
    eq_inv_of_mul_eq_one_left hx
  have hmem : ((S.e₁.symm s : S.I₁) : Y) ∈ S.I₁ ⊓ S.I₂ :=
    ⟨(S.e₁.symm s).2, hab ▸ S.I₂.inv_mem (S.e₂.symm t).2⟩
  rw [S.inter, Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  have hk' : S.e₁.symm s = (⟨S.z, S.z_mem₁⟩ : S.I₁) ^ k :=
    Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
  have hs : s = (-1 : SL(2, F₁)) ^ k := by
    rw [← S.e₁_z, ← map_zpow, ← hk', MulEquiv.apply_symm_apply]
  show s ∈ _
  rw [hs]
  exact Subgroup.zpow_mem_zpowers _ _

end Shape

theorem Shape.exists_elementary_eight {Y : Type} [Group Y] {F₁ F₂ : Type} [Field F₁] [Field F₂]
    [Finite F₁] [Finite F₂] (S : Shape Y F₁ F₂) (h₁ : Odd (Nat.card F₁)) (h₂ : Odd (Nat.card F₂)) :
    ∃ E : Subgroup Y, E ≤ S.I₁ ⊔ S.I₂ ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ 2 = 1) ∧
      Nat.card E = 8 := by
  obtain ⟨p₁, q₁, hpp₁, hqq₁, hpq₁, hp₁, hq₁, hpq₁'⟩ := e8_quat h₁
  obtain ⟨p₂, q₂, hpp₂, hqq₂, hpq₂, -, -, -⟩ := e8_quat h₂
  have hnn : S.e8Psi (-1, -1) = 1 := S.e8Psi_neg_one_neg_one
  have hz1 : S.e8Psi (-1, 1) = S.z := S.e8Psi_neg_one_one
  have hC : ∀ x, S.e8Psi x = 1 → x.1 ∈ Subgroup.zpowers (-1 : SL(2, F₁)) :=
    fun x hx => S.e8Psi_eq_one hx
  have hm1 : (-1 : SL(2, F₁)) ∈ Subgroup.zpowers (-1 : SL(2, F₁)) := Subgroup.mem_zpowers _
  have hC' : ∀ u : SL(2, F₁) × SL(2, F₂), S.z * S.e8Psi u = 1 →
      u.1 ∈ Subgroup.zpowers (-1 : SL(2, F₁)) := by
    intro u h
    have h' : S.e8Psi ((-1, 1) * u) = 1 := by rw [map_mul, hz1]; exact h
    have h'' : (-1 : SL(2, F₁)) * u.1 ∈ Subgroup.zpowers (-1 : SL(2, F₁)) := hC _ h'
    exact (Subgroup.mul_mem_cancel_left _ hm1).1 h''
  have hX : S.e8Psi (p₁, p₂) * S.e8Psi (p₁, p₂) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, hpp₁, hpp₂, hnn]
  have hX' : S.e8Psi (q₁, q₂) * S.e8Psi (q₁, q₂) = 1 := by
    rw [← map_mul, Prod.mk_mul_mk, hqq₁, hqq₂, hnn]
  have hXX' : S.e8Psi (p₁, p₂) * S.e8Psi (q₁, q₂) = S.e8Psi (q₁, q₂) * S.e8Psi (p₁, p₂) := by
    have e : (p₁, p₂) * (q₁, q₂) = (-1, -1) * ((q₁, q₂) * (p₁, p₂)) := Prod.ext hpq₁ hpq₂
    calc S.e8Psi (p₁, p₂) * S.e8Psi (q₁, q₂) = S.e8Psi ((p₁, p₂) * (q₁, q₂)) := (map_mul _ _ _).symm
      _ = S.e8Psi ((-1, -1) * ((q₁, q₂) * (p₁, p₂))) := by rw [e]
      _ = S.e8Psi (q₁, q₂) * S.e8Psi (p₁, p₂) := by rw [map_mul, map_mul, hnn, one_mul]
  refine exists_elementary_eight_of_involutions (a := S.z) (b := S.e8Psi (p₁, p₂))
    (c := S.e8Psi (q₁, q₂)) S.z_sq hX hX' (S.e8Psi_commute_z _) (S.e8Psi_commute_z _) hXX'
    (Subgroup.mem_sup_left S.z_mem₁) (S.e8Psi_mem _) (S.e8Psi_mem _) S.z_ne ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun h => hp₁ (hC _ h)
  · exact fun h => hq₁ (hC _ h)
  · exact fun h => hp₁ (hC' _ h)
  · exact fun h => hq₁ (hC' _ h)
  · exact fun h => hpq₁' (hC ((p₁, p₂) * (q₁, q₂)) (by rw [map_mul]; exact h))
  · exact fun h => hpq₁' (hC' ((p₁, p₂) * (q₁, q₂)) (by rw [map_mul]; exact h))

end CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
