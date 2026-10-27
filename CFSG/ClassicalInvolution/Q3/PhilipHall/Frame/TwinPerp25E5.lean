module

public import CFSG.ClassicalInvolution.Q3.Q3T7P25YMH02

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL.Q8

open Matrix
open scoped MatrixGroups
open CFSG.ClassicalInvolution.Q3.Q3T6 CFSG.ClassicalInvolution.Q3.Q3T7P25

section ZMod3

@[expose] def genJ : SL(2, ZMod 3) := ⟨!![1, 1; 1, -1], by decide⟩

theorem q8_closed : ∀ a b : SL(2, ZMod 3), a ^ 4 = 1 → b ^ 4 = 1 → (a * b) ^ 4 = 1 := by
  decide +kernel

theorem pow8_imp_pow4 : ∀ b : SL(2, ZMod 3), b ^ 8 = 1 → b ^ 4 = 1 := by
  decide +kernel

theorem card_q8 : Fintype.card {b : SL(2, ZMod 3) // b ^ 4 = 1} = 8 := by
  decide +kernel

theorem q8_gen : ∀ b : SL(2, ZMod 3), b ^ 4 = 1 →
    ∃ x < 4, ∃ y < 2, b = autGenS ^ x * genJ ^ y := by
  decide +kernel

theorem q8_cent_aux : ∀ A : Matrix (Fin 2) (Fin 2) (ZMod 3),
    A * (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) = (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A →
    A * (genJ : Matrix (Fin 2) (Fin 2) (ZMod 3)) = (genJ : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A →
    ∃ c : ZMod 3, A = c • (1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by
  decide +kernel

theorem q8_aut_aux : ∀ h₁ h₂ : SL(2, ZMod 3),
    (h₁ ^ 4 = 1 ∧ h₂ ^ 4 = 1 ∧ h₁ ^ 2 ≠ 1 ∧ h₂ ^ 2 = h₁ ^ 2 ∧ h₂ * h₁ = h₁ ^ 3 * h₂) →
      ∃ (g : Matrix (Fin 2) (Fin 2) (ZMod 3)) (u : ZMod 3), g.det * u = 1 ∧
        g * (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
          (h₁ : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g ∧
        g * (genJ : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
          (h₂ : Matrix (Fin 2) (Fin 2) (ZMod 3)) * g := by
  decide +kernel

theorem genJ_pow_four : genJ ^ 4 = 1 := by decide +kernel
theorem genJ_sq : genJ ^ 2 = autGenS ^ 2 := by decide +kernel
theorem genJ_rel : genJ * autGenS = autGenS ^ 3 * genJ := by decide +kernel

end ZMod3

@[expose] def QZ : Subgroup SL(2, ZMod 3) where
  carrier := {b | b ^ 4 = 1}
  mul_mem' := fun {a b} ha hb => q8_closed a b ha hb
  one_mem' := one_pow 4
  inv_mem' := fun {a} ha => by
    have ha' : a ^ 4 = 1 := ha
    show a⁻¹ ^ 4 = 1
    rw [inv_pow, ha', inv_one]

section Transport

variable {F : Type} [Field F]

@[expose] noncomputable def Qsub (r : ZMod 3 ≃+* F) : Subgroup SL(2, F) :=
  QZ.map (slMapEquivF r).toMonoidHom

theorem mem_Qsub (r : ZMod 3 ≃+* F) (b : SL(2, F)) : b ∈ Qsub r ↔ b ^ 4 = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ^ 4 = 1 := hx
    show (slMapEquivF r x) ^ 4 = 1
    rw [← map_pow, hx', map_one]
  · intro hb
    refine ⟨(slMapEquivF r).symm b, ?_, by simp⟩
    show ((slMapEquivF r).symm b) ^ 4 = 1
    rw [← map_pow, hb, map_one]

theorem nonempty_ringEquiv (hF : Nat.card F = 3) : Nonempty (ZMod 3 ≃+* F) := by
  have : Finite F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have : Fintype F := Fintype.ofFinite F
  exact ⟨FiniteField.ringEquivOfCardEq (by rw [ZMod.card, ← Nat.card_eq_fintype_card, hF])⟩

theorem Qsub_one_pow (r : ZMod 3 ≃+* F) {b : SL(2, F)} (hb : b ∈ Qsub r) : b ^ 4 = 1 :=
  (mem_Qsub r b).mp hb

theorem natCard_Qsub (r : ZMod 3 ≃+* F) : Nat.card (Qsub r) = 8 := by
  have h1 : Nat.card (Qsub r) = Nat.card QZ :=
    (Subgroup.card_map_of_injective (slMapEquivF r).injective).symm ▸ rfl
  rw [h1]
  have : Nat.card QZ = Nat.card {b : SL(2, ZMod 3) // b ^ 4 = 1} := rfl
  rw [this, Nat.card_eq_fintype_card, card_q8]

theorem pow4_of_pow_two_pow_Z {b : SL(2, ZMod 3)} {n : ℕ} (h : b ^ (2 ^ n) = 1) : b ^ 4 = 1 := by
  have hd1 : orderOf b ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one h
  have hd2 : orderOf b ∣ 24 := by
    rw [← Aut.sl2Three_natCard]
    exact orderOf_dvd_natCard b
  obtain ⟨k, hk, hko⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd1
  have hk3 : k ≤ 3 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 4 ∣ 24 := by
      rw [hko] at hd2
      exact (pow_dvd_pow 2 hcon).trans hd2
    norm_num at this
  have h8 : b ^ 8 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hko]
    calc 2 ^ k ∣ 2 ^ 3 := pow_dvd_pow 2 hk3
      _ = 8 := by norm_num
  exact pow8_imp_pow4 b h8

theorem pow4_of_pow_two_pow (r : ZMod 3 ≃+* F) {b : SL(2, F)} {n : ℕ} (h : b ^ (2 ^ n) = 1) :
    b ^ 4 = 1 := by
  have h1 : ((slMapEquivF r).symm b) ^ (2 ^ n) = 1 := by
    rw [← map_pow, h, map_one]
  have h2 := pow4_of_pow_two_pow_Z h1
  have : (slMapEquivF r) (((slMapEquivF r).symm b) ^ 4) = 1 := by rw [h2, map_one]
  rwa [map_pow, MulEquiv.apply_symm_apply] at this

theorem eq_map_Qsub_of_card [Finite F] (r : ZMod 3 ≃+* F) {Y : Type} [Group Y] (ι : SL(2, F) →* Y)
    (hι : Function.Injective ι) (H : Subgroup Y) (hH : H ≤ ι.range) (hcard : Nat.card H = 8) :
    H = (Qsub r).map ι := by
  set H' := H.comap ι with hH'
  have hmap : H'.map ι = H := by
    rw [hH', Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hH
  have hc' : Nat.card H' = 8 := by
    rw [← hcard, ← hmap]
    exact (Subgroup.card_map_of_injective hι).symm
  have hle : H' ≤ Qsub r := by
    intro b hb
    apply (mem_Qsub r b).mpr
    have h1 : (⟨b, hb⟩ : H') ^ 8 = 1 := by
      rw [← hc']
      exact pow_card_eq_one'
    have h8 : b ^ 8 = 1 := by simpa using congrArg Subtype.val h1
    exact pow4_of_pow_two_pow r (n := 3) (by simpa using h8)
  have heq : H' = Qsub r :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [natCard_Qsub r, hc'])
  rw [← hmap, heq]

theorem coe_slMapEquivF (r : ZMod 3 ≃+* F) (y : SL(2, ZMod 3)) :
    ((slMapEquivF r y : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (y : Matrix (Fin 2) (Fin 2) (ZMod 3)).map r := by
  simp [slMapEquivF, Matrix.SpecialLinearGroup.map_apply_coe]

theorem scalar_of_comm (r : ZMod 3 ≃+* F) {A : Matrix (Fin 2) (Fin 2) F}
    (h : ∀ b : SL(2, F), b ^ 4 = 1 →
      A * (b : Matrix (Fin 2) (Fin 2) F) = (b : Matrix (Fin 2) (Fin 2) F) * A) :
    ∃ c : F, A = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
  have hS := h (slMapEquivF r autGenS) (by rw [← map_pow, autGenS_pow_four, map_one])
  have hJ := h (slMapEquivF r genJ) (by rw [← map_pow, genJ_pow_four, map_one])
  rw [coe_slMapEquivF] at hS hJ
  set A₀ : Matrix (Fin 2) (Fin 2) (ZMod 3) := A.map r.symm with hA₀
  have hA : A = A₀.map r := by
    ext i j
    simp [A₀]
  have hinj : Function.Injective (fun M : Matrix (Fin 2) (Fin 2) (ZMod 3) => M.map r) := fun M N hMN => by
    ext i j
    exact r.injective (congrFun (congrFun hMN i) j)
  have hS0 : A₀ * (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (autGenS : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A₀ := by
    apply hinj
    simp only [Matrix.map_mul]
    rw [← hA]
    exact hS
  have hJ0 : A₀ * (genJ : Matrix (Fin 2) (Fin 2) (ZMod 3)) =
      (genJ : Matrix (Fin 2) (Fin 2) (ZMod 3)) * A₀ := by
    apply hinj
    simp only [Matrix.map_mul]
    rw [← hA]
    exact hJ
  obtain ⟨c, hc⟩ := q8_cent_aux A₀ hS0 hJ0
  refine ⟨r c, ?_⟩
  rw [hA, hc]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.smul_apply, hij]

theorem exists_conj_of_aut (r : ZMod 3 ≃+* F) (θ : Qsub r ≃* Qsub r) :
    ∃ d : GL (Fin 2) F, ∀ b : Qsub r,
      Matrix.SpecialLinearGroup.toGL ((θ b : Qsub r) : SL(2, F)) =
        d * Matrix.SpecialLinearGroup.toGL (b : SL(2, F)) * d⁻¹ := by
  set Φ := slMapEquivF r with hΦ
  have hiQ : Φ autGenS ∈ Qsub r :=
    (mem_Qsub r _).mpr (by rw [← map_pow, autGenS_pow_four, map_one])
  have hjQ : Φ genJ ∈ Qsub r := (mem_Qsub r _).mpr (by rw [← map_pow, genJ_pow_four, map_one])
  set i₀ : Qsub r := ⟨Φ autGenS, hiQ⟩ with hi₀
  set j₀ : Qsub r := ⟨Φ genJ, hjQ⟩ with hj₀
  have hq1 : j₀ ^ 2 = i₀ ^ 2 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, hi₀, hj₀]
    rw [← map_pow, ← map_pow, genJ_sq]
  have hq2 : j₀ * i₀ = i₀ ^ 3 * j₀ := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, hi₀, hj₀]
    rw [← map_pow, ← map_mul, ← map_mul, genJ_rel]
  have hq3 : i₀ ^ 2 ≠ 1 := by
    intro h
    have h' : (Φ autGenS) ^ 2 = 1 := by
      have := congrArg Subtype.val h
      simpa [hi₀] using this
    rw [← map_pow] at h'
    exact autGenS_sq_ne_one (Φ.injective (by rw [h', map_one]))
  set h₁ : SL(2, F) := ((θ i₀ : Qsub r) : SL(2, F)) with hh₁
  set h₂ : SL(2, F) := ((θ j₀ : Qsub r) : SL(2, F)) with hh₂
  have hh₁4 : h₁ ^ 4 = 1 := (mem_Qsub r _).mp (θ i₀).2
  have hh₂4 : h₂ ^ 4 = 1 := (mem_Qsub r _).mp (θ j₀).2
  have hh₁2 : h₁ ^ 2 ≠ 1 := by
    intro h
    apply hq3
    apply θ.injective
    apply Subtype.ext
    rw [map_pow, map_one]
    simpa [hh₁] using h
  have hh₂2 : h₂ ^ 2 = h₁ ^ 2 := by
    have := congrArg (fun x : Qsub r => ((θ x : Qsub r) : SL(2, F))) hq1
    simpa [hh₁, hh₂] using this
  have hh₂₁ : h₂ * h₁ = h₁ ^ 3 * h₂ := by
    have := congrArg (fun x : Qsub r => ((θ x : Qsub r) : SL(2, F))) hq2
    simpa [hh₁, hh₂] using this
  set h₁Z := Φ.symm h₁ with hh₁Z
  set h₂Z := Φ.symm h₂ with hh₂Z
  obtain ⟨g, u, hdet, hgS, hgJ⟩ := q8_aut_aux h₁Z h₂Z
    ⟨by rw [hh₁Z, ← map_pow, hh₁4, map_one], by rw [hh₂Z, ← map_pow, hh₂4, map_one],
      by
        intro h
        apply hh₁2
        have := congrArg Φ h
        rwa [hh₁Z, map_pow, MulEquiv.apply_symm_apply, map_one] at this,
      by rw [hh₁Z, hh₂Z, ← map_pow, ← map_pow, hh₂2],
      by
        rw [hh₁Z, hh₂Z, ← map_pow, ← map_mul, ← map_mul, hh₂₁]⟩
  let G : GL (Fin 2) (ZMod 3) := Matrix.GeneralLinearGroup.mk'' g (IsUnit.of_mul_eq_one u hdet)
  set D : GL (Fin 2) F := Matrix.GeneralLinearGroup.map (r : ZMod 3 →+* F) G with hD
  have hDc : (D : Matrix (Fin 2) (Fin 2) F) = g.map r := rfl
  have hh₁c : (h₁ : Matrix (Fin 2) (Fin 2) F) = (h₁Z : Matrix (Fin 2) (Fin 2) (ZMod 3)).map r := by
    rw [← coe_slMapEquivF, hh₁Z, MulEquiv.apply_symm_apply]
  have hh₂c : (h₂ : Matrix (Fin 2) (Fin 2) F) = (h₂Z : Matrix (Fin 2) (Fin 2) (ZMod 3)).map r := by
    rw [← coe_slMapEquivF, hh₂Z, MulEquiv.apply_symm_apply]
  have hDi : (D : Matrix (Fin 2) (Fin 2) F) * ((Φ autGenS : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (h₁ : Matrix (Fin 2) (Fin 2) F) * D := by
    rw [hDc, hΦ, coe_slMapEquivF, hh₁c, ← Matrix.map_mul, ← Matrix.map_mul, hgS]
  have hDj : (D : Matrix (Fin 2) (Fin 2) F) * ((Φ genJ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
      (h₂ : Matrix (Fin 2) (Fin 2) F) * D := by
    rw [hDc, hΦ, coe_slMapEquivF, hh₂c, ← Matrix.map_mul, ← Matrix.map_mul, hgJ]
  have hconj : ∀ (h x : SL(2, F)), (D : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) =
      (h : Matrix (Fin 2) (Fin 2) F) * D →
      Matrix.SpecialLinearGroup.toGL h = D * Matrix.SpecialLinearGroup.toGL x * D⁻¹ := by
    intro h x hx
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (h : Matrix (Fin 2) (Fin 2) F) = (D : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) *
      ((D⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    rw [hx, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  have hθi := hconj h₁ (Φ autGenS) hDi
  have hθj := hconj h₂ (Φ genJ) hDj
  let Θ : Qsub r →* GL (Fin 2) F :=
    Matrix.SpecialLinearGroup.toGL.comp ((Qsub r).subtype.comp θ.toMonoidHom)
  let Ξ : Qsub r →* GL (Fin 2) F :=
    (MulAut.conj D).toMonoidHom.comp (Matrix.SpecialLinearGroup.toGL.comp (Qsub r).subtype)
  have hΘi : Θ i₀ = Ξ i₀ := hθi
  have hΘj : Θ j₀ = Ξ j₀ := hθj
  refine ⟨D, fun b => ?_⟩
  obtain ⟨x, hx, y, hy, hb⟩ := q8_gen (Φ.symm (b : SL(2, F))) (by
    rw [← map_pow, (mem_Qsub r _).mp b.2, map_one])
  have hbe : b = i₀ ^ x * j₀ ^ y := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_mul, hi₀, hj₀]
    rw [← map_pow, ← map_pow, ← map_mul, ← hb, MulEquiv.apply_symm_apply]
  have : Θ b = Ξ b := by
    rw [hbe, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow, hΘi, hΘj]
  exact this

end Transport

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R.EndL.Q8
