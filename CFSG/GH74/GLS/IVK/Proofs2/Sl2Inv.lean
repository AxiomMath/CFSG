module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

namespace Sl2Inv

open Matrix

variable {F : Type*} [Field F]

@[expose] def upper (a : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp] lemma coe_upper (a : F) : (upper a : Matrix (Fin 2) (Fin 2) F) = !![1, a; 0, 1] := rfl

lemma upper_mul (a b : F) : upper a * upper b = upper (a + b) := by
  refine Subtype.ext ?_
  show (!![1, a; 0, 1] * !![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) F) = !![1, a + b; 0, 1]
  rw [Matrix.mul_fin_two]
  simp [add_comm]

lemma upper_zero : upper (0 : F) = 1 := by
  refine Subtype.ext ?_
  show (!![1, 0; 0, 1] : Matrix (Fin 2) (Fin 2) F) = 1
  exact (Matrix.one_fin_two).symm

lemma upper_inv (a : F) : (upper a)⁻¹ = upper (-a) :=
  inv_eq_of_mul_eq_one_right (by rw [upper_mul, add_neg_cancel, upper_zero])

lemma upper_injective : Function.Injective (upper : F → SpecialLinearGroup (Fin 2) F) := by
  intro a b h
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa using this

@[expose] def upperHom : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun a := upper (Multiplicative.toAdd a)
  map_one' := upper_zero
  map_mul' _ _ := (upper_mul _ _).symm

lemma upperHom_injective : Function.Injective (upperHom (F := F)) :=
  fun _ _ h => Multiplicative.toAdd.injective (upper_injective h)

@[expose] def unitriangular : Subgroup (SpecialLinearGroup (Fin 2) F) := (upperHom (F := F)).range

lemma card_unitriangular : Nat.card (unitriangular (F := F)) = Nat.card F := by
  rw [unitriangular,
    Nat.card_congr (MonoidHom.ofInjective (upperHom_injective (F := F))).toEquiv.symm]
  exact Nat.card_congr Multiplicative.toAdd

lemma card_SL2 [Finite F] :
    Nat.card (SpecialLinearGroup (Fin 2) F) = Nat.card F * (Nat.card F ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite F
  rw [Matrix.card_SL_field, ← Nat.card_eq_fintype_card, Fin.prod_univ_two]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  generalize Nat.card F = q at hq ⊢
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one]
  apply Nat.div_eq_of_eq_mul_left (by omega)
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : q ≤ q ^ 2 := by nlinarith
  zify [h1, h2, (by omega : 1 ≤ q)]
  ring

lemma factorization_card_SL2 [Finite F] {p n : ℕ} (hp : p.Prime) (hq : Nat.card F = p ^ n) :
    (Nat.card (SpecialLinearGroup (Fin 2) F)).factorization p = n := by
  have hn : n ≠ 0 := by
    rintro rfl
    have : 1 < Nat.card F := Finite.one_lt_card
    simp [hq] at this
  have hpq : p ∣ Nat.card F := by rw [hq]; exact dvd_pow_self p hn
  have hq0 : Nat.card F ≠ 0 := Nat.card_pos.ne'
  have hnd : ¬ p ∣ Nat.card F ^ 2 - 1 := by
    intro h
    have h2 : p ∣ Nat.card F ^ 2 := dvd_pow hpq two_ne_zero
    have h1 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    have := Nat.dvd_sub h2 h
    rw [Nat.sub_sub_self h1] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hne : Nat.card F ^ 2 - 1 ≠ 0 := by
    have : 1 < Nat.card F := Finite.one_lt_card
    have : 1 < Nat.card F ^ 2 := Nat.one_lt_pow two_ne_zero this
    omega
  rw [card_SL2, Nat.factorization_mul hq0 hne, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hnd, add_zero, hq, hp.factorization_pow,
    Finsupp.single_eq_same]

theorem exists_conj_unitriangular [Finite F] {p n : ℕ} (hp : p.Prime) (hq : Nat.card F = p ^ n)
    (H : Subgroup (SpecialLinearGroup (Fin 2) F)) (hH : Nat.card H = p ^ n) :
    ∃ g : SpecialLinearGroup (Fin 2) F, ∀ x ∈ H, g⁻¹ * x * g ∈ unitriangular (F := F) := by
  have := Fact.mk hp
  have hfac := factorization_card_SL2 (F := F) hp hq
  let SH : Sylow p (SpecialLinearGroup (Fin 2) F) := Sylow.ofCard H (by rw [hH, hfac])
  let SU : Sylow p (SpecialLinearGroup (Fin 2) F) :=
    Sylow.ofCard (unitriangular (F := F)) (by rw [card_unitriangular, hq, hfac])
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin 2) F) SU SH
  refine ⟨g, fun x hx => ?_⟩
  have hx' : x ∈ ((g • SU : Sylow p (SpecialLinearGroup (Fin 2) F)) : Subgroup _) := by
    rw [hg]; simpa [SH, Sylow.coe_ofCard] using hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hx'
  simpa [SU, Sylow.coe_ofCard] using hx'

@[expose] def dneg (s : F) (hs : s * s = -1) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![s, 0; 0, -s], by simp [Matrix.det_fin_two_of, hs]⟩

lemma dneg_mul_upper (s : F) (hs : s * s = -1) (a : F) :
    dneg s hs * upper a = upper (-a) * dneg s hs := by
  refine Subtype.ext ?_
  show (!![s, 0; 0, -s] * !![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) F) =
    !![1, -a; 0, 1] * !![s, 0; 0, -s]
  rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp [mul_comm]

lemma dneg_inverts (s : F) (hs : s * s = -1) :
    ∀ u ∈ unitriangular (F := F), dneg s hs * u * (dneg s hs)⁻¹ = u⁻¹ := by
  rintro _ ⟨a, rfl⟩
  change dneg s hs * upper (Multiplicative.toAdd a) * (dneg s hs)⁻¹ =
    (upper (Multiplicative.toAdd a))⁻¹
  rw [dneg_mul_upper, upper_inv, mul_assoc, mul_inv_cancel, mul_one]

lemma inverted_of_conj {G : Type*} [Group G] {H U : Subgroup G} (d₀ g : G)
    (hU : ∀ u ∈ U, d₀ * u * d₀⁻¹ = u⁻¹) (hH : ∀ x ∈ H, g⁻¹ * x * g ∈ U) :
    ∀ x ∈ H, (g * d₀ * g⁻¹) * x * (g * d₀ * g⁻¹)⁻¹ = x⁻¹ := by
  intro x hx
  have h := hU _ (hH x hx)
  calc g * d₀ * g⁻¹ * x * (g * d₀ * g⁻¹)⁻¹ = g * (d₀ * (g⁻¹ * x * g) * d₀⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * x * g)⁻¹ * g⁻¹ := by rw [h]
    _ = x⁻¹ := by group

end Sl2Inv

theorem sl2_sylow_inverted {F : Type} [Field F] [Finite F] {p n : ℕ} (hp : p.Prime)
    (hq : Nat.card F = p ^ n) (h4 : Nat.card F % 4 = 1) {K : Type*} [Group K]
    (φ : K ≃* Matrix.SpecialLinearGroup (Fin 2) F) (P : Subgroup K) (hP : Nat.card P = p ^ n) :
    ∃ d : K, ∀ x ∈ P, d * x * d⁻¹ = x⁻¹ := by
  obtain ⟨s, hs⟩ : ∃ s : F, s * s = -1 := by
    have := Fintype.ofFinite F
    obtain ⟨s, hs⟩ := FiniteField.isSquare_neg_one_iff.mpr
      (by rw [← Nat.card_eq_fintype_card]; omega : Fintype.card F % 4 ≠ 3)
    exact ⟨s, hs.symm⟩
  let H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F) := P.map φ.toMonoidHom
  have hH : Nat.card H = p ^ n := by
    rw [← hP]
    exact Nat.card_congr (P.equivMapOfInjective φ.toMonoidHom φ.injective).symm.toEquiv
  obtain ⟨g, hg⟩ := Sl2Inv.exists_conj_unitriangular hp hq H hH
  have hinv := Sl2Inv.inverted_of_conj (Sl2Inv.dneg s hs) g (Sl2Inv.dneg_inverts s hs) hg
  refine ⟨φ.symm (g * Sl2Inv.dneg s hs * g⁻¹), fun x hx => ?_⟩
  apply φ.injective
  rw [map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply]
  exact hinv (φ x) ⟨x, hx, rfl⟩

end CFSG.GH74.GLS.IVK.Proofs2
