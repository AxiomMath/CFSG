module

import CFSG.LieType.HighestRoot.SL2Outer
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ClassicalInvolution.NDB.WC

open scoped MatrixGroups commutatorElement

section Matrix

variable {F : Type*} [Field F]

theorem mat_commute_of_sq {τ y y' : Matrix (Fin 2) (Fin 2) F} (h2 : (2 : F) ≠ 0)
    (hdet : τ.det = 1) (hτ : τ * τ = -1) (hy : y * τ = τ * y) (hy' : y' * τ = τ * y') :
    y * y' = y' * y := by
  rw [Matrix.det_fin_two] at hdet
  have q : ∀ i j, (τ * τ) i j = (-1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by rw [hτ]
  have r : ∀ i j, (y * τ) i j = (τ * y) i j := fun i j => by rw [hy]
  have r' : ∀ i j, (y' * τ) i j = (τ * y') i j := fun i j => by rw [hy']
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at q r r'
  have t00 : τ 0 0 * τ 0 0 + τ 0 1 * τ 1 0 = -1 := q 0 0
  have t11 : τ 1 0 * τ 0 1 + τ 1 1 * τ 1 1 = -1 := q 1 1
  have hs : (τ 0 0 + τ 1 1) * (τ 0 0 + τ 1 1) = 0 := by linear_combination t00 + t11 + 2 * hdet
  have hd : τ 1 1 = -τ 0 0 := by linear_combination mul_self_eq_zero.mp hs
  have p1 : y 0 1 * τ 1 0 = τ 0 1 * y 1 0 := by linear_combination r 0 0
  have p2 : τ 0 1 * (y 0 0 - y 1 1) = 2 * τ 0 0 * y 0 1 := by linear_combination r 0 1 - y 0 1 * hd
  have p3 : τ 1 0 * (y 0 0 - y 1 1) = 2 * τ 0 0 * y 1 0 := by
    linear_combination -(r 1 0) - y 1 0 * hd
  have p1' : y' 0 1 * τ 1 0 = τ 0 1 * y' 1 0 := by linear_combination r' 0 0
  have p2' : τ 0 1 * (y' 0 0 - y' 1 1) = 2 * τ 0 0 * y' 0 1 := by
    linear_combination r' 0 1 - y' 0 1 * hd
  have p3' : τ 1 0 * (y' 0 0 - y' 1 1) = 2 * τ 0 0 * y' 1 0 := by
    linear_combination -(r' 1 0) - y' 1 0 * hd
  have h4 : (4 : F) ≠ 0 := by
    have : (4 : F) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  set E := y 0 1 * y' 1 0 - y' 0 1 * y 1 0 with hE
  set F₁ := y' 0 1 * (y 0 0 - y 1 1) - y 0 1 * (y' 0 0 - y' 1 1) with hF₁
  set F₂ := y 1 0 * (y' 0 0 - y' 1 1) - y' 1 0 * (y 0 0 - y 1 1) with hF₂
  have haE : τ 0 0 * E = 0 := by
    have : 4 * (τ 0 0 * E) = 0 := by
      linear_combination y' 0 1 * p3 - y 0 1 * p3' - (y 0 0 - y 1 1) * p1' +
        (y' 0 0 - y' 1 1) * p1 - y' 1 0 * p2 + y 1 0 * p2'
    exact (mul_eq_zero.mp this).resolve_left h4
  have hcE : τ 1 0 * E = 0 := by linear_combination y' 1 0 * p1 - y 1 0 * p1'
  have hE0 : E = 0 := by linear_combination (-τ 0 0) * haE + (-τ 0 1) * hcE + E * t00
  have haF₁ : τ 0 0 * F₁ = 0 := by
    have : 2 * (τ 0 0 * F₁) = 0 := by
      linear_combination (y' 0 0 - y' 1 1) * p2 - (y 0 0 - y 1 1) * p2'
    exact (mul_eq_zero.mp this).resolve_left h2
  have hcF₁ : τ 1 0 * F₁ = 0 := by
    linear_combination y' 0 1 * p3 - y 0 1 * p3' - 2 * haE
  have hF₁0 : F₁ = 0 := by linear_combination (-τ 0 0) * haF₁ + (-τ 0 1) * hcF₁ + F₁ * t00
  have haF₂ : τ 0 0 * F₂ = 0 := by
    have : 2 * (τ 0 0 * F₂) = 0 := by
      linear_combination (y 0 0 - y 1 1) * p3' - (y' 0 0 - y' 1 1) * p3
    exact (mul_eq_zero.mp this).resolve_left h2
  have hcF₂ : τ 1 0 * F₂ = 0 := by linear_combination y 1 0 * p3' - y' 1 0 * p3
  have hF₂0 : F₂ = 0 := by linear_combination (-τ 0 0) * haF₂ + (-τ 0 1) * hcF₂ + F₂ * t00
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Fin.zero_eta, Fin.mk_one, Fin.isValue]
  · linear_combination hE0
  · linear_combination hF₁0
  · linear_combination hF₂0
  · linear_combination -hE0

theorem sl2_commute_of_sq {τ y y' : SL(2, F)} (h2 : (2 : F) ≠ 0)
    (hτ : ((τ * τ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1) (hy : y * τ = τ * y)
    (hy' : y' * τ = τ * y') : y * y' = y' * y := by
  have e : ∀ {a b c d : SL(2, F)}, a * b = c * d →
      (a : Matrix (Fin 2) (Fin 2) F) * b = (c : Matrix (Fin 2) (Fin 2) F) * d := fun h => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, h, Matrix.SpecialLinearGroup.coe_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul] at hτ
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  exact mat_commute_of_sq h2 τ.2 hτ (e hy) (e hy')

end Matrix

section Group

variable {H : Type*} [Group H]

theorem commute_commutator_of_central {y₁ y₂ τ : H}
    (h₁ : y₁ * τ * y₁⁻¹ * τ⁻¹ ∈ Subgroup.center H)
    (h₂ : y₂ * τ * y₂⁻¹ * τ⁻¹ ∈ Subgroup.center H) : ⁅y₁, y₂⁆ * τ = τ * ⁅y₁, y₂⁆ := by
  set c₁ := y₁ * τ * y₁⁻¹ * τ⁻¹ with hc₁
  set c₂ := y₂ * τ * y₂⁻¹ * τ⁻¹ with hc₂
  have z₁ := Subgroup.mem_center_iff.mp h₁
  have w₁ := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ h₁)
  have z₂ := Subgroup.mem_center_iff.mp h₂
  have w₂ := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ h₂)
  have A₁ : y₁ * τ * y₁⁻¹ = c₁ * τ := by rw [hc₁]; group
  have A₂ : y₂ * τ * y₂⁻¹ = c₂ * τ := by rw [hc₂]; group
  have B₁ : y₁⁻¹ * τ * y₁ = c₁⁻¹ * τ := by
    calc y₁⁻¹ * τ * y₁ = c₁⁻¹ * (c₁ * y₁⁻¹) * τ * y₁ := by group
      _ = c₁⁻¹ * (y₁⁻¹ * c₁) * τ * y₁ := by rw [← z₁ y₁⁻¹]
      _ = c₁⁻¹ * (y₁⁻¹ * (c₁ * τ) * y₁) := by group
      _ = c₁⁻¹ * (y₁⁻¹ * (y₁ * τ * y₁⁻¹) * y₁) := by rw [A₁]
      _ = c₁⁻¹ * τ := by group
  have B₂ : y₂⁻¹ * τ * y₂ = c₂⁻¹ * τ := by
    calc y₂⁻¹ * τ * y₂ = c₂⁻¹ * (c₂ * y₂⁻¹) * τ * y₂ := by group
      _ = c₂⁻¹ * (y₂⁻¹ * c₂) * τ * y₂ := by rw [← z₂ y₂⁻¹]
      _ = c₂⁻¹ * (y₂⁻¹ * (c₂ * τ) * y₂) := by group
      _ = c₂⁻¹ * (y₂⁻¹ * (y₂ * τ * y₂⁻¹) * y₂) := by rw [A₂]
      _ = c₂⁻¹ * τ := by group
  have key : (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * τ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)⁻¹ = τ := by
    calc (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * τ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)⁻¹
        = y₁ * y₂ * y₁⁻¹ * (y₂⁻¹ * τ * y₂) * y₁ * y₂⁻¹ * y₁⁻¹ := by group
      _ = y₁ * y₂ * y₁⁻¹ * (c₂⁻¹ * τ) * y₁ * y₂⁻¹ * y₁⁻¹ := by rw [B₂]
      _ = (y₁ * y₂ * y₁⁻¹ * c₂⁻¹) * τ * y₁ * y₂⁻¹ * y₁⁻¹ := by group
      _ = (c₂⁻¹ * (y₁ * y₂ * y₁⁻¹)) * τ * y₁ * y₂⁻¹ * y₁⁻¹ := by rw [w₂ (y₁ * y₂ * y₁⁻¹)]
      _ = c₂⁻¹ * (y₁ * y₂ * (y₁⁻¹ * τ * y₁) * y₂⁻¹ * y₁⁻¹) := by group
      _ = c₂⁻¹ * (y₁ * y₂ * (c₁⁻¹ * τ) * y₂⁻¹ * y₁⁻¹) := by rw [B₁]
      _ = c₂⁻¹ * ((y₁ * y₂ * c₁⁻¹) * τ * y₂⁻¹ * y₁⁻¹) := by group
      _ = c₂⁻¹ * ((c₁⁻¹ * (y₁ * y₂)) * τ * y₂⁻¹ * y₁⁻¹) := by rw [w₁ (y₁ * y₂)]
      _ = c₂⁻¹ * (c₁⁻¹ * (y₁ * (y₂ * τ * y₂⁻¹) * y₁⁻¹)) := by group
      _ = c₂⁻¹ * (c₁⁻¹ * (y₁ * (c₂ * τ) * y₁⁻¹)) := by rw [A₂]
      _ = c₂⁻¹ * (c₁⁻¹ * ((y₁ * c₂) * τ * y₁⁻¹)) := by group
      _ = c₂⁻¹ * (c₁⁻¹ * ((c₂ * y₁) * τ * y₁⁻¹)) := by rw [z₂ y₁]
      _ = c₂⁻¹ * (c₁⁻¹ * (c₂ * (y₁ * τ * y₁⁻¹))) := by group
      _ = c₂⁻¹ * (c₁⁻¹ * (c₂ * (c₁ * τ))) := by rw [A₁]
      _ = c₂⁻¹ * ((c₁⁻¹ * c₂) * c₁ * τ) := by group
      _ = c₂⁻¹ * ((c₂ * c₁⁻¹) * c₁ * τ) := by rw [← w₁ c₂]
      _ = τ := by group
  rw [commutatorElement_def]
  calc y₁ * y₂ * y₁⁻¹ * y₂⁻¹ * τ
      = ((y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * τ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹)⁻¹) *
        (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by group
    _ = τ * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) := by rw [key]

theorem conj_eq_one_iff_mem_center {g : H} : MulAut.conj g = 1 ↔ g ∈ Subgroup.center H := by
  constructor
  · intro h
    refine Subgroup.mem_center_iff.mpr fun x => ?_
    have := DFunLike.congr_fun h x
    rw [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · intro h
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, ← Subgroup.mem_center_iff.mp h x]
    group

end Group

section Aut

variable {F : Type} [Field F] [Finite F]

theorem two_ne_zero_of_odd (hF : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  have : Fintype F := Fintype.ofFinite F
  apply Ring.two_ne_zero
  intro h
  have h0 := FiniteField.even_card_iff_char_two.mp h
  rw [Nat.card_eq_fintype_card, Nat.odd_iff] at hF
  omega

theorem derived_map_eq_one (hF : Odd (Nat.card F)) {τ : SL(2, F)}
    (hτ : ((τ * τ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = -1) {Q : Type*} [Group Q]
    (ρ : Q →* MulAut SL(2, F)) (hc : ∀ q, ρ q * MulAut.conj τ = MulAut.conj τ * ρ q) :
    ∀ q ∈ derivedSeries Q 3, ρ q = 1 := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hF
  have hmap : ∀ n, (derivedSeries Q n).map ρ =
      Nat.rec (motive := fun _ => Subgroup (MulAut SL(2, F))) ρ.range
        (fun _ H => ⁅H, H⁆) n := by
    intro n
    induction n with
    | zero =>
      rw [derivedSeries_zero, ← MonoidHom.range_eq_map]
      rfl
    | succ n ih => rw [derivedSeries_succ, Subgroup.map_commutator, ih]
  set I := ρ.range with hI
  set C := Subgroup.centralizer ({MulAut.conj τ} : Set (MulAut SL(2, F))) with hC
  have hIC : I ≤ C := by
    rintro _ ⟨q, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hc q)
  have hI₁C : ⁅I, I⁆ ≤ C :=
    (Subgroup.commutator_mono hIC hIC).trans (Subgroup.commutator_le_self C)
  have hinn : ⁅I, I⁆ ≤ (MulAut.conj : SL(2, F) →* MulAut SL(2, F)).range := by
    rw [Subgroup.commutator_le]
    intro α _ β _
    obtain ⟨y, hy⟩ := CFSG.ComponentClassification.RankTwoOddLie.sl2OuterComm F hF α β
    exact ⟨y, by rw [← hy, commutatorElement_def]⟩
  have hcen : ∀ α ∈ ⁅I, I⁆, ∃ y : SL(2, F), MulAut.conj y = α ∧
      y * τ * y⁻¹ * τ⁻¹ ∈ Subgroup.center SL(2, F) := by
    intro α hα
    obtain ⟨y, hy⟩ := hinn hα
    refine ⟨y, hy, conj_eq_one_iff_mem_center.mp ?_⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hI₁C hα)
    rw [← hy] at h
    simp only [map_mul, map_inv]
    rw [h]
    group
  set A : Subgroup (MulAut SL(2, F)) :=
    (Subgroup.centralizer ({τ} : Set SL(2, F))).map MulAut.conj with hA
  have hI₂A : ⁅⁅I, I⁆, ⁅I, I⁆⁆ ≤ A := by
    rw [Subgroup.commutator_le]
    intro α hα β hβ
    obtain ⟨y₁, rfl, h₁⟩ := hcen α hα
    obtain ⟨y₂, rfl, h₂⟩ := hcen β hβ
    exact ⟨⁅y₁, y₂⁆, Subgroup.mem_centralizer_singleton_iff.mpr
      (commute_commutator_of_central h₁ h₂), map_commutatorElement _ _ _⟩
  have hAc : ⁅A, A⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨c₁, hc₁, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨c₂, hc₂, rfl⟩
    rw [← map_mul, ← map_mul, sl2_commute_of_sq h2 hτ
      (Subgroup.mem_centralizer_singleton_iff.mp hc₂)
      (Subgroup.mem_centralizer_singleton_iff.mp hc₁)]
  have hI₃ : (derivedSeries Q 3).map ρ = ⊥ := by
    rw [hmap 3]
    exact le_bot_iff.mp (hAc ▸ Subgroup.commutator_mono hI₂A hI₂A)
  intro q hq
  have : ρ q ∈ (derivedSeries Q 3).map ρ := ⟨q, hq, rfl⟩
  rw [hI₃, Subgroup.mem_bot] at this
  exact this

end Aut

end CFSG.ClassicalInvolution.NDB.WC
