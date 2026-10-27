module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Basis.Bilinear
public import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LinearAlgebra

open Module

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

structure IsAltTrilinForm (τ : V → V → V → F) : Prop where
  add_left : ∀ x x' y z, τ (x + x') y z = τ x y z + τ x' y z
  smul_left : ∀ (c : F) x y z, τ (c • x) y z = c * τ x y z
  add_mid : ∀ x y y' z, τ x (y + y') z = τ x y z + τ x y' z
  smul_mid : ∀ (c : F) x y z, τ x (c • y) z = c * τ x y z
  add_right : ∀ x y z z', τ x y (z + z') = τ x y z + τ x y z'
  smul_right : ∀ (c : F) x y z, τ x y (c • z) = c * τ x y z
  self₁₂ : ∀ x z, τ x x z = 0
  self₂₃ : ∀ x y, τ x y y = 0

namespace IsAltTrilinForm

variable {τ : V → V → V → F}

theorem anti₁₂ (h : IsAltTrilinForm τ) (x y z : V) : τ x y z = -τ y x z := by
  have e := h.self₁₂ (x + y) z
  rw [h.add_left, h.add_mid, h.add_mid, h.self₁₂, h.self₁₂] at e
  linear_combination e

theorem anti₂₃ (h : IsAltTrilinForm τ) (x y z : V) : τ x y z = -τ x z y := by
  have e := h.self₂₃ x (y + z)
  rw [h.add_mid, h.add_right, h.add_right, h.self₂₃, h.self₂₃] at e
  linear_combination e

theorem self₁₃ (h : IsAltTrilinForm τ) (x y : V) : τ x y x = 0 := by
  rw [h.anti₂₃, h.self₁₂, neg_zero]

theorem cyc (h : IsAltTrilinForm τ) (x y z : V) : τ x y z = τ y z x := by
  rw [h.anti₁₂, h.anti₂₃ y, neg_neg]

@[expose] def toLin (h : IsAltTrilinForm τ) : V →ₗ[F] V →ₗ[F] V →ₗ[F] F :=
  LinearMap.mk₂ F
    (fun x y =>
      { toFun := τ x y
        map_add' := h.add_right x y
        map_smul' := fun c z => h.smul_right c x y z })
    (fun x x' y => LinearMap.ext fun z => h.add_left x x' y z)
    (fun c x y => LinearMap.ext fun z => h.smul_left c x y z)
    (fun x y y' => LinearMap.ext fun z => h.add_mid x y y' z)
    (fun c x y => LinearMap.ext fun z => h.smul_mid c x y z)

@[simp] theorem toLin_apply (h : IsAltTrilinForm τ) (x y z : V) : h.toLin x y z = τ x y z := rfl

theorem radical_of_basis (h : IsAltTrilinForm τ) {ι : Type*} (b : Basis ι F V) {x : V}
    (hx : ∀ j k, τ x (b j) (b k) = 0) (y z : V) : τ x y z = 0 := by
  have : h.toLin x = 0 := LinearMap.ext_basis b b fun j k => by simpa using hx j k
  simpa using LinearMap.congr_fun₂ this y z

theorem eq_zero_of_basis (h : IsAltTrilinForm τ) {ι : Type*} (b : Basis ι F V)
    (hb : ∀ i j k, τ (b i) (b j) (b k) = 0) (x y z : V) : τ x y z = 0 := by
  have : h.toLin = 0 := Basis.ext b fun i => LinearMap.ext_basis b b fun j k => by
    simpa using hb i j k
  have h2 := LinearMap.congr_fun₂ this x y
  simpa using LinearMap.congr_fun h2 z

theorem apply_add_four (h : IsAltTrilinForm τ) (b₀ b₁ b₂ b₃ y z : V) (c₀ c₁ c₂ c₃ : F) :
    τ (c₀ • b₀ + c₁ • b₁ + c₂ • b₂ + c₃ • b₃) y z =
      c₀ * τ b₀ y z + c₁ * τ b₁ y z + c₂ * τ b₂ y z + c₃ * τ b₃ y z := by
  rw [h.add_left, h.add_left, h.add_left, h.smul_left, h.smul_left, h.smul_left, h.smul_left]

theorem radical_of_basis_lt (h : IsAltTrilinForm τ) {n : ℕ} (b : Basis (Fin n) F V) {x : V}
    (hx : ∀ j k, j < k → τ x (b j) (b k) = 0) (y z : V) : τ x y z = 0 := by
  refine h.radical_of_basis b (fun j k => ?_) y z
  rcases lt_trichotomy j k with hjk | rfl | hjk
  · exact hx j k hjk
  · exact h.self₂₃ _ _
  · rw [h.anti₂₃, hx k j hjk, neg_zero]

theorem eq_zero_of_finrank_eq_two (h : IsAltTrilinForm τ) [Module.Finite F V]
    (hV : finrank F V = 2) (x y z : V) :
    τ x y z = 0 := by
  set b := Module.finBasisOfFinrankEq F V hV
  refine h.eq_zero_of_basis b (fun i j k => ?_) x y z
  fin_cases i <;> fin_cases j <;> fin_cases k
  all_goals first
    | exact h.self₁₂ _ _
    | exact h.self₁₃ _ _
    | exact h.self₂₃ _ _

private theorem exists_radical_of_basis_of_eq_zero (h : IsAltTrilinForm τ) (b : Basis (Fin 4) F V)
    (h₀₂₃ : τ (b 0) (b 2) (b 3) = 0) (h₀₁₃ : τ (b 0) (b 1) (b 3) = 0)
    (h₀₁₂ : τ (b 0) (b 1) (b 2) = 0) :
    ∃ x, x ≠ 0 ∧ ∀ y z, τ x y z = 0 := by
  refine ⟨b 0, b.ne_zero 0, h.radical_of_basis_lt b fun j k hjk => ?_⟩
  fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd hjk (by decide)
    | exact h.self₁₂ _ _
    | exact h.self₁₃ _ _
    | exact h₀₁₂
    | exact h₀₁₃
    | exact h₀₂₃

private theorem exists_radical_of_basis_of_ne_zero (h : IsAltTrilinForm τ) (b : Basis (Fin 4) F V)
    (hall : ¬ (τ (b 1) (b 2) (b 3) = 0 ∧ τ (b 0) (b 2) (b 3) = 0 ∧
      τ (b 0) (b 1) (b 3) = 0 ∧ τ (b 0) (b 1) (b 2) = 0)) :
    ∃ x, x ≠ 0 ∧ ∀ y z, τ x y z = 0 := by
  set t₁₂₃ := τ (b 1) (b 2) (b 3) with ht₁₂₃
  set t₀₂₃ := τ (b 0) (b 2) (b 3) with ht₀₂₃
  set t₀₁₃ := τ (b 0) (b 1) (b 3) with ht₀₁₃
  set t₀₁₂ := τ (b 0) (b 1) (b 2) with ht₀₁₂
  have hall' : ¬ (t₁₂₃ = 0 ∧ t₀₂₃ = 0 ∧ t₀₁₃ = 0 ∧ t₀₁₂ = 0) := by
    simpa only [← ht₁₂₃, ← ht₀₂₃, ← ht₀₁₃, ← ht₀₁₂] using hall
  set x := t₁₂₃ • b 0 + (-t₀₂₃) • b 1 + t₀₁₃ • b 2 + (-t₀₁₂) • b 3 with hx
  refine ⟨x, fun hx0 => hall' ?_, h.radical_of_basis_lt b fun j k hjk => ?_⟩
  · have hrep : ∀ i, b.repr x i = 0 := fun i => by rw [hx0, map_zero, Finsupp.zero_apply]
    have r0 := hrep 0
    have r1 := hrep 1
    have r2 := hrep 2
    have r3 := hrep 3
    simp only [hx, map_add, map_smul, Basis.repr_self, Finsupp.add_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul] at r0 r1 r2 r3
    simp at r0 r1 r2 r3
    exact ⟨r0, r1, r2, r3⟩
  · have c20 : τ (b 2) (b 0) (b 1) = t₀₁₂ := h.cyc _ _ _
    have c30 : τ (b 3) (b 0) (b 1) = t₀₁₃ := h.cyc _ _ _
    have c10 : τ (b 1) (b 0) (b 2) = -t₀₁₂ := h.anti₁₂ _ _ _
    have c30' : τ (b 3) (b 0) (b 2) = t₀₂₃ := h.cyc _ _ _
    have c10' : τ (b 1) (b 0) (b 3) = -t₀₁₃ := h.anti₁₂ _ _ _
    have c20' : τ (b 2) (b 0) (b 3) = -t₀₂₃ := h.anti₁₂ _ _ _
    have c01 : τ (b 0) (b 1) (b 2) = t₀₁₂ := rfl
    have c31 : τ (b 3) (b 1) (b 2) = t₁₂₃ := h.cyc _ _ _
    have c01' : τ (b 0) (b 1) (b 3) = t₀₁₃ := rfl
    have c21 : τ (b 2) (b 1) (b 3) = -t₁₂₃ := h.anti₁₂ _ _ _
    have c02 : τ (b 0) (b 2) (b 3) = t₀₂₃ := rfl
    have c12 : τ (b 1) (b 2) (b 3) = t₁₂₃ := rfl
    fin_cases j <;> fin_cases k
    all_goals first
      | exact absurd hjk (by decide)
      | (simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue]
         rw [hx, h.apply_add_four]
         simp only [h.self₁₂, h.self₁₃, c20, c30, c10, c30', c10', c20', c01, c31, c01', c21,
           c02, c12]
         ring)

theorem exists_radical_of_finrank_eq_four (h : IsAltTrilinForm τ) [Module.Finite F V]
    (hV : finrank F V = 4) :
    ∃ x, x ≠ 0 ∧ ∀ y z, τ x y z = 0 := by
  set b := Module.finBasisOfFinrankEq F V hV
  by_cases hall : τ (b 1) (b 2) (b 3) = 0 ∧ τ (b 0) (b 2) (b 3) = 0 ∧
      τ (b 0) (b 1) (b 3) = 0 ∧ τ (b 0) (b 1) (b 2) = 0
  · exact exists_radical_of_basis_of_eq_zero h b hall.2.1 hall.2.2.1 hall.2.2.2
  · exact exists_radical_of_basis_of_ne_zero h b hall

theorem restrict (h : IsAltTrilinForm τ) (C : Submodule F V) :
    IsAltTrilinForm (fun x y z : C => τ x y z) where
  add_left x x' y z := h.add_left x x' y z
  smul_left c x y z := h.smul_left c x y z
  add_mid x y y' z := h.add_mid x y y' z
  smul_mid c x y z := h.smul_mid c x y z
  add_right x y z z' := h.add_right x y z z'
  smul_right c x y z := h.smul_right c x y z
  self₁₂ x z := h.self₁₂ x z
  self₂₃ x y := h.self₂₃ x y

theorem radical_of_sup (h : IsAltTrilinForm τ) {C R : Submodule F V} (hCR : C ⊔ R = ⊤)
    (hR : ∀ r ∈ R, ∀ y z, τ r y z = 0) {x : V} (hx : ∀ c ∈ C, ∀ c' ∈ C, τ x c c' = 0)
    (y z : V) : τ x y z = 0 := by
  have hdec : ∀ w : V, ∃ c ∈ C, ∃ r ∈ R, w = c + r := fun w => by
    have hw : w ∈ C ⊔ R := hCR ▸ Submodule.mem_top
    obtain ⟨c, hc, r, hr, rfl⟩ := Submodule.mem_sup.mp hw
    exact ⟨c, hc, r, hr, rfl⟩
  have hR2 : ∀ r ∈ R, ∀ y, τ x r y = 0 := fun r hr y => by
    rw [h.anti₁₂, hR r hr, neg_zero]
  have hR3 : ∀ r ∈ R, ∀ y, τ x y r = 0 := fun r hr y => by
    rw [h.anti₂₃, hR2 r hr, neg_zero]
  obtain ⟨c, hc, r, hr, rfl⟩ := hdec y
  obtain ⟨c', hc', r', hr', rfl⟩ := hdec z
  rw [h.add_mid, h.add_right, h.add_right, hx c hc c' hc', hR3 r' hr', hR2 r hr, hR2 r hr]
  simp

theorem false_of_isCompl_finrank_two (h : IsAltTrilinForm τ) [Module.Finite F V]
    {C R : Submodule F V}
    (hCR : IsCompl C R) (hR : ∀ r ∈ R, ∀ y z, τ r y z = 0)
    (hrad : ∀ x, (∀ y z, τ x y z = 0) → x ∈ R) (hC : finrank F C = 2) : False := by
  have hT0 := (h.restrict C).eq_zero_of_finrank_eq_two hC
  have hsub : C ≤ R := fun x hx => hrad x (h.radical_of_sup hCR.sup_eq_top hR
    fun c hc c' hc' => hT0 ⟨x, hx⟩ ⟨c, hc⟩ ⟨c', hc'⟩)
  have hbot : C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ C ⊓ R := ⟨hx, hsub hx⟩
    rwa [hCR.inf_eq_bot] at this
  rw [hbot, finrank_bot] at hC
  omega

theorem false_of_isCompl_finrank_four (h : IsAltTrilinForm τ) [Module.Finite F V]
    {C R : Submodule F V}
    (hCR : IsCompl C R) (hR : ∀ r ∈ R, ∀ y z, τ r y z = 0)
    (hrad : ∀ x, (∀ y z, τ x y z = 0) → x ∈ R) (hC : finrank F C = 4) : False := by
  obtain ⟨⟨x, hxC⟩, hx0, hx⟩ := (h.restrict C).exists_radical_of_finrank_eq_four hC
  have hx' : ∀ c ∈ C, ∀ c' ∈ C, τ x c c' = 0 := fun c hc c' hc' => hx ⟨c, hc⟩ ⟨c', hc'⟩
  have hxR := hrad x (h.radical_of_sup hCR.sup_eq_top hR hx')
  have : x ∈ C ⊓ R := ⟨hxC, hxR⟩
  rw [hCR.inf_eq_bot, Submodule.mem_bot] at this
  exact hx0 (Subtype.ext this)

theorem finrank_ne_add_two_four (h : IsAltTrilinForm τ) [Module.Finite F V] (R : Submodule F V)
    (hR : ∀ r ∈ R, ∀ y z, τ r y z = 0) (hrad : ∀ x, (∀ y z, τ x y z = 0) → x ∈ R) :
    finrank F V ≠ finrank F R + 2 ∧ finrank F V ≠ finrank F R + 4 := by
  obtain ⟨C, hRC⟩ := Submodule.exists_isCompl R
  have hdim := Submodule.finrank_add_eq_of_isCompl hRC
  exact ⟨fun h2 => h.false_of_isCompl_finrank_two hRC.symm hR hrad (by omega),
    fun h4 => h.false_of_isCompl_finrank_four hRC.symm hR hrad (by omega)⟩

end IsAltTrilinForm

end CFSG.LinearAlgebra
