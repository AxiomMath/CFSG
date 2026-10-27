module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphPiecesBlocks
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMismatchTablesSp6
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotLeviFact

public section

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup Matrix
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear
  blockSpecialLinear_mono)
open CFSG.Quasithin (perfectCore)
open scoped MatrixGroups commutatorElement

section Diag

variable {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def diagUnitsSL (w : Fin n → Fˣ) (hw : ∏ i, w i = 1) :
    SpecialLinearGroup (Fin n) F :=
  ⟨Matrix.diagonal fun i => (w i : F), by
    rw [det_diagonal, ← Units.coe_prod, hw, Units.val_one]⟩

@[simp] theorem coe_diagUnitsSL (w : Fin n → Fˣ) (hw : ∏ i, w i = 1) :
    ((diagUnitsSL w hw : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (w i : F) :=
  rfl

@[expose] noncomputable def diagTorusSL (ω : (Fin 3 → Fˣ) →* (Fin n → Fˣ))
    (hω : ∀ t, ∏ i, ω t i = 1) : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F where
  toFun t := diagUnitsSL (ω t) (hω t)
  map_one' := by
    apply Subtype.ext
    rw [coe_diagUnitsSL, map_one]
    simp
  map_mul' t t' := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_diagUnitsSL, coe_diagUnitsSL, coe_diagUnitsSL,
      diagonal_mul_diagonal, map_mul]
    simp

theorem coe_diagTorusSL (ω : (Fin 3 → Fˣ) →* (Fin n → Fˣ)) (hω : ∀ t, ∏ i, ω t i = 1)
    (t : Fin 3 → Fˣ) :
    ((diagTorusSL ω hω t : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (ω t i : F) :=
  rfl

theorem diagTorusSL_apply_ne (ω : (Fin 3 → Fˣ) →* (Fin n → Fˣ)) (hω : ∀ t, ∏ i, ω t i = 1)
    (t : Fin 3 → Fˣ) {i j : Fin n} (hij : i ≠ j) :
    ((diagTorusSL ω hω t : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i j = 0 := by
  rw [coe_diagTorusSL, diagonal_apply_ne _ hij]

theorem diagTorusSL_apply_self (ω : (Fin 3 → Fˣ) →* (Fin n → Fˣ)) (hω : ∀ t, ∏ i, ω t i = 1)
    (t : Fin 3 → Fˣ) (i : Fin n) :
    ((diagTorusSL ω hω t : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i =
      (ω t i : F) := by
  rw [coe_diagTorusSL, diagonal_apply_eq]

structure IsDiagOf (d : SpecialLinearGroup (Fin n) F) (v : Fin 3 → F) (c : Fin n → Fin 3) :
    Prop where
  offDiag : ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0
  diag : ∀ i, (d : Matrix (Fin n) (Fin n) F) i i = v (c i)

theorem IsDiagOf.ne {d : SpecialLinearGroup (Fin n) F} {v : Fin 3 → F} {c : Fin n → Fin 3}
    (h : IsDiagOf d v c) (hv : Function.Injective v) {i j : Fin n} (hij : c i ≠ c j) :
    (d : Matrix (Fin n) (Fin n) F) i i ≠ (d : Matrix (Fin n) (Fin n) F) j j := by
  rw [h.diag, h.diag]
  exact fun h' => hij (hv h')

theorem IsDiagOf.filter_eq [DecidableEq F] {d : SpecialLinearGroup (Fin n) F} {v : Fin 3 → F}
    {c : Fin n → Fin 3} (h : IsDiagOf d v c) (hv : Function.Injective v) (k : Fin 3) :
    (Finset.univ.filter fun j => (d : Matrix (Fin n) (Fin n) F) j j = v k) =
      Finset.univ.filter fun j => c j = k := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h.diag]
  exact hv.eq_iff

theorem val_ne_one_and_inv_of_sq_ne_one {c : Fˣ} (hc : c ^ 2 ≠ 1) :
    (c : F) ≠ 1 ∧ (((c⁻¹ : Fˣ) : F)) ≠ 1 ∧ (c : F) ≠ ((c⁻¹ : Fˣ) : F) := by
  refine ⟨fun h => hc ?_, fun h => hc ?_, fun h => hc ?_⟩
  · rw [Units.val_eq_one.1 h, one_pow]
  · rw [inv_eq_one.1 (Units.val_eq_one.1 h), one_pow]
  · have h' : c = c⁻¹ := Units.val_injective h
    rw [sq, ← mul_inv_cancel c, ← h']

theorem injective_vecValues {a₀ : Fˣ} (hsq : a₀ ^ 2 ≠ 1) :
    Function.Injective (![(a₀ : F), ((a₀⁻¹ : Fˣ) : F), 1] : Fin 3 → F) := by
  obtain ⟨h1, h2, h3⟩ := val_ne_one_and_inv_of_sq_ne_one (F := F) hsq
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

end Diag


section Tori

variable (F : Type) [Field F]

@[expose] noncomputable def lin6Weights : (Fin 3 → Fˣ) →* (Fin 6 → Fˣ) where
  toFun t := ![t 0, t 1, t 2, (t 0)⁻¹, (t 1)⁻¹, (t 2)⁻¹]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' t t' := by
    funext i
    fin_cases i <;> simp [mul_comm]

@[expose] noncomputable def lin7Weights : (Fin 3 → Fˣ) →* (Fin 7 → Fˣ) where
  toFun t := ![t 0, t 1, t 2, (t 0)⁻¹, (t 1)⁻¹, (t 2)⁻¹, 1]
  map_one' := by
    funext i
    fin_cases i <;> simp
  map_mul' t t' := by
    funext i
    fin_cases i <;> simp [mul_comm]

theorem prod_lin6Weights (t : Fin 3 → Fˣ) : ∏ i, lin6Weights F t i = 1 := by
  rw [Fin.prod_univ_six]
  change t 0 * t 1 * t 2 * (t 0)⁻¹ * (t 1)⁻¹ * (t 2)⁻¹ = 1
  calc t 0 * t 1 * t 2 * (t 0)⁻¹ * (t 1)⁻¹ * (t 2)⁻¹ =
      (t 0 * (t 0)⁻¹) * (t 1 * (t 1)⁻¹) * (t 2 * (t 2)⁻¹) := by ac_rfl
    _ = 1 := by simp

theorem prod_lin7Weights (t : Fin 3 → Fˣ) : ∏ i, lin7Weights F t i = 1 := by
  rw [Fin.prod_univ_seven]
  change t 0 * t 1 * t 2 * (t 0)⁻¹ * (t 1)⁻¹ * (t 2)⁻¹ * 1 = 1
  calc t 0 * t 1 * t 2 * (t 0)⁻¹ * (t 1)⁻¹ * (t 2)⁻¹ * 1 =
      (t 0 * (t 0)⁻¹) * (t 1 * (t 1)⁻¹) * (t 2 * (t 2)⁻¹) := by rw [mul_one]; ac_rfl
    _ = 1 := by simp

@[expose] noncomputable def lin6Torus : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin 6) F :=
  diagTorusSL (lin6Weights F) (prod_lin6Weights F)

@[expose] noncomputable def lin7Torus : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin 7) F :=
  diagTorusSL (lin7Weights F) (prod_lin7Weights F)

variable {F} {n : ℕ}

@[expose] noncomputable def linTorusA (τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F)
    (A : Subgroup Fˣ) : Subgroup (SpecialLinearGroup (Fin n) F) :=
  A.map (τ.comp (sp6ParamA F))

@[expose] noncomputable def linTorusM2 (τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F)
    (A : Subgroup Fˣ) : Subgroup (SpecialLinearGroup (Fin n) F) :=
  (A.prod A).map (τ.comp (sp6ParamM2 F))

@[expose] noncomputable def linTorusM3 (τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F)
    (A : Subgroup Fˣ) : Subgroup (SpecialLinearGroup (Fin n) F) :=
  (A.prod A).map (τ.comp (sp6ParamM3 F))

theorem sp6ParamA_apply (a : Fˣ) : sp6ParamA F a = ![a, 1, 1] := by
  funext i
  fin_cases i <;> rfl

theorem sp6ParamM2_apply (p : Fˣ × Fˣ) : sp6ParamM2 F p = ![p.1, p.2, 1] := by
  funext i
  fin_cases i <;> simp [sp6ParamM2]

theorem sp6ParamM3_apply (p : Fˣ × Fˣ) : sp6ParamM3 F p = ![p.1, p.2, p.2] := by
  funext i
  fin_cases i <;> simp [sp6ParamM3]

end Tori


section Generic

variable {F : Type} [Field F] {n : ℕ}

theorem offDiag_of_mem_map_diagTorusSL {ω : (Fin 3 → Fˣ) →* (Fin n → Fˣ)}
    {hω : ∀ t, ∏ i, ω t i = 1} {P : Type*} [Group P] {H : Subgroup P}
    {π : P →* (Fin 3 → Fˣ)} {d : SpecialLinearGroup (Fin n) F}
    (hd : d ∈ H.map ((diagTorusSL ω hω).comp π)) :
    ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0 := by
  obtain ⟨p, -, rfl⟩ := hd
  exact fun i j hij => diagTorusSL_apply_ne ω hω (π p) hij

theorem exists_mem_ne_of_isDiagOf {D : Set (SpecialLinearGroup (Fin n) F)}
    {d₀ d₁ : SpecialLinearGroup (Fin n) F} (h₀ : d₀ ∈ D) (h₁ : d₁ ∈ D) {v : Fin 3 → F}
    (hv : Function.Injective v) {c₀ c₁ : Fin n → Fin 3} (hd₀ : IsDiagOf d₀ v c₀)
    (hd₁ : IsDiagOf d₁ v c₁) {i j : Fin n} (h : c₀ i ≠ c₀ j ∨ c₁ i ≠ c₁ j) :
    ∃ d ∈ D, (d : Matrix (Fin n) (Fin n) F) i i ≠ (d : Matrix (Fin n) (Fin n) F) j j := by
  rcases h with h | h
  · exact ⟨d₀, h₀, hd₀.ne hv h⟩
  · exact ⟨d₁, h₁, hd₁.ne hv h⟩

theorem rigid_of_isDiagOf [DecidableEq F] {S : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hdiag : ∀ d ∈ S, ∀ i j, i ≠ j → (d : Matrix (Fin n) (Fin n) F) i j = 0)
    {s₀ : SpecialLinearGroup (Fin n) F} (hs₀ : s₀ ∈ S) {v : Fin 3 → F}
    (hv : Function.Injective v) {c : Fin n → Fin 3} (hd : IsDiagOf s₀ v c) (k : Fin 3)
    (hdom : n < 2 * (Finset.univ.filter fun j => c j = k).card) (j₀ : Fin n)
    (hj₀ : ∀ i, i ≠ j₀ → c i ≠ c j₀) (x : SpecialLinearGroup (Fin n) F)
    (hx : ∀ s ∈ S, ⁅x, s⁆ ∈ center (SpecialLinearGroup (Fin n) F)) :
    x ∈ centralizer (S : Set (SpecialLinearGroup (Fin n) F)) :=
  mem_centralizer_of_commutator_mem_center (D := (S : Set _)) hdiag hs₀ (c := v k)
    (by rw [hd.filter_eq hv k]; exact hdom) (j₀ := j₀) (fun i hi => hd.ne hv (hj₀ i hi)) hx


theorem mem_linTorusA (τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F) {A : Subgroup Fˣ}
    {a : Fˣ} (ha : a ∈ A) : τ ![a, 1, 1] ∈ linTorusA τ A :=
  ⟨a, ha, by rw [MonoidHom.comp_apply, sp6ParamA_apply]⟩

theorem mem_linTorusM2 (τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F) {A : Subgroup Fˣ}
    {a b : Fˣ} (ha : a ∈ A) (hb : b ∈ A) : τ ![a, b, 1] ∈ linTorusM2 τ A :=
  ⟨(a, b), ⟨ha, hb⟩, by rw [MonoidHom.comp_apply, sp6ParamM2_apply]⟩

theorem mem_linTorusM3 (τ : (Fin 3 → Fˣ) →* SpecialLinearGroup (Fin n) F) {A : Subgroup Fˣ}
    {a b : Fˣ} (ha : a ∈ A) (hb : b ∈ A) : τ ![a, b, b] ∈ linTorusM3 τ A :=
  ⟨(a, b), ⟨ha, hb⟩, by rw [MonoidHom.comp_apply, sp6ParamM3_apply]⟩

@[expose] noncomputable def sepValues (a₀ : Fˣ) : Fin 3 → F := ![(a₀ : F), ((a₀⁻¹ : Fˣ) : F), 1]

theorem injective_sepValues {a₀ : Fˣ} (hsq : a₀ ^ 2 ≠ 1) :
    Function.Injective (sepValues (F := F) a₀) :=
  injective_vecValues hsq

end Generic

section Linear6

variable {F : Type} [Field F]

theorem lin6Weights_apply (t : Fin 3 → Fˣ) :
    lin6Weights F t = ![t 0, t 1, t 2, (t 0)⁻¹, (t 1)⁻¹, (t 2)⁻¹] :=
  rfl

theorem lin6Torus_apply_self (t : Fin 3 → Fˣ) (i : Fin 6) :
    ((lin6Torus F t : SpecialLinearGroup (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i i =
      ((![t 0, t 1, t 2, (t 0)⁻¹, (t 1)⁻¹, (t 2)⁻¹] : Fin 6 → Fˣ) i : F) :=
  diagTorusSL_apply_self _ _ t i

theorem isDiagOf_lin6Torus_A (a₀ : Fˣ) :
    IsDiagOf (lin6Torus F ![a₀, 1, 1]) (sepValues a₀) ![0, 2, 2, 1, 2, 2] where
  offDiag i j hij := diagTorusSL_apply_ne _ _ _ hij
  diag i := by
    rw [lin6Torus_apply_self]
    fin_cases i <;> simp [sepValues]

theorem isDiagOf_lin6Torus_B (a₀ : Fˣ) :
    IsDiagOf (lin6Torus F ![1, a₀, 1]) (sepValues a₀) ![2, 0, 2, 2, 1, 2] where
  offDiag i j hij := diagTorusSL_apply_ne _ _ _ hij
  diag i := by
    rw [lin6Torus_apply_self]
    fin_cases i <;> simp [sepValues]

theorem isDiagOf_lin6Torus_C (a₀ : Fˣ) :
    IsDiagOf (lin6Torus F ![1, a₀, a₀]) (sepValues a₀) ![2, 0, 0, 2, 1, 1] where
  offDiag i j hij := diagTorusSL_apply_ne _ _ _ hij
  diag i := by
    rw [lin6Torus_apply_self]
    fin_cases i <;> simp [sepValues]


@[expose] def lin6BlockA : Finset (Fin 6) := {1, 2, 4, 5}

@[expose] def lin6BlockM2 : Finset (Fin 6) := {2, 5}

@[expose] def linBlockE (n : ℕ) [NeZero n] : Finset (Fin n) := {1, 2}

@[expose] def linBlockF (n : ℕ) [NeZero n] : Finset (Fin n) := {4, 5}

variable [Finite F]

theorem perfectCore_centralizer_lin6TorusA (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (linTorusA (lin6Torus F) A : Set (SpecialLinearGroup (Fin 6) F))) =
      blockSpecialLinear (K := F) lin6BlockA := by
  have hv := injective_sepValues (F := F) hsq
  have key : ∀ i j : Fin 6, i ≠ j → (i ∉ lin6BlockA ∨ j ∉ lin6BlockA) →
      (![0, 2, 2, 1, 2, 2] : Fin 6 → Fin 3) i ≠ ![0, 2, 2, 1, 2, 2] j := by decide
  have h := CFSG.SeitzReduction.LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear
    (N := Finset.univ) (Finset.subset_univ lin6BlockA)
    (linTorusA (lin6Torus F) A : Set (SpecialLinearGroup (Fin 6) F))
    (fun d hd => offDiag_of_mem_map_diagTorusSL hd)
    (by
      rintro _ ⟨a, -, rfl⟩ i hi j hj
      rw [MonoidHom.comp_apply, sp6ParamA_apply, lin6Torus_apply_self, lin6Torus_apply_self]
      simp only [lin6BlockA, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;> simp)
    (fun i _ j _ hij hIJ => exists_mem_ne_of_isDiagOf (mem_linTorusA _ ha₀)
      (mem_linTorusA _ ha₀) hv (isDiagOf_lin6Torus_A a₀) (isDiagOf_lin6Torus_A a₀)
      (Or.inl (key i j hij hIJ)))
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
      (by decide) hF)
  rwa [CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_univ, top_inf_eq] at h

theorem perfectCore_centralizer_lin6TorusM2 (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (linTorusM2 (lin6Torus F) A : Set (SpecialLinearGroup (Fin 6) F))) =
      blockSpecialLinear (K := F) lin6BlockM2 := by
  have hv := injective_sepValues (F := F) hsq
  have key : ∀ i j : Fin 6, i ≠ j → (i ∉ lin6BlockM2 ∨ j ∉ lin6BlockM2) →
      (![0, 2, 2, 1, 2, 2] : Fin 6 → Fin 3) i ≠ ![0, 2, 2, 1, 2, 2] j ∨
        (![2, 0, 2, 2, 1, 2] : Fin 6 → Fin 3) i ≠ ![2, 0, 2, 2, 1, 2] j := by decide
  have h := CFSG.SeitzReduction.LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear
    (N := Finset.univ) (Finset.subset_univ lin6BlockM2)
    (linTorusM2 (lin6Torus F) A : Set (SpecialLinearGroup (Fin 6) F))
    (fun d hd => offDiag_of_mem_map_diagTorusSL hd)
    (by
      rintro _ ⟨p, -, rfl⟩ i hi j hj
      rw [MonoidHom.comp_apply, sp6ParamM2_apply, lin6Torus_apply_self, lin6Torus_apply_self]
      simp only [lin6BlockM2, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp)
    (fun i _ j _ hij hIJ => exists_mem_ne_of_isDiagOf (mem_linTorusM2 _ ha₀ (one_mem A))
      (mem_linTorusM2 _ (one_mem A) ha₀) hv (isDiagOf_lin6Torus_A a₀) (isDiagOf_lin6Torus_B a₀)
      (key i j hij hIJ))
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
      (by decide) hF)
  rwa [CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_univ, top_inf_eq] at h

theorem perfectCore_centralizer_lin6TorusM3 (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (linTorusM3 (lin6Torus F) A : Set (SpecialLinearGroup (Fin 6) F))) =
      blockSpecialLinear (K := F) (linBlockE 6) ⊔ blockSpecialLinear (linBlockF 6) := by
  have hv := injective_sepValues (F := F) hsq
  have key : ∀ i j : Fin 6, i ≠ j → ¬ (i ∈ linBlockE 6 ∧ j ∈ linBlockE 6) →
      ¬ (i ∈ linBlockF 6 ∧ j ∈ linBlockF 6) →
      (![0, 2, 2, 1, 2, 2] : Fin 6 → Fin 3) i ≠ ![0, 2, 2, 1, 2, 2] j ∨
        (![2, 0, 0, 2, 1, 1] : Fin 6 → Fin 3) i ≠ ![2, 0, 0, 2, 1, 1] j := by decide
  have hconst : ∀ (B : Finset (Fin 6)), (B = linBlockE 6 ∨ B = linBlockF 6) →
      ∀ d ∈ (linTorusM3 (lin6Torus F) A : Set (SpecialLinearGroup (Fin 6) F)), ∀ i ∈ B, ∀ j ∈ B,
        (d : Matrix (Fin 6) (Fin 6) F) i i = (d : Matrix (Fin 6) (Fin 6) F) j j := by
    rintro B hB _ ⟨p, -, rfl⟩ i hi j hj
    rw [MonoidHom.comp_apply, sp6ParamM3_apply, lin6Torus_apply_self, lin6Torus_apply_self]
    rcases hB with rfl | rfl <;>
      simp only [linBlockE, linBlockF, Finset.mem_insert, Finset.mem_singleton] at hi hj <;>
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp
  exact perfectCore_centralizer_eq_sup_of_two_blocks (by decide) _
    (fun d hd => offDiag_of_mem_map_diagTorusSL hd) (hconst _ (.inl rfl)) (hconst _ (.inr rfl))
    (fun i j hij h₁ h₂ => exists_mem_ne_of_isDiagOf (mem_linTorusM3 _ ha₀ (one_mem A))
      (mem_linTorusM3 _ (one_mem A) ha₀) hv (isDiagOf_lin6Torus_A a₀) (isDiagOf_lin6Torus_C a₀)
      (key i j hij h₁ h₂))
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)

end Linear6


section Orders

variable {F : Type} [Field F] [Finite F] {n : ℕ}

theorem natCard_sup_blockSpecialLinear_two_two {I₁ I₂ : Finset (Fin n)} (h : Disjoint I₁ I₂)
    (h₁ : I₁.card = 2) (h₂ : I₂.card = 2) :
    Nat.card (blockSpecialLinear (K := F) I₁ ⊔ blockSpecialLinear I₂ : Subgroup _) =
      ordSL 2 (Nat.card F) ^ 2 := by
  rw [natCard_sup_blockSpecialLinear_of_disjoint h, natCard_blockSpecialLinear (by omega),
    natCard_blockSpecialLinear (by omega), h₁, h₂, sq]

theorem natCard_piece_range_of_rigid {G : Type*} [Group G] [Finite G]
    (Φ : SpecialLinearGroup (Fin n) F →* G) (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin n) F))
    {S : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hrig : ∀ x : SpecialLinearGroup (Fin n) F,
      (∀ s ∈ S, ⁅x, s⁆ ∈ center (SpecialLinearGroup (Fin n) F)) →
        x ∈ centralizer (S : Set (SpecialLinearGroup (Fin n) F)))
    {I : Finset (Fin n)} {j : Fin n} (hj : j ∉ I)
    (hP : perfectCore (centralizer (S : Set (SpecialLinearGroup (Fin n) F))) ≤
      blockSpecialLinear I) :
    Nat.card (perfectCore (Φ.range ⊓ centralizer ((S.map Φ : Subgroup G) : Set G))) =
      Nat.card (perfectCore (centralizer (S : Set (SpecialLinearGroup (Fin n) F)))) :=
  natCard_perfectCore_range_inf_centralizer_map Φ hker hrig
    (inf_center_eq_bot_of_le_blockSpecialLinear hj hP)

end Orders

section Linear6Orders

variable {F : Type} [Field F] [Finite F]

omit [Finite F] in
theorem rigid_lin6 [DecidableEq F] {S : Subgroup (SpecialLinearGroup (Fin 6) F)} {A : Subgroup Fˣ}
    (hS : S = linTorusA (lin6Torus F) A ∨ S = linTorusM2 (lin6Torus F) A ∨
      S = linTorusM3 (lin6Torus F) A) {a₀ : Fˣ} (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1)
    (x : SpecialLinearGroup (Fin 6) F)
    (hx : ∀ s ∈ S, ⁅x, s⁆ ∈ center (SpecialLinearGroup (Fin 6) F)) :
    x ∈ centralizer (S : Set (SpecialLinearGroup (Fin 6) F)) := by
  have hs₀ : lin6Torus F ![a₀, 1, 1] ∈ S := by
    rcases hS with rfl | rfl | rfl
    · exact mem_linTorusA _ ha₀
    · exact mem_linTorusM2 _ ha₀ (one_mem A)
    · exact mem_linTorusM3 _ ha₀ (one_mem A)
  have hdiag : ∀ d ∈ S, ∀ i j, i ≠ j → (d : Matrix (Fin 6) (Fin 6) F) i j = 0 := by
    rcases hS with rfl | rfl | rfl <;> exact fun d hd => offDiag_of_mem_map_diagTorusSL hd
  exact rigid_of_isDiagOf hdiag hs₀ (injective_sepValues hsq) (isDiagOf_lin6Torus_A a₀) 2
    (by decide) 0 (by decide) x hx

theorem pieceCards_lin6Tori (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A)
    (hsq : a₀ ^ 2 ≠ 1) :
    pieceCards ⊤ (linTorusA (lin6Torus F) A) (linTorusM2 (lin6Torus F) A)
      (linTorusM3 (lin6Torus F) A) = pieceOrders .linear6 (Nat.card F) := by
  rw [pieceCards_top, perfectCore_centralizer_lin6TorusA hF ha₀ hsq,
    perfectCore_centralizer_lin6TorusM2 hF ha₀ hsq, perfectCore_centralizer_lin6TorusM3 hF ha₀ hsq,
    natCard_blockSpecialLinear (by decide), natCard_blockSpecialLinear (by decide),
    natCard_sup_blockSpecialLinear_two_two (by decide) (by decide) (by decide)]
  rfl

theorem pieceCards_range_lin6 {G : Type*} [Group G] [Finite G]
    (Φ : SpecialLinearGroup (Fin 6) F →* G) (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin 6) F))
    (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    pieceCards Φ.range ((linTorusA (lin6Torus F) A).map Φ) ((linTorusM2 (lin6Torus F) A).map Φ)
      ((linTorusM3 (lin6Torus F) A).map Φ) = pieceOrders .linear6 (Nat.card F) := by
  classical
  rw [← pieceCards_lin6Tori hF ha₀ hsq, pieceCards_top, pieceCards,
    natCard_piece_range_of_rigid Φ hker (rigid_lin6 (.inl rfl) ha₀ hsq) (j := 0) (by decide)
      (perfectCore_centralizer_lin6TorusA hF ha₀ hsq).le,
    natCard_piece_range_of_rigid Φ hker (rigid_lin6 (.inr (.inl rfl)) ha₀ hsq) (j := 0)
      (by decide) (perfectCore_centralizer_lin6TorusM2 hF ha₀ hsq).le,
    natCard_piece_range_of_rigid Φ hker (rigid_lin6 (.inr (.inr rfl)) ha₀ hsq) (I := {1, 2, 4, 5})
      (j := 0) (by decide)
      ((perfectCore_centralizer_lin6TorusM3 hF ha₀ hsq).le.trans
        (sup_le (blockSpecialLinear_mono (by decide)) (blockSpecialLinear_mono (by decide))))]

end Linear6Orders


section Linear7

variable {F : Type} [Field F]

theorem lin7Torus_apply_self (t : Fin 3 → Fˣ) (i : Fin 7) :
    ((lin7Torus F t : SpecialLinearGroup (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) i i =
      ((![t 0, t 1, t 2, (t 0)⁻¹, (t 1)⁻¹, (t 2)⁻¹, 1] : Fin 7 → Fˣ) i : F) :=
  diagTorusSL_apply_self _ _ t i

theorem isDiagOf_lin7Torus_A (a₀ : Fˣ) :
    IsDiagOf (lin7Torus F ![a₀, 1, 1]) (sepValues a₀) ![0, 2, 2, 1, 2, 2, 2] where
  offDiag i j hij := diagTorusSL_apply_ne _ _ _ hij
  diag i := by
    rw [lin7Torus_apply_self]
    fin_cases i <;> simp [sepValues]

theorem isDiagOf_lin7Torus_B (a₀ : Fˣ) :
    IsDiagOf (lin7Torus F ![1, a₀, 1]) (sepValues a₀) ![2, 0, 2, 2, 1, 2, 2] where
  offDiag i j hij := diagTorusSL_apply_ne _ _ _ hij
  diag i := by
    rw [lin7Torus_apply_self]
    fin_cases i <;> simp [sepValues]

theorem isDiagOf_lin7Torus_C (a₀ : Fˣ) :
    IsDiagOf (lin7Torus F ![1, a₀, a₀]) (sepValues a₀) ![2, 0, 0, 2, 1, 1, 2] where
  offDiag i j hij := diagTorusSL_apply_ne _ _ _ hij
  diag i := by
    rw [lin7Torus_apply_self]
    fin_cases i <;> simp [sepValues]

@[expose] def lin7BlockA : Finset (Fin 7) := {1, 2, 4, 5, 6}

@[expose] def lin7BlockM2 : Finset (Fin 7) := {2, 5, 6}

variable [Finite F]

theorem perfectCore_centralizer_lin7TorusA (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (linTorusA (lin7Torus F) A : Set (SpecialLinearGroup (Fin 7) F))) =
      blockSpecialLinear (K := F) lin7BlockA := by
  have hv := injective_sepValues (F := F) hsq
  have key : ∀ i j : Fin 7, i ≠ j → (i ∉ lin7BlockA ∨ j ∉ lin7BlockA) →
      (![0, 2, 2, 1, 2, 2, 2] : Fin 7 → Fin 3) i ≠ ![0, 2, 2, 1, 2, 2, 2] j := by decide
  have h := CFSG.SeitzReduction.LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear
    (N := Finset.univ) (Finset.subset_univ lin7BlockA)
    (linTorusA (lin7Torus F) A : Set (SpecialLinearGroup (Fin 7) F))
    (fun d hd => offDiag_of_mem_map_diagTorusSL hd)
    (by
      rintro _ ⟨a, -, rfl⟩ i hi j hj
      rw [MonoidHom.comp_apply, sp6ParamA_apply, lin7Torus_apply_self, lin7Torus_apply_self]
      simp only [lin7BlockA, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl | rfl | rfl <;>
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> simp)
    (fun i _ j _ hij hIJ => exists_mem_ne_of_isDiagOf (mem_linTorusA _ ha₀)
      (mem_linTorusA _ ha₀) hv (isDiagOf_lin7Torus_A a₀) (isDiagOf_lin7Torus_A a₀)
      (Or.inl (key i j hij hIJ)))
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
      (by decide) hF)
  rwa [CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_univ, top_inf_eq] at h

theorem perfectCore_centralizer_lin7TorusM2 (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (linTorusM2 (lin7Torus F) A : Set (SpecialLinearGroup (Fin 7) F))) =
      blockSpecialLinear (K := F) lin7BlockM2 := by
  have hv := injective_sepValues (F := F) hsq
  have key : ∀ i j : Fin 7, i ≠ j → (i ∉ lin7BlockM2 ∨ j ∉ lin7BlockM2) →
      (![0, 2, 2, 1, 2, 2, 2] : Fin 7 → Fin 3) i ≠ ![0, 2, 2, 1, 2, 2, 2] j ∨
        (![2, 0, 2, 2, 1, 2, 2] : Fin 7 → Fin 3) i ≠ ![2, 0, 2, 2, 1, 2, 2] j := by decide
  have h := CFSG.SeitzReduction.LinearPilot.perfectCore_inf_centralizer_eq_blockSpecialLinear
    (N := Finset.univ) (Finset.subset_univ lin7BlockM2)
    (linTorusM2 (lin7Torus F) A : Set (SpecialLinearGroup (Fin 7) F))
    (fun d hd => offDiag_of_mem_map_diagTorusSL hd)
    (by
      rintro _ ⟨p, -, rfl⟩ i hi j hj
      rw [MonoidHom.comp_apply, sp6ParamM2_apply, lin7Torus_apply_self, lin7Torus_apply_self]
      simp only [lin7BlockM2, Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> simp)
    (fun i _ j _ hij hIJ => exists_mem_ne_of_isDiagOf (mem_linTorusM2 _ ha₀ (one_mem A))
      (mem_linTorusM2 _ (one_mem A) ha₀) hv (isDiagOf_lin7Torus_A a₀) (isDiagOf_lin7Torus_B a₀)
      (key i j hij hIJ))
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le
      (by decide) hF)
  rwa [CFSG.SeitzReduction.LinearPilot.blockSpecialLinear_univ, top_inf_eq] at h

theorem perfectCore_centralizer_lin7TorusM3 (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ}
    (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    perfectCore (centralizer (linTorusM3 (lin7Torus F) A : Set (SpecialLinearGroup (Fin 7) F))) =
      blockSpecialLinear (K := F) (linBlockE 7) ⊔ blockSpecialLinear (linBlockF 7) := by
  have hv := injective_sepValues (F := F) hsq
  have key : ∀ i j : Fin 7, i ≠ j → ¬ (i ∈ linBlockE 7 ∧ j ∈ linBlockE 7) →
      ¬ (i ∈ linBlockF 7 ∧ j ∈ linBlockF 7) →
      (![0, 2, 2, 1, 2, 2, 2] : Fin 7 → Fin 3) i ≠ ![0, 2, 2, 1, 2, 2, 2] j ∨
        (![2, 0, 0, 2, 1, 1, 2] : Fin 7 → Fin 3) i ≠ ![2, 0, 0, 2, 1, 1, 2] j := by decide
  have hconst : ∀ (B : Finset (Fin 7)), (B = linBlockE 7 ∨ B = linBlockF 7) →
      ∀ d ∈ (linTorusM3 (lin7Torus F) A : Set (SpecialLinearGroup (Fin 7) F)), ∀ i ∈ B, ∀ j ∈ B,
        (d : Matrix (Fin 7) (Fin 7) F) i i = (d : Matrix (Fin 7) (Fin 7) F) j j := by
    rintro B hB _ ⟨p, -, rfl⟩ i hi j hj
    rw [MonoidHom.comp_apply, sp6ParamM3_apply, lin7Torus_apply_self, lin7Torus_apply_self]
    rcases hB with rfl | rfl <;>
      simp only [linBlockE, linBlockF, Finset.mem_insert, Finset.mem_singleton] at hi hj <;>
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp
  exact perfectCore_centralizer_eq_sup_of_two_blocks (by decide) _
    (fun d hd => offDiag_of_mem_map_diagTorusSL hd) (hconst _ (.inl rfl)) (hconst _ (.inr rfl))
    (fun i j hij h₁ h₂ => exists_mem_ne_of_isDiagOf (mem_linTorusM3 _ ha₀ (one_mem A))
      (mem_linTorusM3 _ (one_mem A) ha₀) hv (isDiagOf_lin7Torus_A a₀) (isDiagOf_lin7Torus_C a₀)
      (key i j hij h₁ h₂))
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)
    (CFSG.SeitzReduction.LinearPilot.commutator_blockSpecialLinear_eq_of_two_le (by decide) hF)

omit [Finite F] in
theorem rigid_lin7 [DecidableEq F] {S : Subgroup (SpecialLinearGroup (Fin 7) F)} {A : Subgroup Fˣ}
    (hS : S = linTorusA (lin7Torus F) A ∨ S = linTorusM2 (lin7Torus F) A ∨
      S = linTorusM3 (lin7Torus F) A) {a₀ : Fˣ} (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1)
    (x : SpecialLinearGroup (Fin 7) F)
    (hx : ∀ s ∈ S, ⁅x, s⁆ ∈ center (SpecialLinearGroup (Fin 7) F)) :
    x ∈ centralizer (S : Set (SpecialLinearGroup (Fin 7) F)) := by
  have hs₀ : lin7Torus F ![a₀, 1, 1] ∈ S := by
    rcases hS with rfl | rfl | rfl
    · exact mem_linTorusA _ ha₀
    · exact mem_linTorusM2 _ ha₀ (one_mem A)
    · exact mem_linTorusM3 _ ha₀ (one_mem A)
  have hdiag : ∀ d ∈ S, ∀ i j, i ≠ j → (d : Matrix (Fin 7) (Fin 7) F) i j = 0 := by
    rcases hS with rfl | rfl | rfl <;> exact fun d hd => offDiag_of_mem_map_diagTorusSL hd
  exact rigid_of_isDiagOf hdiag hs₀ (injective_sepValues hsq) (isDiagOf_lin7Torus_A a₀) 2
    (by decide) 0 (by decide) x hx

theorem pieceCards_lin7Tori (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A)
    (hsq : a₀ ^ 2 ≠ 1) :
    pieceCards ⊤ (linTorusA (lin7Torus F) A) (linTorusM2 (lin7Torus F) A)
      (linTorusM3 (lin7Torus F) A) = pieceOrders .linear7 (Nat.card F) := by
  rw [pieceCards_top, perfectCore_centralizer_lin7TorusA hF ha₀ hsq,
    perfectCore_centralizer_lin7TorusM2 hF ha₀ hsq, perfectCore_centralizer_lin7TorusM3 hF ha₀ hsq,
    natCard_blockSpecialLinear (by decide), natCard_blockSpecialLinear (by decide),
    natCard_sup_blockSpecialLinear_two_two (by decide) (by decide) (by decide)]
  rfl

theorem pieceCards_range_lin7 {G : Type*} [Group G] [Finite G]
    (Φ : SpecialLinearGroup (Fin 7) F →* G) (hker : Φ.ker ≤ center (SpecialLinearGroup (Fin 7) F))
    (hF : 4 ≤ Nat.card F) {A : Subgroup Fˣ} {a₀ : Fˣ} (ha₀ : a₀ ∈ A) (hsq : a₀ ^ 2 ≠ 1) :
    pieceCards Φ.range ((linTorusA (lin7Torus F) A).map Φ) ((linTorusM2 (lin7Torus F) A).map Φ)
      ((linTorusM3 (lin7Torus F) A).map Φ) = pieceOrders .linear7 (Nat.card F) := by
  classical
  rw [← pieceCards_lin7Tori hF ha₀ hsq, pieceCards_top, pieceCards,
    natCard_piece_range_of_rigid Φ hker (rigid_lin7 (.inl rfl) ha₀ hsq) (j := 0) (by decide)
      (perfectCore_centralizer_lin7TorusA hF ha₀ hsq).le,
    natCard_piece_range_of_rigid Φ hker (rigid_lin7 (.inr (.inl rfl)) ha₀ hsq) (j := 0)
      (by decide) (perfectCore_centralizer_lin7TorusM2 hF ha₀ hsq).le,
    natCard_piece_range_of_rigid Φ hker (rigid_lin7 (.inr (.inr rfl)) ha₀ hsq) (I := {1, 2, 4, 5})
      (j := 0) (by decide)
      ((perfectCore_centralizer_lin7TorusM3 hF ha₀ hsq).le.trans
        (sup_le (blockSpecialLinear_mono (by decide)) (blockSpecialLinear_mono (by decide))))]

end Linear7

end CFSG.SeitzReduction.F4Pilot
