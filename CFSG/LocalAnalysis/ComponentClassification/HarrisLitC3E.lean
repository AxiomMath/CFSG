module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FieldSq

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.C3

open CFSG Subgroup Matrix

section SL2

variable {E : Type*} [Field E]

@[expose] def unipU (x : E) : SpecialLinearGroup (Fin 2) E :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def unipL (x : E) : SpecialLinearGroup (Fin 2) E :=
  ⟨!![1, 0; x, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_unipU (x : E) :
    ((unipU x : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = !![1, x; 0, 1] := rfl

@[simp] theorem coe_unipL (x : E) :
    ((unipL x : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) = !![1, 0; x, 1] := rfl

theorem trace_conj (a b : SpecialLinearGroup (Fin 2) E) :
    ((a * b * a⁻¹ : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E).trace =
      (b : Matrix (Fin 2) (Fin 2) E).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_cycle,
    ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mul]

theorem comm_of_conj_unip (h2 : (2 : E) ≠ 0) {a u : SpecialLinearGroup (Fin 2) E}
    (hu : (u : Matrix (Fin 2) (Fin 2) E).trace = 2)
    (h : ∃ s : E, (s = 1 ∨ s = -1) ∧
      ((a * u * a⁻¹ : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
        s • (u : Matrix (Fin 2) (Fin 2) E)) :
    (a : Matrix (Fin 2) (Fin 2) E) * u = u * a := by
  obtain ⟨s, hs, hsu⟩ := h
  have hs1 : s = 1 := by
    have h1 := trace_conj a u
    rw [hsu, Matrix.trace_smul, hu, smul_eq_mul] at h1
    rcases hs with rfl | rfl
    · rfl
    · exfalso
      have h4 : (2 : E) * 2 = 0 := by linear_combination -h1
      exact h2 (mul_self_eq_zero.mp h4)
  rw [hs1, one_smul] at hsu
  have h1 : (a * u : SpecialLinearGroup (Fin 2) E) = u * a := by
    have := congrArg (· * a) (Subtype.ext hsu : a * u * a⁻¹ = u)
    simpa using this
  have := congrArg Subtype.val h1
  simpa using this

theorem trace_unipU (x : E) : ((unipU x : SpecialLinearGroup (Fin 2) E) :
    Matrix (Fin 2) (Fin 2) E).trace = 2 := by
  simp [unipU, Matrix.trace_fin_two]
  norm_num

theorem trace_unipL (x : E) : ((unipL x : SpecialLinearGroup (Fin 2) E) :
    Matrix (Fin 2) (Fin 2) E).trace = 2 := by
  simp [unipL, Matrix.trace_fin_two]
  norm_num

theorem eq_one_or_neg_of_conj_unip (h2 : (2 : E) ≠ 0) {a : SpecialLinearGroup (Fin 2) E}
    (hU : ∃ s : E, (s = 1 ∨ s = -1) ∧
      ((a * unipU 1 * a⁻¹ : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
        s • ((unipU 1 : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E))
    (hL : ∃ s : E, (s = 1 ∨ s = -1) ∧
      ((a * unipL 1 * a⁻¹ : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
        s • ((unipL 1 : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E)) :
    a = 1 ∨ a = -1 := by
  have hcU := comm_of_conj_unip h2 (trace_unipU 1) hU
  have hcL := comm_of_conj_unip h2 (trace_unipL 1) hL
  set M : Matrix (Fin 2) (Fin 2) E := (a : Matrix (Fin 2) (Fin 2) E) with hM
  have e1 := congrFun (congrFun hcU 0) 0
  have e2 := congrFun (congrFun hcU 0) 1
  have e3 := congrFun (congrFun hcL 0) 0
  simp [unipU, unipL, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  have hM10 : M 1 0 = 0 := by linear_combination e1
  have hM01 : M 0 1 = 0 := by linear_combination e3
  have hM11 : M 1 1 = M 0 0 := by linear_combination -e2
  have hdet := a.2
  rw [← hM, Matrix.det_fin_two, hM10, hM01, hM11] at hdet
  have hsq : M 0 0 * M 0 0 = 1 := by linear_combination hdet
  rcases mul_self_eq_one_iff.mp hsq with h | h
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hM, h, hM10, hM01, hM11]
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hM, h, hM10, hM01, hM11]

end SL2

variable {E : Type*} [Field E] {A : Type} [Group A] (π : SpecialLinearGroup (Fin 2) E →* A)

theorem exists_smul_of_eq (hker : ∀ g, π g = 1 ↔ g = 1 ∨ g = -1)
    {a b : SpecialLinearGroup (Fin 2) E} (h : π a = π b) :
    ∃ s : E, (s = 1 ∨ s = -1) ∧
      (a : Matrix (Fin 2) (Fin 2) E) = s • (b : Matrix (Fin 2) (Fin 2) E) := by
  have h1 : π (a * b⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  rcases (hker _).mp h1 with h3 | h3
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [one_smul, mul_inv_eq_one.mp h3]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    have h4 : a = -1 * b := by rw [← h3, inv_mul_cancel_right]
    rw [h4, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one, neg_one_smul, Matrix.neg_mul, Matrix.one_mul]

theorem conj_smul_of_comm (hker : ∀ g, π g = 1 ↔ g = 1 ∨ g = -1)
    {g u : SpecialLinearGroup (Fin 2) E} (h : π g * π u = π u * π g) :
    ∃ s : E, (s = 1 ∨ s = -1) ∧
      ((g * u * g⁻¹ : SpecialLinearGroup (Fin 2) E) : Matrix (Fin 2) (Fin 2) E) =
        s • (u : Matrix (Fin 2) (Fin 2) E) :=
  exists_smul_of_eq π hker (by rw [map_mul, map_mul, map_inv, h, mul_inv_cancel_right])

variable {σ : E →+* E} {c : A}

theorem map_unip_one :
    SpecialLinearGroup.map σ (unipU 1) = unipU 1 ∧ SpecialLinearGroup.map σ (unipL 1) = unipL 1 :=
  ⟨Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [unipU]),
    Subtype.ext (by
      rw [Matrix.SpecialLinearGroup.map_apply_coe]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [unipL])⟩

theorem mem_normalizer_range (hcc : c * c = 1)
    (hcσ : ∀ g, c * π g * c = π (SpecialLinearGroup.map σ g)) :
    c ∈ normalizer (π.range : Set A) := by
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  rw [mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨SpecialLinearGroup.map σ g, by rw [← hcσ g, hcinv]⟩
  · rintro ⟨g, hg⟩
    refine ⟨SpecialLinearGroup.map σ g, ?_⟩
    rw [← hcσ g, hg, hcinv]
    calc c * (c * y * c) * c = (c * c) * y * (c * c) := by group
      _ = y := by rw [hcc, one_mul, mul_one]

theorem comm_of_fixed (hcc : c * c = 1) (hcσ : ∀ g, c * π g * c = π (SpecialLinearGroup.map σ g))
    {u : SpecialLinearGroup (Fin 2) E} (hu : SpecialLinearGroup.map σ u = u) :
    c * π u = π u * c := by
  have h := hcσ u
  rw [hu] at h
  calc c * π u = c * π u * c * c := by rw [mul_assoc (c * π u), hcc, mul_one]
    _ = π u * c := by rw [h]

theorem center_sup_eq_bot (h2 : (2 : E) ≠ 0) (hker : ∀ g, π g = 1 ↔ g = 1 ∨ g = -1)
    (hcc : c * c = 1) (hcσ : ∀ g, c * π g * c = π (SpecialLinearGroup.map σ g))
    (hcπ : c ∉ π.range) {t₀ : E} (ht₀ : σ t₀ ≠ t₀) : center ↥(π.range ⊔ zpowers c) = ⊥ := by
  have hc1 : c ≠ 1 := fun h => hcπ (h ▸ one_mem _)
  have hco : orderOf c = 2 := orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1
  have htriv : ∀ g, π g * π (unipU 1) = π (unipU 1) * π g →
      π g * π (unipL 1) = π (unipL 1) * π g → π g = 1 := fun g h₁ h₂ =>
    (hker g).mpr (eq_one_or_neg_of_conj_unip h2 (conj_smul_of_comm π hker h₁)
      (conj_smul_of_comm π hker h₂))
  rw [eq_bot_iff]
  rintro ⟨β, hβ⟩ hβc
  rw [mem_bot]
  have hβc' : ∀ y ∈ π.range ⊔ zpowers c, y * β = β * y := fun y hy => by
    have h := mem_center_iff.mp hβc ⟨y, hy⟩
    exact congrArg Subtype.val h
  have hN : zpowers c ≤ normalizer (π.range : Set A) :=
    zpowers_le.mpr (mem_normalizer_range π hcc hcσ)
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers c) π.range hN
  have hβ' : β ∈ ((zpowers c ⊔ π.range : Subgroup A) : Set A) := by
    rw [sup_comm]
    exact hβ
  rw [hset] at hβ'
  obtain ⟨ci, hci, _, ⟨g, rfl⟩, hβeq⟩ := hβ'
  simp only at hβeq
  have hci' : ci = 1 ∨ ci = c := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hci
    rw [← zpow_mod_orderOf, hco]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [Nat.cast_ofNat, h, zpow_zero]
    · right
      rw [Nat.cast_ofNat, h, zpow_one]
  obtain ⟨hσU, hσL⟩ := map_unip_one (σ := σ)
  have hg : ∀ u, SpecialLinearGroup.map σ u = u → π g * π u = π u * π g := by
    intro u hu
    have h1 := hβc' (π u) (mem_sup_left ⟨u, rfl⟩)
    rw [← hβeq] at h1
    rcases hci' with rfl | rfl
    · simp only [one_mul] at h1
      exact h1.symm
    · have hcu := comm_of_fixed π hcc hcσ hu
      have h3 : ci * (π g * π u) = ci * (π u * π g) := by
        calc ci * (π g * π u) = ci * π g * π u := by group
          _ = π u * (ci * π g) := h1.symm
          _ = ci * π u * π g := by rw [← mul_assoc, ← hcu]
          _ = ci * (π u * π g) := by group
      exact mul_left_cancel h3
  have hg1 := htriv g (hg _ hσU) (hg _ hσL)
  apply Subtype.ext
  change β = 1
  rw [← hβeq, hg1, mul_one]
  rcases hci' with rfl | rfl
  · rfl
  · exfalso
    have h1 := hβc' (π (unipU t₀)) (mem_sup_left ⟨_, rfl⟩)
    rw [← hβeq, hg1, mul_one] at h1
    have h3 : π (SpecialLinearGroup.map σ (unipU t₀)) = π (unipU t₀) := by
      rw [← hcσ, ← h1, mul_assoc, hcc, mul_one]
    obtain ⟨s, -, hs⟩ := exists_smul_of_eq π hker h3
    rw [Matrix.SpecialLinearGroup.map_apply_coe, coe_unipU] at hs
    have e00 := congrFun (congrFun hs 0) 0
    have e01 := congrFun (congrFun hs 0) 1
    simp at e00 e01
    rw [← e00, one_mul] at e01
    exact ht₀ e01

theorem exists_eight_le_sup [Finite A] (h2 : (2 : E) ≠ 0)
    (hker : ∀ g, π g = 1 ↔ g = 1 ∨ g = -1) (hcc : c * c = 1)
    (hcσ : ∀ g, c * π g * c = π (SpecialLinearGroup.map σ g)) (hcπ : c ∉ π.range)
    {a b : E} (hab : a ^ 2 + b ^ 2 = -1) (hσa : σ a = a) (hσb : σ b = b) :
    ∃ A₈ : Subgroup A, A₈ ≤ π.range ⊔ zpowers c ∧ GrSLit.IsElemTwo A₈ ∧ Nat.card A₈ = 8 := by
  set j : SpecialLinearGroup (Fin 2) E := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩ with hj
  set d : SpecialLinearGroup (Fin 2) E := ⟨!![a, b; b, -a], by
    rw [Matrix.det_fin_two_of]
    linear_combination -hab⟩ with hd
  have hjj : j * j = -1 := by
    apply Subtype.ext
    change !![(0 : E), 1; -1, 0] * !![(0 : E), 1; -1, 0] = -1
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdd : d * d = -1 := by
    apply Subtype.ext
    change !![a, b; b, -a] * !![a, b; b, -a] = -1
    ext i k
    fin_cases i <;> fin_cases k <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
      first | ring1 | linear_combination hab
  have hjd : j * d = -1 * (d * j) := by
    apply Subtype.ext
    change !![(0 : E), 1; -1, 0] * !![a, b; b, -a] = -1 * (!![a, b; b, -a] * !![(0 : E), 1; -1, 0])
    ext i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hπneg : π (-1) = 1 := (hker _).mpr (Or.inr rfl)
  have hfixj : SpecialLinearGroup.map σ j = j := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hj])
  have hfixd : SpecialLinearGroup.map σ d = d := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [hd, hσa, hσb])
  have hne : ∀ g : SpecialLinearGroup (Fin 2) E, π g = 1 →
      (g : Matrix (Fin 2) (Fin 2) E) 0 1 = 0 ∧
        (g : Matrix (Fin 2) (Fin 2) E) 0 0 = (g : Matrix (Fin 2) (Fin 2) E) 1 1 := by
    intro g hg
    rcases (hker g).mp hg with rfl | rfl <;> simp
  refine ⟨zpowers (π j) ⊔ zpowers (π d) ⊔ zpowers c, ?_, ?_⟩
  · refine sup_le (sup_le ?_ ?_) le_sup_right
    · exact (zpowers_le.mpr (⟨j, rfl⟩ : π j ∈ π.range)).trans le_sup_left
    · exact (zpowers_le.mpr (⟨d, rfl⟩ : π d ∈ π.range)).trans le_sup_left
  have h1 : π j * π j = 1 := by rw [← map_mul, hjj, hπneg]
  have h2' : π d * π d = 1 := by rw [← map_mul, hdd, hπneg]
  have hj1 : π j ≠ 1 := fun h => by
    have := (hne j h).1
    simp [hj] at this
  have hd1 : π d ≠ 1 := fun h => by
    obtain ⟨hb0, haa⟩ := hne d h
    simp [hd] at hb0 haa
    have ha0 : a = 0 := by
      have h3 : (2 : E) * a = 0 := by linear_combination haa
      exact (mul_eq_zero.mp h3).resolve_left h2
    rw [ha0, hb0] at hab
    have h4 : (1 : E) = 0 := by linear_combination hab
    exact one_ne_zero h4
  have hjd1 : π d ≠ π j := fun h => by
    obtain ⟨s, -, hs⟩ := exists_smul_of_eq π hker h.symm
    have e01 := congrFun (congrFun hs 0) 1
    have e10 := congrFun (congrFun hs 1) 0
    simp [hj, hd] at e01 e10
    apply h2
    linear_combination e01 - e10
  have hcomm : π j * π d = π d * π j := by
    rw [← map_mul, ← map_mul, hjd, map_mul, hπneg, one_mul]
  have hcj : π j * c = c * π j := (comm_of_fixed π hcc hcσ hfixj).symm
  have hcd : π d * c = c * π d := (comm_of_fixed π hcc hcσ hfixd).symm
  have hcw : c ∉ zpowers (π j) ⊔ zpowers (π d) := fun h => hcπ
    (sup_le (zpowers_le.mpr (⟨j, rfl⟩ : π j ∈ π.range))
      (zpowers_le.mpr (⟨d, rfl⟩ : π d ∈ π.range)) h)
  obtain ⟨hE, hcard⟩ := GrSLit.GrS4.isElemTwo_eight_of_commuting h1 h2' hcc hj1 hd1 hjd1 hcomm
    hcj hcd hcw
  exact ⟨hE, by rw [hcard]; norm_num⟩

end CFSG.ComponentClassification.HarrisLit.C3
