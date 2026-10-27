module

public import CFSG.LocalAnalysis.ComponentClassification.AS81AutRad

public noncomputable section

namespace CFSG.ComponentClassification.AS81.Sec2Aut

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial LinearFlag FieldFourCover
open CFSG.ComponentClassification.RankTwoL3Even CFSG.LieType.Chevalley

variable {F : Type} [Field F]

theorem fieldAut_proj_unipU_zero (σ : F ≃+* F) (a c : F) :
    fieldAut 3 F σ (proj 3 F (unipU F a 0 c)) = proj 3 F (unipU F (σ a) 0 (σ c)) := by
  rw [fieldAut_proj_unipU, map_zero]

theorem fieldAut_proj_unipU_transpose (σ : F ≃+* F) (a c : F) :
    fieldAut 3 F σ (proj 3 F (unipU F a 0 c).transpose) =
      proj 3 F (unipU F (σ a) 0 (σ c)).transpose := by
  rw [fieldAut_proj]
  congr 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    SpecialLinearGroup.coe_transpose, SpecialLinearGroup.coe_transpose, coe_unipU, coe_unipU]
  fin_cases i <;> fin_cases j <;> simp

theorem mul_unipU_zero_transpose_apply (M : Matrix (Fin 3) (Fin 3) F) (a c : F) (i j : Fin 3) :
    (M * ((unipU F a 0 c).transpose : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 0 then a * M i 1 + c * M i 2 else 0 := by
  rw [SpecialLinearGroup.coe_transpose, coe_unipU]
  fin_cases i <;> fin_cases j <;>
    (simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply]; try ring)

theorem unipU_zero_mul_apply' (M : Matrix (Fin 3) (Fin 3) F) (a c : F) (i j : Fin 3) :
    ((unipU F a 0 c : Matrix (Fin 3) (Fin 3) F) * M) i j =
      M i j + if i = 0 then a * M 1 j + c * M 2 j else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem mul_unipU_zero_apply' (M : Matrix (Fin 3) (Fin 3) F) (a c : F) (i j : Fin 3) :
    (M * (unipU F a 0 c : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + (if j = 1 then a * M i 0 else 0) + if j = 2 then c * M i 0 else 0 := by
  rw [coe_unipU]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

variable [CharP F 2]

theorem dualAut_proj_unipU_zero (a c : F) :
    dualAut 3 F (proj 3 F (unipU F a 0 c)) = proj 3 F (unipU F a 0 c).transpose := by
  rw [dualAut_proj, unipU_inv]
  simp only [CharTwo.neg_eq, mul_zero, add_zero]

theorem not_mapsTo_projRad_zero_of_dual (A : GL (Fin 3) F) (σ : F ≃+* F)
    (h1 : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (unipU F 1 0 0)) ∈
      projRad F 0)
    (h2 : (conjAut 3 F A * fieldAut 3 F σ * dualAut 3 F) (proj 3 F (unipU F 0 0 1)) ∈
      projRad F 0) : False := by
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  obtain ⟨a₁, c₁, h₁⟩ := mem_projRad_zero.1 h1
  obtain ⟨a₂, c₂, h₂⟩ := mem_projRad_zero.1 h2
  simp only [MulAut.mul_apply, dualAut_proj_unipU_zero, fieldAut_proj_unipU_transpose,
    map_one, map_zero] at h₁ h₂
  have key₁ := mul_eq_mul_of_conjAut_proj_eq
    (by rw [trace_unipU_transpose, trace_unipU, trace_unipU]) (trace_unipU_ne_zero _ _ _) h₁.symm
  have key₂ := mul_eq_mul_of_conjAut_proj_eq
    (by rw [trace_unipU_transpose, trace_unipU, trace_unipU]) (trace_unipU_ne_zero _ _ _) h₂.symm
  have e₁ : ∀ i j : Fin 3, M i j + (if j = 0 then 1 * M i 1 + 0 * M i 2 else 0) =
      M i j + if i = 0 then a₁ * M 1 j + c₁ * M 2 j else 0 := by
    intro i j
    have := congrFun (congrFun key₁ i) j
    rwa [mul_unipU_zero_transpose_apply, unipU_zero_mul_apply'] at this
  have e₂ : ∀ i j : Fin 3, M i j + (if j = 0 then 0 * M i 1 + 1 * M i 2 else 0) =
      M i j + if i = 0 then a₂ * M 1 j + c₂ * M 2 j else 0 := by
    intro i j
    have := congrFun (congrFun key₂ i) j
    rwa [mul_unipU_zero_transpose_apply, unipU_zero_mul_apply'] at this
  have h11 : M 1 1 = 0 := by have := e₁ 1 0; simp at this; exact this
  have h21 : M 2 1 = 0 := by have := e₁ 2 0; simp at this; exact this
  have h12 : M 1 2 = 0 := by have := e₂ 1 0; simp at this; exact this
  have h22 : M 2 2 = 0 := by have := e₂ 2 0; simp at this; exact this
  apply hdet
  rw [Matrix.det_fin_three, h11, h21, h12, h22]
  ring

theorem mapsTo_projRad_zero_eq (A : GL (Fin 3) F) (σ : F ≃+* F)
    (h : ∀ x ∈ projRad F 0, (conjAut 3 F A * fieldAut 3 F σ) x ∈ projRad F 0) :
    (A : Matrix (Fin 3) (Fin 3) F) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
      ∀ a c a' c' : F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (unipU F a 0 c)) =
        proj 3 F (unipU F a' 0 c') ↔
        (σ a * (A : Matrix (Fin 3) (Fin 3) F) 0 0 =
            a' * (A : Matrix (Fin 3) (Fin 3) F) 1 1 + c' * (A : Matrix (Fin 3) (Fin 3) F) 2 1 ∧
          σ c * (A : Matrix (Fin 3) (Fin 3) F) 0 0 =
            a' * (A : Matrix (Fin 3) (Fin 3) F) 1 2 + c' * (A : Matrix (Fin 3) (Fin 3) F) 2 2) := by
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have hrel : ∀ a c a' c' : F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (unipU F a 0 c)) =
      proj 3 F (unipU F a' 0 c') ↔ ∀ i j : Fin 3,
        M i j + (if j = 1 then σ a * M i 0 else 0) + (if j = 2 then σ c * M i 0 else 0) =
        M i j + if i = 0 then a' * M 1 j + c' * M 2 j else 0 := by
    intro a c a' c'
    simp only [MulAut.mul_apply, fieldAut_proj_unipU_zero]
    constructor
    · intro h' i j
      have key := mul_eq_mul_of_conjAut_proj_eq (by rw [trace_unipU, trace_unipU])
        (trace_unipU_ne_zero _ _ _) h'
      have := congrFun (congrFun key i) j
      rwa [mul_unipU_zero_apply', unipU_zero_mul_apply'] at this
    · intro he
      rw [conjAut_proj]
      congr 1
      have hA : M * (unipU F (σ a) 0 (σ c) : Matrix (Fin 3) (Fin 3) F) =
          (unipU F a' 0 c' : Matrix (Fin 3) (Fin 3) F) * M := by
        ext i j
        rw [mul_unipU_zero_apply', unipU_zero_mul_apply']
        exact he i j
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [coe_slConjugation, hA, Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul,
        mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one]
  obtain ⟨a₁, c₁, h₁⟩ := mem_projRad_zero.1 (h _ (mem_projRad_zero.2 ⟨1, 0, rfl⟩))
  have e := (hrel 1 0 a₁ c₁).1 h₁.symm
  have h10 : M 1 0 = 0 := by have := e 1 1; simpa using this
  have h20 : M 2 0 = 0 := by have := e 2 1; simpa using this
  refine ⟨h10, h20, fun a c a' c' => ?_⟩
  rw [hrel]
  constructor
  · intro he
    have e01 := he 0 1
    have e02 := he 0 2
    simp at e01 e02
    exact ⟨e01, e02⟩
  · rintro ⟨e01, e02⟩ i j
    fin_cases i <;> fin_cases j <;> simp [h10, h20, e01, e02]


variable [Finite F]

omit [CharP F 2] in
theorem forall_of_two_mul_card_lt {Q : F → Prop}
    (hsub : ∀ a b, Q a → Q b → Q (a - b))
    (hcard : Nat.card F < 2 * Nat.card {a : F // Q a}) : ∀ a, Q a := by
  by_contra hne
  push Not at hne
  obtain ⟨b, hb⟩ := hne
  have hinj : Function.Injective (fun a : {a : F // Q a} => (⟨a + b, fun h => hb (by
      simpa using hsub _ _ h a.2)⟩ : {a : F // ¬ Q a})) := fun x y hxy => by
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simpa using this
  have h1 := Nat.card_le_card_of_injective _ hinj
  have h2 : Nat.card {a : F // Q a} + Nat.card {a : F // ¬ Q a} = Nat.card F := by
    have := Fintype.ofFinite F
    classical
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Nat.add_sub_cancel' (Fintype.card_subtype_le _)]
  omega

theorem fix_projRad_zero_of_card_le (hF : Nat.card F = 4) {α : MulAut (projectiveSL 3 F)}
    (hR : ∀ x ∈ projRad F 0, α x ∈ projRad F 0)
    (h8 : 8 ≤ Nat.card {v : F × F //
      α (proj 3 F (unipU F v.1 0 v.2)) = proj 3 F (unipU F v.1 0 v.2)}) :
    ∀ x ∈ projRad F 0, α x = x := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 α
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  swap
  · exfalso
    simp only [pow_one] at hR
    exact not_mapsTo_projRad_zero_of_dual A σ (hR _ (mem_projRad_zero.2 ⟨1, 0, rfl⟩))
      (hR _ (mem_projRad_zero.2 ⟨0, 1, rfl⟩))
  simp only [pow_zero, mul_one] at hR h8 ⊢
  obtain ⟨h10, h20, hact⟩ := mapsTo_projRad_zero_eq A σ hR
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_three, h10, h20] at hdet
  have h00 : M 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  set P : F × F → Prop := fun v => σ v.1 * M 0 0 = v.1 * M 1 1 + v.2 * M 2 1 ∧
    σ v.2 * M 0 0 = v.1 * M 1 2 + v.2 * M 2 2 with hP
  have hfix : ∀ v : F × F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (unipU F v.1 0 v.2)) =
      proj 3 F (unipU F v.1 0 v.2) ↔ P v := fun v => hact v.1 v.2 v.1 v.2
  have hcardP : 8 ≤ Nat.card {v : F × F // P v} := by
    rwa [← Nat.card_congr (Equiv.subtypeEquivRight hfix)]
  have hsub : ∀ v w : F × F, P v → P w → P (v - w) := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
    simp only [Prod.mk_sub_mk, map_sub, hP] at h1 h2 h3 h4 ⊢
    exact ⟨by linear_combination h1 - h3, by linear_combination h2 - h4⟩
  have hpig : ∀ f : F × F →+ F, ∃ v : F × F, P v ∧ v ≠ 0 ∧ f v = 0 := by
    intro f
    have := Fintype.ofFinite F
    have := Fintype.ofFinite {v : F × F // P v}
    obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun v : {v : F × F // P v} => f v) (by
        rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF]
        omega)
    refine ⟨(x : F × F) - y, hsub _ _ x.2 y.2, sub_ne_zero.mpr fun h => hxy (Subtype.ext h), ?_⟩
    rw [map_sub, hf, sub_self]
  obtain ⟨⟨l, l'⟩, ⟨hl1, hl2⟩, hl0, hl⟩ := hpig (AddMonoidHom.snd F F)
  obtain ⟨⟨m, m'⟩, ⟨hm1, hm2⟩, hm0, hm⟩ := hpig (AddMonoidHom.fst F F)
  obtain ⟨⟨n, n'⟩, ⟨hn1, hn2⟩, hn0, hn⟩ := hpig (AddMonoidHom.fst F F - AddMonoidHom.snd F F)
  simp only [AddMonoidHom.coe_snd, AddMonoidHom.coe_fst, AddMonoidHom.sub_apply] at hl hm hn
  subst hl hm
  have hn' : n' = n := (sub_eq_zero.mp hn).symm
  subst hn'
  have hl' : l ≠ 0 := fun h => hl0 (by rw [h]; rfl)
  have hm' : m' ≠ 0 := fun h => hm0 (by rw [h]; rfl)
  have hn'' : n' ≠ 0 := fun h => hn0 (by rw [h]; rfl)
  simp only [map_zero, zero_mul, add_zero, zero_add] at hl1 hl2 hm1 hm2 hn1 hn2
  have h12 : M 1 2 = 0 := (mul_eq_zero.mp hl2.symm).resolve_left hl'
  have h21 : M 2 1 = 0 := (mul_eq_zero.mp hm1.symm).resolve_left hm'
  rw [h21, mul_zero, add_zero] at hn1
  rw [h12, mul_zero, zero_add] at hn2
  have h22 : M 2 2 = M 1 1 := mul_left_cancel₀ hn'' (by rw [← hn2, hn1])
  set Q : F → Prop := fun a => σ a * M 0 0 = a * M 1 1 with hQ
  have hPQ : ∀ v : F × F, P v ↔ Q v.1 ∧ Q v.2 := fun v => by
    simp only [hP, hQ, h12, h21, h22, mul_zero, add_zero, zero_add]
  have hcardQ : 8 ≤ Nat.card {a : F // Q a} * Nat.card {a : F // Q a} := by
    rw [← Nat.card_prod, ← Nat.card_congr Equiv.subtypeProdEquivProd,
      ← Nat.card_congr (Equiv.subtypeEquivRight hPQ)]
    exact hcardP
  have hQall : ∀ a, Q a := by
    refine forall_of_two_mul_card_lt (fun a b ha hb => ?_) ?_
    · simp only [hQ, map_sub] at ha hb ⊢
      linear_combination ha - hb
    · rw [hF]
      by_contra hle
      push Not at hle
      have : Nat.card {a : F // Q a} ≤ 2 := by omega
      nlinarith
  have hσ1 : M 1 1 = M 0 0 := by
    have := hQall 1
    simp only [hQ, map_one, one_mul] at this
    exact this.symm
  have hσ : ∀ a, σ a = a := fun a => by
    have := hQall a
    simp only [hQ, hσ1] at this
    exact mul_right_cancel₀ h00 this
  intro x hx
  obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
  refine (hfix (a, c)).2 ?_
  rw [hPQ]
  simp only [hQ, hσ, hσ1]
  exact ⟨trivial, trivial⟩


omit [CharP F 2] [Finite F] in
theorem fieldAut_proj_leviOne (σ : F ≃+* F) (B : SL2 F) :
    fieldAut 3 F σ (proj 3 F (leviOne F B)) =
      proj 3 F (leviOne F (SpecialLinearGroup.map σ.toRingHom B)) := by
  rw [fieldAut_proj]
  congr 1
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_leviOne, coe_leviOne,
    Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp

omit [CharP F 2] [Finite F] in
theorem map_uSL (σ : F ≃+* F) (t : F) :
    SpecialLinearGroup.map σ.toRingHom (uSL t) =
      uSL (σ t) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    coe_uSL, coe_uSL]
  fin_cases i <;> fin_cases j <;> simp

omit [CharP F 2] [Finite F] in
theorem map_vSL (σ : F ≃+* F) (t : F) :
    SpecialLinearGroup.map σ.toRingHom (vSL t) =
      vSL (σ t) := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    coe_vSL, coe_vSL]
  fin_cases i <;> fin_cases j <;> simp

omit [Finite F] in
theorem trace_unipU_mul_leviOne_uSL (a c t : F) :
    trace ((unipU F a 0 c : Matrix (Fin 3) (Fin 3) F) *
      (leviOne F (uSL t) : Matrix (Fin 3) (Fin 3) F)) = 1 := by
  rw [coe_unipU, coe_leviOne, coe_uSL]
  simp [Matrix.trace_fin_three]
  exact CharTwo.add_self_eq_zero 1

omit [Finite F] in
theorem trace_unipU_mul_leviOne_vSL (a c t : F) :
    trace ((unipU F a 0 c : Matrix (Fin 3) (Fin 3) F) *
      (leviOne F (vSL t) : Matrix (Fin 3) (Fin 3) F)) = 1 := by
  rw [coe_unipU, coe_leviOne, coe_vSL]
  simp [Matrix.trace_fin_three]
  exact CharTwo.add_self_eq_zero 1


omit [Finite F] in
theorem trace_leviOne_uSL (s : F) :
    trace ((leviOne F (uSL s) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [coe_leviOne, coe_uSL]
  simp [Matrix.trace_fin_three]
  exact CharTwo.add_self_eq_zero 1

omit [Finite F] in
theorem trace_leviOne_vSL (s : F) :
    trace ((leviOne F (vSL s) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [coe_leviOne, coe_vSL]
  simp [Matrix.trace_fin_three]
  exact CharTwo.add_self_eq_zero 1

omit [CharP F 2] [Finite F] in
theorem mul_leviOne_uSL_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    (M * ((leviOne F (uSL s) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 2 then s * M i 1 else 0 := by
  rw [coe_leviOne, coe_uSL]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

omit [CharP F 2] [Finite F] in
theorem mul_leviOne_vSL_apply (M : Matrix (Fin 3) (Fin 3) F) (s : F) (i j : Fin 3) :
    (M * ((leviOne F (vSL s) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i j =
      M i j + if j = 1 then s * M i 2 else 0 := by
  rw [coe_leviOne, coe_vSL]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

omit [CharP F 2] [Finite F] in
theorem unipU_mul_leviOne_uSL_mul_apply (M : Matrix (Fin 3) (Fin 3) F) (a c t : F) (i j : Fin 3) :
    (((unipU F a 0 c * leviOne F (uSL t) : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) * M) i j =
      M i j + (if i = 0 then a * M 1 j + (a * t + c) * M 2 j else 0) +
        if i = 1 then t * M 2 j else 0 := by
  show ((unipU F a 0 c : Matrix (Fin 3) (Fin 3) F) *
    (leviOne F (uSL t) : Matrix (Fin 3) (Fin 3) F) * M) i j = _
  rw [coe_unipU, coe_leviOne, coe_uSL]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

omit [CharP F 2] [Finite F] in
theorem unipU_mul_leviOne_vSL_mul_apply (M : Matrix (Fin 3) (Fin 3) F) (a c t : F) (i j : Fin 3) :
    (((unipU F a 0 c * leviOne F (vSL t) : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) * M) i j =
      M i j + (if i = 0 then (a + c * t) * M 1 j + c * M 2 j else 0) +
        if i = 2 then t * M 1 j else 0 := by
  show ((unipU F a 0 c : Matrix (Fin 3) (Fin 3) F) *
    (leviOne F (vSL t) : Matrix (Fin 3) (Fin 3) F) * M) i j = _
  rw [coe_unipU, coe_leviOne, coe_vSL]
  fin_cases i <;> fin_cases j <;> (simp [Matrix.mul_apply, Fin.sum_univ_three]; try ring)

theorem fix_projRad_zero_of_levi (hF : Nat.card F = 4) {α : MulAut (projectiveSL 3 F)}
    (hR : ∀ x ∈ projRad F 0, α x ∈ projRad F 0)
    (hL : ∀ B : SL2 F, α (proj 3 F (leviOne F B)) * (proj 3 F (leviOne F B))⁻¹ ∈ projRad F 0)
    (h2 : ∃ n : ℕ, α ^ 2 ^ n = 1) : ∀ x ∈ projRad F 0, α x = x := by
  obtain ⟨A, σ, ε, hε, rfl⟩ := (automorphism_generation (K := F) (n := 3) le_rfl).2 α
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hε with rfl | rfl
  swap
  · exfalso
    simp only [pow_one] at hR
    exact not_mapsTo_projRad_zero_of_dual A σ (hR _ (mem_projRad_zero.2 ⟨1, 0, rfl⟩))
      (hR _ (mem_projRad_zero.2 ⟨0, 1, rfl⟩))
  simp only [pow_zero, mul_one] at hR hL h2 ⊢
  obtain ⟨h10, h20, hact⟩ := mapsTo_projRad_zero_eq A σ hR
  set M := (A : Matrix (Fin 3) (Fin 3) F) with hM
  have hdet : M.det ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero A
  rw [Matrix.det_fin_three, h10, h20] at hdet
  have hrel : ∀ B : SL2 F,
      trace ((leviOne F (SpecialLinearGroup.map σ.toRingHom B) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1 →
      (∀ a c : F, trace ((unipU F a 0 c * leviOne F B : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = 1) →
      ∃ a c : F, M * ((leviOne F (SpecialLinearGroup.map σ.toRingHom B) :
        SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((unipU F a 0 c * leviOne F B : SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) * M := by
    intro B htrB htr
    obtain ⟨a, c, h⟩ := mem_projRad_zero.1 (hL B)
    refine ⟨a, c, ?_⟩
    have h' : conjAut 3 F A (proj 3 F (leviOne F (SpecialLinearGroup.map σ.toRingHom B))) =
        proj 3 F (unipU F a 0 c * leviOne F B) := by
      rw [map_mul, h, inv_mul_cancel_right, MulAut.mul_apply, fieldAut_proj_leviOne]
    exact mul_eq_mul_of_conjAut_proj_eq (by rw [htrB, htr]) (by rw [htr]; exact one_ne_zero) h'
  have hU : ∀ t : F, ∃ a c : F, ∀ i j : Fin 3,
      M i j + (if j = 2 then σ t * M i 1 else 0) =
        M i j + (if i = 0 then a * M 1 j + (a * t + c) * M 2 j else 0) +
          if i = 1 then t * M 2 j else 0 := by
    intro t
    obtain ⟨a, c, h⟩ := hrel (uSL t) (by rw [map_uSL]; exact trace_leviOne_uSL _)
      (fun a c => trace_unipU_mul_leviOne_uSL a c t)
    refine ⟨a, c, fun i j => ?_⟩
    have := congrFun (congrFun h i) j
    rwa [map_uSL, mul_leviOne_uSL_apply, unipU_mul_leviOne_uSL_mul_apply] at this
  have hV : ∃ a c : F, ∀ i j : Fin 3,
      M i j + (if j = 1 then 1 * M i 2 else 0) =
        M i j + (if i = 0 then (a + c * 1) * M 1 j + c * M 2 j else 0) +
          if i = 2 then 1 * M 1 j else 0 := by
    obtain ⟨a, c, h⟩ := hrel (vSL 1) (by rw [map_vSL]; exact trace_leviOne_vSL _)
      (fun a c => trace_unipU_mul_leviOne_vSL a c 1)
    refine ⟨a, c, fun i j => ?_⟩
    have := congrFun (congrFun h i) j
    rwa [map_vSL, map_one, mul_leviOne_vSL_apply, unipU_mul_leviOne_vSL_mul_apply] at this
  obtain ⟨a₁, c₁, e₁⟩ := hU 1
  obtain ⟨a₂, c₂, e₂⟩ := hV
  have h21 : M 2 1 = 0 := by have := e₁ 1 1; simpa using this
  have h22 : M 2 2 = M 1 1 := by have := e₁ 1 2; simp at this; exact this.symm
  have h12 : M 1 2 = 0 := by have := e₂ 1 1; simpa using this
  rw [h12, h21, h22] at hdet
  have h11 : M 1 1 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have h00 : M 0 0 ≠ 0 := fun h => hdet (by rw [h]; ring)
  have hσ : ∀ t, σ t = t := fun t => by
    obtain ⟨a, c, e⟩ := hU t
    have := e 1 2
    simp only [Fin.isValue, Fin.reduceEq, ite_true, ite_false, add_zero, add_right_inj,
      h22] at this
    exact mul_right_cancel₀ h11 this
  set r := M 0 0 / M 1 1 with hr
  have hr0 : r ≠ 0 := div_ne_zero h00 h11
  have hrm : r * M 1 1 = M 0 0 := div_mul_cancel₀ _ h11
  have hstep : ∀ a c : F, (conjAut 3 F A * fieldAut 3 F σ) (proj 3 F (unipU F a 0 c)) =
      proj 3 F (unipU F (r * a) 0 (r * c)) := fun a c => by
    refine (hact a c (r * a) (r * c)).2 ⟨?_, ?_⟩
    · rw [hσ, h21, mul_zero, add_zero, ← hrm]
      ring
    · rw [hσ, h12, mul_zero, zero_add, h22, ← hrm]
      ring
  have hpow : ∀ j : ℕ, ∀ a c : F, ((conjAut 3 F A * fieldAut 3 F σ) ^ j)
      (proj 3 F (unipU F a 0 c)) = proj 3 F (unipU F (r ^ j * a) 0 (r ^ j * c)) := by
    intro j
    induction j with
    | zero => intro a c; simp
    | succ j ih =>
      intro a c
      rw [pow_succ, MulAut.mul_apply, hstep, ih, pow_succ, mul_assoc, mul_assoc]
  obtain ⟨n, hn⟩ := h2
  have h2n : r ^ 2 ^ n = 1 := by
    have := hpow (2 ^ n) 1 0
    rw [hn, MulAut.one_apply, mul_one, mul_zero] at this
    exact ((unipU_eq_of_proj_eq this).1).symm
  have h3 : r ^ 3 = 1 := pow_three_eq_one_of_card hF hr0
  have hr1 : r = 1 := by
    have hg : Nat.gcd 3 (2 ^ n) = 1 := Nat.Coprime.pow_right n (by norm_num)
    have := (pow_gcd_eq_one (a := r) (m := 3) (n := 2 ^ n)).2 ⟨h3, h2n⟩
    rwa [hg, pow_one] at this
  intro x hx
  obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
  rw [hstep, hr1, one_mul, one_mul]


omit [Finite F] in
@[expose] def antidiagSL : SpecialLinearGroup (Fin 3) F :=
  ⟨!![0, 0, 1; 0, 1, 0; 1, 0, 0], by simp [Matrix.det_fin_three, CharTwo.neg_eq]⟩

omit [Finite F] in
theorem antidiagSL_mul_self : (antidiagSL : SpecialLinearGroup (Fin 3) F) * antidiagSL = 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;> simp [antidiagSL, Matrix.mul_apply, Fin.sum_univ_three]

omit [Finite F] in
@[expose] def radSwap : MulAut (projectiveSL 3 F) :=
  MulAut.conj (proj 3 F antidiagSL) * dualAut 3 F

omit [Finite F] in
theorem radSwap_proj_unipU (b c : F) :
    radSwap (proj 3 F (unipU F 0 b c)) = proj 3 F (unipU F b 0 c) := by
  rw [radSwap, MulAut.mul_apply, dualAut_proj, unipU_inv, MulAut.conj_apply, ← map_mul,
    ← map_inv, ← map_mul]
  congr 1
  have hJ : (antidiagSL : SpecialLinearGroup (Fin 3) F)⁻¹ = antidiagSL :=
    inv_eq_of_mul_eq_one_right antidiagSL_mul_self
  rw [hJ]
  have ht : ((unipU F (-0) (-b) (-c + 0 * b)).transpose : Matrix (Fin 3) (Fin 3) F) =
      !![1, 0, 0; 0, 1, 0; c, b, 1] := by
    rw [SpecialLinearGroup.coe_transpose, coe_unipU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [CharTwo.neg_eq]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ht, coe_unipU]
  simp only [antidiagSL, Matrix.mul_fin_three]
  fin_cases i <;> fin_cases j <;> simp

omit [Finite F] in
theorem map_projRad_one_radSwap :
    (projRad F 1).map (radSwap : MulAut (projectiveSL 3 F)).toMonoidHom = projRad F 0 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨b, c, rfl⟩ := mem_projRad_one.1 hy
    rw [MulEquiv.coe_toMonoidHom, radSwap_proj_unipU]
    exact mem_projRad_zero.2 ⟨b, c, rfl⟩
  · intro hx
    obtain ⟨a, c, rfl⟩ := mem_projRad_zero.1 hx
    exact ⟨_, mem_projRad_one.2 ⟨a, c, rfl⟩, by rw [MulEquiv.coe_toMonoidHom, radSwap_proj_unipU]⟩

end CFSG.ComponentClassification.AS81.Sec2Aut
