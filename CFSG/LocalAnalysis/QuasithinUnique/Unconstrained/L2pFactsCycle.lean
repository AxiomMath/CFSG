module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.CharacterTheory.Semidihedral.OddFieldSL2

public section

namespace CFSG.QuasithinUnique.Unc25K1

open Matrix
open scoped MatrixGroups

section Ring

variable {R : Type*} [Ring R]

private theorem ring_cycle {a b : R} (ha : a * a = -1) (hb : b * b = -1)
    (hab : a * b = -(b * a)) :
    (1 + a) * (1 + b) * a = b * ((1 + a) * (1 + b)) ∧
      (1 + a) * (1 + b) * b = a * b * ((1 + a) * (1 + b)) := by
  have hba : b * a = -(a * b) := by rw [hab, neg_neg]
  have haba : a * b * a = b := by
    rw [mul_assoc, hba, mul_neg, ← mul_assoc, ha, neg_mul, one_mul, neg_neg]
  have hbab : b * a * b = a := by
    rw [hba, neg_mul, mul_assoc, hb, mul_neg, mul_one, neg_neg]
  constructor
  · have e1 : (1 + a) * (1 + b) * a = a + b * a + a * a + a * b * a := by noncomm_ring
    have e2 : b * ((1 + a) * (1 + b)) = b + b * a + b * b + b * a * b := by noncomm_ring
    rw [e1, e2, ha, hb, haba, hbab]
    abel
  · have e1 : (1 + a) * (1 + b) * b = b + b * b + a * b + a * (b * b) := by noncomm_ring
    have e2 : a * b * ((1 + a) * (1 + b)) =
        a * b + a * b * a + a * (b * b) + a * b * a * b := by noncomm_ring
    rw [e1, e2, hb, haba, hb]
    abel

end Ring

section Matrix

variable {F : Type*} [Field F]

private theorem mul_self_fin_two (A : Matrix (Fin 2) (Fin 2) F) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

private theorem det_one_add_fin_two (A : Matrix (Fin 2) (Fin 2) F) :
    (1 + A).det = 1 + A.trace + A.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

private theorem trace_eq_zero_of_mul_self_eq_neg_one {A : Matrix (Fin 2) (Fin 2) F}
    (hA : A * A = -1) (hdet : A.det = 1) : A.trace = 0 := by
  have h := mul_self_fin_two A
  rw [hA, hdet, one_smul] at h
  have h' : A.trace • A = 0 := by
    have h2 := congrArg (· + (1 : Matrix (Fin 2) (Fin 2) F)) h
    simpa using h2.symm
  by_contra htr
  have hA0 : A = 0 := by
    have h3 := congrArg ((A.trace)⁻¹ • ·) h'
    simpa [smul_smul, inv_mul_cancel₀ htr] using h3
  rw [hA0, Matrix.det_zero] at hdet
  exact zero_ne_one hdet

private theorem exists_sl2_cycle (h2 : (2 : F) ≠ 0) (a b : SpecialLinearGroup (Fin 2) F)
    (ha : (a : Matrix (Fin 2) (Fin 2) F) * a = -1) (hb : (b : Matrix (Fin 2) (Fin 2) F) * b = -1)
    (hab : (a : Matrix (Fin 2) (Fin 2) F) * b = -((b : Matrix (Fin 2) (Fin 2) F) * a)) :
    ∃ w : SpecialLinearGroup (Fin 2) F, w * a = b * w ∧ w * b = a * b * w := by
  set M : Matrix (Fin 2) (Fin 2) F :=
    (1 + (a : Matrix (Fin 2) (Fin 2) F)) * (1 + (b : Matrix (Fin 2) (Fin 2) F)) with hM
  have hdetM : M.det = 4 := by
    rw [hM, Matrix.det_mul, det_one_add_fin_two, det_one_add_fin_two,
      trace_eq_zero_of_mul_self_eq_neg_one ha a.2, trace_eq_zero_of_mul_self_eq_neg_one hb b.2,
      a.2, b.2]
    norm_num
  have hdet : ((2 : F)⁻¹ • M).det = 1 := by
    rw [Matrix.det_smul, Fintype.card_fin, hdetM]
    field_simp
    norm_num
  obtain ⟨h1, h2'⟩ := ring_cycle ha hb hab
  refine ⟨⟨(2 : F)⁻¹ • M, hdet⟩, ?_, ?_⟩
  · apply Subtype.ext
    change (2 : F)⁻¹ • M * (a : Matrix (Fin 2) (Fin 2) F) =
      (b : Matrix (Fin 2) (Fin 2) F) * ((2 : F)⁻¹ • M)
    rw [Matrix.smul_mul, Matrix.mul_smul, hM, h1]
  · apply Subtype.ext
    change (2 : F)⁻¹ • M * (b : Matrix (Fin 2) (Fin 2) F) =
      (a : Matrix (Fin 2) (Fin 2) F) * b * ((2 : F)⁻¹ • M)
    rw [Matrix.smul_mul, Matrix.mul_smul, hM, h2']

private theorem coe_eq_one_or_neg_one_of_mem_center {c : SpecialLinearGroup (Fin 2) F}
    (hc : c ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F)) :
    (c : Matrix (Fin 2) (Fin 2) F) = 1 ∨ (c : Matrix (Fin 2) (Fin 2) F) = -1 := by
  obtain ⟨r, hr, hrc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  rw [Fintype.card_fin] at hr
  rcases sq_eq_one_iff.mp hr with rfl | rfl
  · left
    rw [← hrc, map_one]
  · right
    rw [← hrc, map_neg, map_one]

private theorem coe_mul_self_eq_neg_one (h2 : (2 : F) ≠ 0) {a : SpecialLinearGroup (Fin 2) F}
    (h1 : (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) ≠ 1)
    (hsq : (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) *
      (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) = 1) :
    (a : Matrix (Fin 2) (Fin 2) F) * a = -1 := by
  have hmem : a * a ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_mul]; exact hsq)
  rcases coe_eq_one_or_neg_one_of_mem_center hmem with h | h
  · exfalso
    have hxx : a * a = 1 := Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul]; simpa using h)
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_left hxx
    rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 a hinv
      with rfl | rfl
    · exact h1 rfl
    · exact h1 ((QuotientGroup.eq_one_iff _).mpr
        (CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F))
  · rw [Matrix.SpecialLinearGroup.coe_mul] at h
    exact h

theorem exists_psl2_cycle (h2 : (2 : F) ≠ 0)
    {v₁ v₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F} (h₁ : v₁ ≠ 1) (h₂ : v₂ ≠ 1)
    (h₁₂ : v₁ ≠ v₂) (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1) (hc : v₁ * v₂ = v₂ * v₁) :
    ∃ w, w * v₁ * w⁻¹ = v₂ ∧ w * v₂ * w⁻¹ = v₁ * v₂ := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective v₁
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective v₂
  have ha := coe_mul_self_eq_neg_one h2 h₁ hv₁
  have hb := coe_mul_self_eq_neg_one h2 h₂ hv₂
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
    refine (QuotientGroup.eq_one_iff _).mp ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hc]
    group
  have hab : (a : Matrix (Fin 2) (Fin 2) F) * b = -((b : Matrix (Fin 2) (Fin 2) F) * a) := by
    have hprod : (a : Matrix (Fin 2) (Fin 2) F) * b =
        ((a * b * a⁻¹ * b⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((b * a : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
        show a * b * a⁻¹ * b⁻¹ * (b * a) = a * b by group]
    rcases coe_eq_one_or_neg_one_of_mem_center hmem with h | h
    · exfalso
      rw [h, one_mul, Matrix.SpecialLinearGroup.coe_mul] at hprod
      have hsq : ((a * b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
          ((a * b : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        calc (a : Matrix (Fin 2) (Fin 2) F) * b * (a * b)
            = a * (b * a) * b := by noncomm_ring
          _ = a * (a * b) * b := by rw [hprod]
          _ = (a * a) * (b * b) := by noncomm_ring
          _ = 1 := by rw [ha, hb]; noncomm_ring
      have hxx : (a * b) * (a * b) = 1 :=
        Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul]; simpa using hsq)
      have hinv : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_left hxx
      have hcen : a * b ∈ Subgroup.center (SpecialLinearGroup (Fin 2) F) := by
        rcases CFSG.Semidihedral.OddFieldSL2.eq_one_or_minusIdentity_of_inv_eq_self F h2 _ hinv
          with h' | h'
        · rw [h']
          exact Subgroup.one_mem _
        · rw [h']
          exact CFSG.Semidihedral.OddFieldSL2.minusIdentity_mem_center F
      have h12 : ((a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)) * (b : _) = 1 := by
        rw [← QuotientGroup.mk_mul]
        exact (QuotientGroup.eq_one_iff _).mpr hcen
      apply h₁₂
      calc (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
          = a * (b * b) := by rw [hv₂, mul_one]
        _ = (a * b) * b := by rw [mul_assoc]
        _ = b := by rw [h12, one_mul]
    · rw [h, neg_one_mul] at hprod
      rw [hprod, Matrix.SpecialLinearGroup.coe_mul]
  obtain ⟨w, hwa, hwb⟩ := exists_sl2_cycle h2 a b ha hb hab
  refine ⟨(w : Matrix.ProjectiveSpecialLinearGroup (Fin 2) F), ?_, ?_⟩
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hwa,
      mul_inv_cancel_right]
  · rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, hwb,
      mul_inv_cancel_right, QuotientGroup.mk_mul]

end Matrix

section FourGroup

variable {P : Type*} [Group P]

theorem mem_kleinFourOfCommutingInvolutions_iff {a b : P} (ha : a * a = 1) (hb : b * b = 1)
    (hab : Commute a b) (x : P) :
    x ∈ CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions a b ha hb hab ↔
      x = a * b ∨ x = a ∨ x = b ∨ x = 1 := by
  change x ∈ ({a * b, a, b, 1} : Set P) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

variable [Finite P]

theorem three_dvd_orderOf_of_cycle {v₁ v₂ w : P} (hv₁ : v₁ * v₁ = 1) (hv₂ : v₂ * v₂ = 1)
    (hc : Commute v₁ v₂) (h₁₂ : v₁ ≠ v₂) (hw₁ : w * v₁ * w⁻¹ = v₂)
    (hw₂ : w * v₂ * w⁻¹ = v₁ * v₂) :
    w ∈ Subgroup.normalizer
        ((CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions v₁ v₂ hv₁ hv₂ hc :
          Subgroup P) : Set P) ∧ 3 ∣ orderOf w := by
  have hw₃ : w * (v₁ * v₂) * w⁻¹ = v₁ := by
    calc w * (v₁ * v₂) * w⁻¹ = (w * v₁ * w⁻¹) * (w * v₂ * w⁻¹) := by group
      _ = v₂ * (v₁ * v₂) := by rw [hw₁, hw₂]
      _ = v₁ * (v₂ * v₂) := by rw [← mul_assoc, ← hc.eq, mul_assoc]
      _ = v₁ := by rw [hv₂, mul_one]
  have hw1' : w * 1 * w⁻¹ = 1 := by group
  have hmem := mem_kleinFourOfCommutingInvolutions_iff hv₁ hv₂ hc
  refine ⟨?_, ?_⟩
  · refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hn' : n ∈ (CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions v₁ v₂ hv₁ hv₂ hc :
        Subgroup P) := hn
    rw [hmem] at hn'
    show w * n * w⁻¹ ∈ (CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions v₁ v₂ hv₁ hv₂ hc :
        Subgroup P)
    rw [hmem]
    rcases hn' with rfl | rfl | rfl | rfl
    · right; left; exact hw₃
    · right; right; left; exact hw₁
    · left; exact hw₂
    · right; right; right; exact hw1'
  · have hpow : ∀ x : P, w ^ 3 * x * (w ^ 3)⁻¹ = w * (w * (w * x * w⁻¹) * w⁻¹) * w⁻¹ := by
      intro x
      simp only [pow_succ, pow_zero, one_mul]
      group
    have hc3 : Commute (w ^ 3) v₁ := by
      have : w ^ 3 * v₁ * (w ^ 3)⁻¹ = v₁ := by rw [hpow, hw₁, hw₂, hw₃]
      rw [Commute, SemiconjBy]
      calc w ^ 3 * v₁ = (w ^ 3 * v₁ * (w ^ 3)⁻¹) * w ^ 3 := by group
        _ = v₁ * w ^ 3 := by rw [this]
    by_contra h3
    have hcop : Nat.Coprime 3 (orderOf w) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    have hcw : Commute w v₁ := by
      have h' : Commute ((w ^ 3) ^ m) v₁ := hc3.pow_left m
      rw [hm] at h'
      exact h'
    apply h₁₂
    rw [← hw₁]
    exact (hcw.mul_inv_cancel).symm

end FourGroup

end CFSG.QuasithinUnique.Unc25K1
