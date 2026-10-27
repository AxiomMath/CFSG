module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLe
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4DiagLa
public import CFSG.RankThree.PartOne.KC.LinearCommutantSemi

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace DiagL

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag
open scoped commutatorElement

variable {F : Type} [Field F]

@[expose] def eK (l a b : F) : Matrix (Fin 4) (Fin 4) F :=
  !![a, b * l, 0, 0; b, a, 0, 0; 0, 0, a, b * l; 0, 0, b, a]

theorem smul_one_add_smul_kZero (l a b : F) :
    a • (1 : Matrix (Fin 4) (Fin 4) F) + b • kZero l = eK l a b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eK, kZero, mul_comm]

theorem eK_mul_eK (l a b c d : F) :
    eK l a b * eK l c d = eK l (a * c + l * b * d) (a * d + b * c) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [eK, Matrix.mul_apply, Fin.sum_univ_four, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.cons_val, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one] <;> ring

theorem eK_apply_one_zero (l a b : F) : eK l a b 1 0 = b := by simp [eK]

theorem eK_zero_right (l a : F) : eK l a 0 = Matrix.scalar (Fin 4) a := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eK, Matrix.scalar_apply, Matrix.diagonal]

theorem eK_zero_left (l b : F) : eK l 0 b = b • kZero l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eK, kZero, mul_comm]

theorem eK_zero_zero (l : F) : eK l 0 0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [eK]

theorem ne_zero_of_coe_eq_eK {B : GL (Fin 4) F} {l a b : F}
    (hB : (B : Matrix (Fin 4) (Fin 4) F) = eK l a b) : a ≠ 0 ∨ b ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨rfl, rfl⟩ := h
  have h1 : (B : Matrix (Fin 4) (Fin 4) F) * (B⁻¹ : GL (Fin 4) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hB, eK_zero_zero, Matrix.zero_mul] at h1
  exact zero_ne_one h1

theorem coe_sq_eq_eK {B : GL (Fin 4) F} {l a b : F}
    (hB : (B : Matrix (Fin 4) (Fin 4) F) = eK l a b) :
    ((B ^ 2 : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
      eK l (a * a + l * b * b) (a * b + b * a) := by
  rw [Units.val_pow_eq_pow_val, sq, hB, eK_mul_eK]

variable [Finite F]

open CFSG.RankThree.PartOne.KCLinComm in
theorem conjAut_eq_one_of_eK {B : GL (Fin 4) F} {l a : F} (ha : a ≠ 0)
    (hB : (B : Matrix (Fin 4) (Fin 4) F) = eK l a 0) : conjAut 4 F B = 1 :=
  (conjAut_eq_one_iff (by norm_num) B).2 ⟨Units.mk0 a ha, Units.ext (by
    rw [GeneralLinearGroup.coe_scalar, hB, eK_zero_right, Units.val_mk0])⟩

open CFSG.RankThree.PartOne.KCLinComm in
theorem conjAut_eq_of_eK {B : GL (Fin 4) F} {l b : F} (hl : l ≠ 0) (hb : b ≠ 0)
    (hB : (B : Matrix (Fin 4) (Fin 4) F) = eK l 0 b) : conjAut 4 F B = conjAut 4 F (kG hl) := by
  have h1 : B = GeneralLinearGroup.scalar (Fin 4) (Units.mk0 b hb) * kG hl := Units.ext (by
    rw [Units.val_mul, GeneralLinearGroup.coe_scalar, coe_kG, hB, eK_zero_left, Units.val_mk0,
      Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul, Matrix.one_mul])
  rw [h1, map_mul, (conjAut_eq_one_iff (by norm_num) _).2 ⟨_, rfl⟩, one_mul]

open CFSG.RankThree.PartOne.KCLinComm in
theorem eq_zero_of_conjAut_eq_one {B : GL (Fin 4) F} {l a b : F}
    (hB : (B : Matrix (Fin 4) (Fin 4) F) = eK l a b) (h : conjAut 4 F B = 1) : b = 0 := by
  obtain ⟨c, hc⟩ := (conjAut_eq_one_iff (by norm_num) B).1 h
  have h1 := congrFun (congrFun (congrArg (fun A : GL (Fin 4) F => (A : Matrix (Fin 4) (Fin 4) F))
    hc) 1) 0
  simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hB, eK_apply_one_zero] at h1
  rw [← h1]
  simp

theorem conjAut_kG_ne_one {l : F} (hl : l ≠ 0) : conjAut 4 F (kG hl) ≠ 1 := by
  intro h
  have hB : ((kG hl : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = eK l 0 1 := by
    rw [coe_kG, eK_zero_left, one_smul]
  exact one_ne_zero (eq_zero_of_conjAut_eq_one hB h)

theorem conjAut_kG_sq {l : F} (hl : l ≠ 0) : conjAut 4 F (kG hl) ^ 2 = 1 := by
  rw [← map_pow, kG_sq]
  exact (CFSG.RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).2 ⟨_, rfl⟩

omit [Finite F] in
theorem conjAut_kG_mem_CA {l : F} (hl : l ≠ 0) : conjAut 4 F (kG hl) ∈ CA F hl := by
  rintro _ ⟨s, hs, rfl⟩
  have hsC : s ∈ CK F hl := (Subgroup.commutator_le.2 fun a ha b hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb) : SK F hl ≤ CK F hl) hs
  rw [mem_CK_iff] at hsC
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, coe_kG, ← hsC, Matrix.mul_assoc, ← coe_kG hl, ← Units.val_mul,
    mul_inv_cancel, Units.val_one, Matrix.mul_one]

variable (F) in
@[expose] noncomputable def AK {l : F} (hl : l ≠ 0) : Subgroup (MulAut (projectiveSL 4 F)) :=
  CA F hl ⊓ (conjAut 4 F).range

omit [Finite F] in
theorem exists_of_mem_AK (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1)
    {g : MulAut (projectiveSL 4 F)} (hg : g ∈ AK F hl) :
    ∃ (B : GL (Fin 4) F) (a b : F), g = conjAut 4 F B ∧
      (B : Matrix (Fin 4) (Fin 4) F) = eK l a b := by
  obtain ⟨hgC, B, rfl⟩ := Subgroup.mem_inf.1 hg
  have h1 : conjAut 4 F B * fieldAut 4 F 1 ∈ CA F hl := by rwa [map_one, mul_one]
  obtain ⟨-, hB⟩ := eq_of_mem_CA h4 hl hl1 B 1 h1
  exact ⟨B, _, _, rfl, hB.trans (smul_one_add_smul_kZero l _ _)⟩

omit [Finite F] in
theorem mul_comm_of_mem_AK (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1)
    {g h : MulAut (projectiveSL 4 F)} (hg : g ∈ AK F hl) (hh : h ∈ AK F hl) : g * h = h * g := by
  obtain ⟨B, a, b, rfl, hB⟩ := exists_of_mem_AK h4 hl hl1 hg
  obtain ⟨B', c, d, rfl, hB'⟩ := exists_of_mem_AK h4 hl hl1 hh
  have h1 : B * B' = B' * B := Units.ext (by
    rw [Units.val_mul, Units.val_mul, hB, hB', eK_mul_eK, eK_mul_eK]
    congr 1 <;> ring)
  rw [← map_mul, h1, map_mul]

theorem eq_one_or_eq_of_sq (h4 : (4 : F) ≠ 0) {l : F} (hl : l ≠ 0) (hl1 : l ≠ 1)
    {g : MulAut (projectiveSL 4 F)} (hg : g ∈ AK F hl) (h2 : g ^ 2 = 1) :
    g = 1 ∨ g = conjAut 4 F (kG hl) := by
  obtain ⟨B, a, b, rfl, hB⟩ := exists_of_mem_AK h4 hl hl1 hg
  rw [← map_pow] at h2
  have h3 := eq_zero_of_conjAut_eq_one (coe_sq_eq_eK hB) h2
  have h2F : (2 : F) ≠ 0 := fun h => h4 (by linear_combination (2 : F) * h)
  have hab : a * b = 0 := by
    have : (2 : F) * (a * b) = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left h2F
  rcases ne_zero_of_coe_eq_eK hB with ha | hb
  · have hb : b = 0 := (mul_eq_zero.1 hab).resolve_left ha
    subst hb
    exact Or.inl (conjAut_eq_one_of_eK ha hB)
  · have ha : a = 0 := (mul_eq_zero.1 hab).resolve_right hb
    subst ha
    exact Or.inr (conjAut_eq_of_eK hl hb hB)

theorem sq_eq_one_of_pow_four (h4 : (4 : F) ≠ 0) (hneg : IsSquare (-1 : F)) {l : F} (hl : l ≠ 0)
    (hns : ¬ IsSquare l) {g : MulAut (projectiveSL 4 F)} (hg : g ∈ AK F hl) (hg4 : g ^ 4 = 1) :
    g ^ 2 = 1 := by
  have hl1 := ne_one_of_not_isSquare hns
  obtain ⟨B, a, b, rfl, hB⟩ := exists_of_mem_AK h4 hl hl1 hg
  have hB2 := coe_sq_eq_eK hB
  have hB4 : ((B ^ 2) ^ 2 : GL (Fin 4) F) = B ^ 4 := by rw [← pow_mul]
  rw [← map_pow, ← hB4] at hg4
  have h3 := eq_zero_of_conjAut_eq_one (coe_sq_eq_eK hB2) hg4
  have h2F : (2 : F) ≠ 0 := fun h => h4 (by linear_combination (2 : F) * h)
  have hab : (a * a + l * b * b) * (a * b + b * a) = 0 := by
    have : (2 : F) * ((a * a + l * b * b) * (a * b + b * a)) = 0 := by linear_combination h3
    exact (mul_eq_zero.1 this).resolve_left h2F
  rcases ne_zero_of_coe_eq_eK hB2 with ha | hb
  · have hb : a * b + b * a = 0 := (mul_eq_zero.1 hab).resolve_left ha
    rw [← map_pow]
    exact conjAut_eq_one_of_eK ha (hb ▸ hB2)
  · exfalso
    have ha : a * a + l * b * b = 0 := (mul_eq_zero.1 hab).resolve_right hb
    rcases eq_or_ne b 0 with hb0 | hb0
    · rw [hb0, mul_zero, add_zero] at ha
      have : a = 0 := mul_self_eq_zero.1 ha
      rcases ne_zero_of_coe_eq_eK hB with h | h
      · exact h this
      · exact h hb0
    · obtain ⟨t, ht⟩ := hneg
      apply hns
      refine ⟨t * a / b, ?_⟩
      rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hb0 hb0)]
      linear_combination ha + a * a * ht

theorem conjAut_kG_not_mem_commutator (h4 : (4 : F) ≠ 0) (hneg : IsSquare (-1 : F)) {l : F}
    (hl : l ≠ 0) (hns : ¬ IsSquare l) : conjAut 4 F (kG hl) ∉ ⁅CA F hl, CA F hl⁆ := by
  classical
  have hl1 := ne_one_of_not_isSquare hns
  set z := conjAut 4 F (kG hl) with hz
  have hzA : z ∈ AK F hl := Subgroup.mem_inf.2 ⟨conjAut_kG_mem_CA hl, kG hl, rfl⟩
  have hnorm : ∀ g ∈ CA F hl, ∀ a ∈ AK F hl, g * a * g⁻¹ ∈ AK F hl := fun g hg a ha =>
    Subgroup.mem_inf.2 ⟨(mul_mem (mul_mem hg (Subgroup.mem_inf.1 ha).1) (inv_mem hg) :
      g * a * g⁻¹ ∈ CA F hl), range_conjAut_normal.conj_mem _ (Subgroup.mem_inf.1 ha).2 g⟩
  have hcent : ∀ g ∈ CA F hl, g * z = z * g := by
    intro g hg
    have h1 : (g * z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, conjAut_kG_sq, mul_one, mul_inv_cancel]
    rcases eq_one_or_eq_of_sq h4 hl hl1 (hnorm g hg z hzA) h1 with h2 | h2
    · exact absurd (by simpa using h2) (conjAut_kG_ne_one hl)
    · rw [← hz] at h2
      calc g * z = g * z * g⁻¹ * g := by group
        _ = z * g := by rw [h2]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd
    (Nat.card_pos (α := MulAut (projectiveSL 4 F))).ne'
  have hpow : ∀ a ∈ AK F hl, a ^ m = 1 ∨ a ^ m = z := by
    intro a ha
    have h1 : (a ^ m) ^ (2 ^ k) = 1 := by
      rw [← pow_mul, mul_comm, ← hkm, pow_card_eq_one']
    have h2 := sq_eq_one_of_pow_two_pow
      (fun b hb hb4 => sq_eq_one_of_pow_four h4 hneg hl hns hb hb4) k _ (pow_mem ha m) h1
    exact eq_one_or_eq_of_sq h4 hl hl1 (pow_mem ha m) h2
  have hidx : ∀ g ∈ CA F hl, ∀ h ∈ CA F hl, g ∉ AK F hl → h ∉ AK F hl → g⁻¹ * h ∈ AK F hl := by
    intro g hg h hh hgA hhA
    have hgr : g ∉ (conjAut 4 F).range := fun hr => hgA (Subgroup.mem_inf.2 ⟨hg, hr⟩)
    have hhr : h ∉ (conjAut 4 F).range := fun hr => hhA (Subgroup.mem_inf.2 ⟨hh, hr⟩)
    exact Subgroup.mem_inf.2
      ⟨mul_mem (inv_mem hg) hh, inv_mul_mem_of_not_mem h4 hl hl1 hg hh hgr hhr⟩
  have hcA : ∀ g ∈ CA F hl, ∀ h ∈ CA F hl, ⁅g, h⁆ ∈ AK F hl := fun g hg h hh =>
    Subgroup.mem_inf.2 ⟨(by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh) : ⁅g, h⁆ ∈ CA F hl),
      commutator_mem_range_conjAut g h⟩
  have hzm : z ^ m ≠ 1 := by
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, conjAut_kG_sq, one_pow, one_mul]
    exact conjAut_kG_ne_one hl
  exact not_mem_commutator_of_pow hnorm (fun a ha b hb => mul_comm_of_mem_AK h4 hl hl1 ha hb)
    hcent hpow hidx hcA hzm

end DiagL

end CFSG.ComponentClassification.CatFactsL4U4
