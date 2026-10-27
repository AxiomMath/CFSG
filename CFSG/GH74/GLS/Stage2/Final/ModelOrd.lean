module

public import CFSG.GH74.L5U5.ModelsBasic
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.ClassicalGroups.UnitaryFlag.GroupData

public section

namespace CFSG.GH74.GLS.Stage2.Final.ModelOrd

open Matrix CFSG.Assembly.LowTwoRank CFSG.GH74.L5U5

section Centralizer

variable {F : Type} [Field F]

theorem diagGL_comm_yGL (a b : GL (Fin 2) F) :
    diagGL a b * yGL F = yGL F * diagGL a b := by
  rw [yGL, diagGL_mul, diagGL_mul, mul_one, one_mul, mul_neg_one, neg_one_mul]

theorem det_mul_det_diag_of_mem_H2 (M : ModelData F) {a h : GL (Fin 2) F} (hh : h ∈ M.H2) :
    (a : Matrix (Fin 2) (Fin 2) F).det * ((h * a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det =
      1 := by
  obtain ⟨-, hdet⟩ := (M.mem_H2 h).1 hh
  have h1 : (a : Matrix (Fin 2) (Fin 2) F).det *
      ((a⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
    rw [← det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, det_one]
  rw [Units.val_mul, det_mul, hdet, one_mul, h1]

theorem diagGL_mem_K4_of_mem {M : ModelData F} {a h : GL (Fin 2) F} (ha : a ∈ M.U2)
    (hh : h ∈ M.H2) : diagGL a (h * a⁻¹) ∈ M.K4 := by
  rw [ModelData.diagGL_mem_K4_iff]
  exact ⟨ha, M.U2.mul_mem ((M.mem_H2 h).1 hh).1 (M.U2.inv_mem ha),
    det_mul_det_diag_of_mem_H2 M hh⟩

end Centralizer

theorem card_centralizer_yK {F : Type} [Field F] [Finite F] (M : ModelData F) (h2 : (2 : F) ≠ 0) :
    Nat.card ↥(Subgroup.centralizer ({M.yK} : Set ↥M.K4)) = Nat.card ↥M.U2 * Nat.card ↥M.H2 := by
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.symm (Equiv.ofBijective
    (fun p : ↥M.U2 × ↥M.H2 => (⟨⟨diagGL (p.1 : GL (Fin 2) F)
      ((p.2 : GL (Fin 2) F) * (p.1 : GL (Fin 2) F)⁻¹),
        diagGL_mem_K4_of_mem p.1.2 p.2.2⟩, ?_⟩ :
      ↥(Subgroup.centralizer ({M.yK} : Set ↥M.K4)))) ⟨?_, ?_⟩))
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (diagGL_comm_yGL _ _)
  · rintro ⟨⟨a, ha⟩, ⟨h, hh⟩⟩ ⟨⟨a', ha'⟩, ⟨h', hh'⟩⟩ hab
    have hd := diagGL_inj (congrArg (fun g : ↥(Subgroup.centralizer ({M.yK} : Set ↥M.K4)) =>
      (g : GL (Fin 4) F)) hab)
    obtain ⟨rfl, hh2⟩ := hd
    have : h = h' := mul_right_cancel hh2
    subst this
    rfl
  · rintro ⟨⟨g, hgK⟩, hg⟩
    have hc : g * yGL F = yGL F * g := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hg
      exact congrArg (fun x : ↥M.K4 => (x : GL (Fin 4) F)) this
    obtain ⟨a, b, rfl, ha, hb, hdet⟩ := M.exists_diagGL_of_comm h2 hgK hc
    refine ⟨(⟨a, ha⟩, ⟨b * a, (M.mem_H2 _).2 ⟨M.U2.mul_mem hb ha, ?_⟩⟩), ?_⟩
    · rw [Units.val_mul, det_mul, mul_comm, hdet]
    · refine Subtype.ext (Subtype.ext ?_)
      change diagGL a (b * a * a⁻¹) = diagGL a b
      rw [mul_inv_cancel_right]

section Linear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable (F : Type) [Field F] [Finite F]

theorem card_gl_two :
    Nat.card (GL (Fin 2) F) = Nat.card F * ((Nat.card F - 1) * (Nat.card F ^ 2 - 1)) := by
  rw [card_GL_eq]
  have e : Finset.Icc 1 2 = {1, 2} := by decide
  rw [e]
  simp

theorem card_statedSL_two :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

theorem card_statedSL_four :
    Nat.card ↥(StatedSL 4 F) =
      Nat.card F ^ 6 * ((Nat.card F ^ 2 - 1) * ((Nat.card F ^ 3 - 1) * (Nat.card F ^ 4 - 1))) := by
  rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 4 F).toEquiv, card_SL_eq (by norm_num)]
  have e : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [e]
  simp

variable {F} in
theorem odd_card_of_two_ne_zero (h2 : (2 : F) ≠ 0) : Odd (Nat.card F) := by
  have : Fintype F := Fintype.ofFinite F
  have hchar : ringChar F ≠ 2 := fun h => h2 (by
    have := (ringChar.spec F 2).2 (by rw [h])
    exact_mod_cast this)
  rw [Nat.card_eq_fintype_card]
  exact Nat.odd_iff.2 (FiniteField.odd_card_of_char_ne_two hchar)

theorem arith_lin {q : ℕ} (hq : Odd q) :
    ∃ m, Odd m ∧ q ^ 6 * ((q ^ 2 - 1) * ((q ^ 3 - 1) * (q ^ 4 - 1))) =
      2 * ((q * ((q - 1) * (q ^ 2 - 1))) * (q * (q ^ 2 - 1))) * m := by
  obtain ⟨s, rfl⟩ := hq
  refine ⟨(2 * s + 1) ^ 4 * ((2 * s + 1) ^ 2 + (2 * s + 1) + 1) * (2 * s ^ 2 + 2 * s + 1),
    ((Odd.pow ⟨s, rfl⟩).mul ⟨2 * s ^ 2 + 3 * s + 1, by ring⟩).mul ⟨s ^ 2 + s, by ring⟩, ?_⟩
  have e1 : 2 * s + 1 - 1 = 2 * s := by omega
  have e2 : (2 * s + 1) ^ 2 - 1 = 4 * s ^ 2 + 4 * s := by
    have : (2 * s + 1) ^ 2 = 4 * s ^ 2 + 4 * s + 1 := by ring
    omega
  have e3 : (2 * s + 1) ^ 3 - 1 = 8 * s ^ 3 + 12 * s ^ 2 + 6 * s := by
    have : (2 * s + 1) ^ 3 = 8 * s ^ 3 + 12 * s ^ 2 + 6 * s + 1 := by ring
    omega
  have e4 : (2 * s + 1) ^ 4 - 1 = 16 * s ^ 4 + 32 * s ^ 3 + 24 * s ^ 2 + 8 * s := by
    have : (2 * s + 1) ^ 4 = 16 * s ^ 4 + 32 * s ^ 3 + 24 * s ^ 2 + 8 * s + 1 := by ring
    omega
  rw [e1, e2, e3, e4]
  ring

end Linear

theorem odd_index_lin (F : Type) [Field F] [Finite F] (h2 : (2 : F) ≠ 0) :
    ∃ m, Odd m ∧ Nat.card ↥(ModelData.lin F).K4 =
      2 * Nat.card ↥(Subgroup.centralizer ({(ModelData.lin F).yK} : Set ↥(ModelData.lin F).K4)) *
        m := by
  rw [card_centralizer_yK (ModelData.lin F) h2]
  have hU : Nat.card ↥(ModelData.lin F).U2 = Nat.card (GL (Fin 2) F) :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  have hH : Nat.card ↥(ModelData.lin F).H2 = Nat.card ↥(StatedSL 2 F) := rfl
  have hK : Nat.card ↥(ModelData.lin F).K4 = Nat.card ↥(StatedSL 4 F) := rfl
  rw [hU, hH, hK, card_gl_two, card_statedSL_two, card_statedSL_four]
  exact arith_lin (odd_card_of_two_ne_zero h2)

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] {p f : ℕ}

theorem card_statedSU_int (h : UnitaryFieldData p f F) {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card ↥(StatedSU n (p ^ f) F) : ℤ) =
      ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 2 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) F)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) hn).2.1
  rw [show StatedSU n (p ^ f) F = unitarySU p f F n from rfl, unitarySU_eq_gramSU h, card_gramSU,
    hU]

theorem card_uniGL_int [Finite F] [Fact p.Prime] [CharP F p] (h : UnitaryFieldData p f F)
    {n : ℕ} (hn : 1 ≤ n) :
    (Nat.card ↥(uniGL (unitaryInvolution F p f) n) : ℤ) =
      ((p ^ f : ℕ) : ℤ) ^ (n * (n - 1) / 2) *
        ∏ i ∈ Finset.Icc 1 n, (((p ^ f : ℕ) : ℤ) ^ i - (-1) ^ i) := by
  have hU := (unitary_full_group_order h
    (gramForm_isSymm h (G := (1 : Matrix (Fin n) (Fin n) F)) (by simp))
    (gramForm_separatingLeft h (by simp)) (Module.finrank_fin_fun _) hn).1
  rw [← hU]
  congr 1
  refine Nat.card_congr (Matrix.GeneralLinearGroup.toLin.toEquiv.subtypeEquiv fun A => ?_)
  change A ∈ uniGL _ n ↔ Matrix.GeneralLinearGroup.toLin A ∈ sesqUnitaryGroup _
  rw [mem_uniGL, mem_sesqUnitaryGroup, Matrix.GeneralLinearGroup.coe_toLin]
  simp only [Matrix.mulVecLin_apply]
  rw [gramForm_isometry_iff, Matrix.mul_one]
  have hσ : (⇑(unitaryInvolution F p f) : F → F) = ⇑h.bar :=
    funext fun c => by rw [unitaryInvolution_apply, h.bar_apply]
  simp only [conjTr, hσ]

theorem prod_Icc_two_four (Q : ℤ) :
    ∏ i ∈ Finset.Icc 2 4, (Q ^ i - (-1) ^ i) = (Q ^ 2 - 1) * ((Q ^ 3 + 1) * (Q ^ 4 - 1)) := by
  have e : Finset.Icc 2 4 = {2, 3, 4} := by decide
  rw [e]
  simp

theorem prod_Icc_two_two (Q : ℤ) :
    ∏ i ∈ Finset.Icc 2 2, (Q ^ i - (-1) ^ i) = Q ^ 2 - 1 := by
  have e : Finset.Icc 2 2 = {2} := by decide
  rw [e]
  simp

theorem prod_Icc_one_two (Q : ℤ) :
    ∏ i ∈ Finset.Icc 1 2, (Q ^ i - (-1) ^ i) = (Q + 1) * (Q ^ 2 - 1) := by
  have e : Finset.Icc 1 2 = {1, 2} := by decide
  rw [e]
  simp

theorem arith_uni {q : ℕ} (hq : Odd q) (K U H : ℕ)
    (hK : (K : ℤ) = (q : ℤ) ^ 6 * (((q : ℤ) ^ 2 - 1) * (((q : ℤ) ^ 3 + 1) * ((q : ℤ) ^ 4 - 1))))
    (hH : (H : ℤ) = (q : ℤ) * ((q : ℤ) ^ 2 - 1))
    (hU : (U : ℤ) = (q : ℤ) * (((q : ℤ) + 1) * ((q : ℤ) ^ 2 - 1))) :
    ∃ m, Odd m ∧ K = 2 * (U * H) * m := by
  obtain ⟨s, rfl⟩ := hq
  refine ⟨(2 * s + 1) ^ 4 * (4 * s ^ 2 + 2 * s + 1) * (2 * s ^ 2 + 2 * s + 1),
    ((Odd.pow ⟨s, rfl⟩).mul ⟨2 * s ^ 2 + s, by ring⟩).mul ⟨s ^ 2 + s, by ring⟩, ?_⟩
  apply Nat.cast_injective (R := ℤ)
  push_cast at hK hH hU ⊢
  rw [hK, hU, hH]
  ring

end Unitary

open CFSG.LocalAnalysis.ComponentInitial in
theorem odd_index_uni {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2) :
    ∃ m, Odd m ∧ Nat.card ↥(ModelData.uni hF).K4 =
      2 * Nat.card ↥(Subgroup.centralizer ({(ModelData.uni hF).yK} :
        Set ↥(ModelData.uni hF).K4)) * m := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have := Finite.one_lt_card (α := F)
      rw [hF] at this
      simp at this
    · exact hf
  have h : UnitaryFieldData p f F := ⟨Fact.out, hf, by rw [hF, ← pow_mul, mul_comm]⟩
  have hodd : Odd (p ^ f) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card (by rw [hF]; exact hodd.pow)
  rw [card_centralizer_yK (ModelData.uni hF) h2]
  have hK : (Nat.card ↥(ModelData.uni hF).K4 : ℤ) = ((p ^ f : ℕ) : ℤ) ^ 6 *
      ((((p ^ f : ℕ) : ℤ) ^ 2 - 1) * ((((p ^ f : ℕ) : ℤ) ^ 3 + 1) *
        (((p ^ f : ℕ) : ℤ) ^ 4 - 1))) := by
    have := card_statedSU_int h (n := 4) (by norm_num)
    rw [prod_Icc_two_four] at this
    exact this
  have hH : (Nat.card ↥(ModelData.uni hF).H2 : ℤ) =
      ((p ^ f : ℕ) : ℤ) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1) := by
    have := card_statedSU_int h (n := 2) (by norm_num)
    rw [prod_Icc_two_two, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at this
    exact this
  have hU : (Nat.card ↥(ModelData.uni hF).U2 : ℤ) =
      ((p ^ f : ℕ) : ℤ) * ((((p ^ f : ℕ) : ℤ) + 1) * (((p ^ f : ℕ) : ℤ) ^ 2 - 1)) := by
    have := card_uniGL_int h (n := 2) (by norm_num)
    rw [prod_Icc_one_two, show 2 * (2 - 1) / 2 = 1 by norm_num, pow_one] at this
    exact this
  exact arith_uni hodd _ _ _ hK hH hU

end CFSG.GH74.GLS.Stage2.Final.ModelOrd
