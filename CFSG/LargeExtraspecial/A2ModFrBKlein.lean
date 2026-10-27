module

public import CFSG.LargeExtraspecial.A2ModFrBRoots
public import CFSG.RankThree.PartOne.K159.KleinModel
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.LargeExtraspecial.A2Mod.FrB

open Matrix CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.RankThree.PartOne.K159 CFSG.LocalAnalysis

variable {K : Type} [Field K]

@[expose] def hypPart (v : Vm 4 K) : Fin 3 ⊕ Fin 3 → K :=
  Sum.elim (fun i => v (.inl i)) fun i => v (.inr (.inl i))

omit [Field K] in
@[simp] theorem hypPart_inl [Field K] (v : Vm 4 K) (i : Fin 3) :
    hypPart v (.inl i) = v (.inl i) := rfl

omit [Field K] in
@[simp] theorem hypPart_inr [Field K] (v : Vm 4 K) (i : Fin 3) :
    hypPart v (.inr i) = v (.inr (.inl i)) := rfl

theorem hypPart_add (v w : Vm 4 K) : hypPart (v + w) = hypPart v + hypPart w := by
  funext x
  rcases x with i | i <;> rfl

theorem hypPart_smul (a : K) (v : Vm 4 K) : hypPart (a • v) = a • hypPart v := by
  funext x
  rcases x with i | i <;> rfl

section CharTwo

variable [CharP K 2]

@[expose] noncomputable def kleinFun (g : SpecialLinearGroup (Fin 4) K) (v : Vm 4 K) : Vm 4 K :=
  Sum.elim (fun i => Klein.rho g (hypPart v) (.inl i))
    (Sum.elim (fun i => Klein.rho g (hypPart v) (.inr i)) fun t => v (.inr (.inr t)))

@[simp] theorem kleinFun_inl (g : SpecialLinearGroup (Fin 4) K) (v : Vm 4 K) (i : Fin 3) :
    kleinFun g v (.inl i) = Klein.rho g (hypPart v) (.inl i) := rfl

@[simp] theorem kleinFun_inr_inl (g : SpecialLinearGroup (Fin 4) K) (v : Vm 4 K) (i : Fin 3) :
    kleinFun g v (.inr (.inl i)) = Klein.rho g (hypPart v) (.inr i) := rfl

@[simp] theorem kleinFun_inr_inr (g : SpecialLinearGroup (Fin 4) K) (v : Vm 4 K) (t : Fin 2) :
    kleinFun g v (.inr (.inr t)) = v (.inr (.inr t)) := rfl

theorem hypPart_kleinFun (g : SpecialLinearGroup (Fin 4) K) (v : Vm 4 K) :
    hypPart (kleinFun g v) = Klein.rho g (hypPart v) := by
  funext x
  rcases x with i | i
  · rw [hypPart_inl, kleinFun_inl]
  · rw [hypPart_inr, kleinFun_inr_inl]

theorem kleinFun_add (g : SpecialLinearGroup (Fin 4) K) (v w : Vm 4 K) :
    kleinFun g (v + w) = kleinFun g v + kleinFun g w := by
  funext x
  rcases x with i | i | t
  · simp only [kleinFun_inl, hypPart_add, map_add, Pi.add_apply]
  · simp only [kleinFun_inr_inl, hypPart_add, map_add, Pi.add_apply]
  · simp only [kleinFun_inr_inr, Pi.add_apply]

theorem kleinFun_smul (g : SpecialLinearGroup (Fin 4) K) (a : K) (v : Vm 4 K) :
    kleinFun g (a • v) = a • kleinFun g v := by
  funext x
  rcases x with i | i | t
  · simp only [kleinFun_inl, hypPart_smul, map_smul, Pi.smul_apply]
  · simp only [kleinFun_inr_inl, hypPart_smul, map_smul, Pi.smul_apply]
  · simp only [kleinFun_inr_inr, Pi.smul_apply]

theorem kleinFun_mul (g h : SpecialLinearGroup (Fin 4) K) (v : Vm 4 K) :
    kleinFun (g * h) v = kleinFun g (kleinFun h v) := by
  funext x
  rcases x with i | i | t
  · rw [kleinFun_inl, kleinFun_inl, hypPart_kleinFun, map_mul, LinearEquiv.mul_apply]
  · rw [kleinFun_inr_inl, kleinFun_inr_inl, hypPart_kleinFun, map_mul, LinearEquiv.mul_apply]
  · rw [kleinFun_inr_inr, kleinFun_inr_inr, kleinFun_inr_inr]

theorem kleinFun_one (v : Vm 4 K) : kleinFun 1 v = v := by
  funext x
  rcases x with i | i | t
  · rw [kleinFun_inl, map_one, LinearEquiv.coe_one, id_eq, hypPart_inl]
  · rw [kleinFun_inr_inl, map_one, LinearEquiv.coe_one, id_eq, hypPart_inr]
  · rw [kleinFun_inr_inr]

@[expose] noncomputable def kleinEquiv (g : SpecialLinearGroup (Fin 4) K) :
    Vm 4 K ≃ₗ[K] Vm 4 K where
  toFun := kleinFun g
  invFun := kleinFun g⁻¹
  map_add' := kleinFun_add g
  map_smul' := kleinFun_smul g
  left_inv v := by rw [← kleinFun_mul, inv_mul_cancel, kleinFun_one]
  right_inv v := by rw [← kleinFun_mul, mul_inv_cancel, kleinFun_one]

variable (K) in
@[expose] noncomputable def kleinHom : SpecialLinearGroup (Fin 4) K →* (Vm 4 K ≃ₗ[K] Vm 4 K) where
  toFun := kleinEquiv
  map_one' := LinearEquiv.ext fun v => kleinFun_one v
  map_mul' g h := LinearEquiv.ext fun v => kleinFun_mul g h v

omit [CharP K 2] in
theorem quadMinus_four_eq (b c : K) (v : Vm 4 K) :
    quadMinus 4 K b c v = quadPlus 3 K (hypPart v) + (v (.inr (.inr 0)) ^ 2 +
      b * v (.inr (.inr 0)) * v (.inr (.inr 1)) + c * v (.inr (.inr 1)) ^ 2) := by
  rw [quadMinus_apply, quadPlus_apply]
  simp only [hypPart_inl, hypPart_inr]
  ring

theorem quadMinus_kleinFun (b c : K) (g : SpecialLinearGroup (Fin 4) K) (v : Vm 4 K) :
    quadMinus 4 K b c (kleinFun g v) = quadMinus 4 K b c v := by
  rw [quadMinus_four_eq, quadMinus_four_eq, hypPart_kleinFun, kleinFun_inr_inr, kleinFun_inr_inr,
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (Klein.rho_mem g)]

variable [Finite K] {b c : K}

theorem range_kleinHom_le (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (kleinHom K).range ≤ (spinAction (quadMinus 4 K b c)).range := by
  have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := K)
    (n := 4) (by omega)
  rw [range_spinAction_quadMinus_eq_commutator le_rfl hirr, MonoidHom.range_eq_map,
    ← Group.IsPerfect.commutator_eq_top, commutator_def, Subgroup.map_commutator]
  have hO : (⊤ : Subgroup (SpecialLinearGroup (Fin 4) K)).map (kleinHom K) ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c) := by
    rintro _ ⟨g, -, rfl⟩
    exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (quadMinus_kleinFun b c g)
  exact Subgroup.commutator_mono hO hO

variable (b c) in
noncomputable def kleinSpin (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    SpecialLinearGroup (Fin 4) K →* spinGroup (quadMinus 4 K b c) :=
  liftHom _ (spinAction_injective 4 hirr (CharTwo.two_eq_zero)) (kleinHom K)
    (range_kleinHom_le hirr)

theorem spinAction_kleinSpin (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : SpecialLinearGroup (Fin 4) K) :
    spinAction (quadMinus 4 K b c) (kleinSpin b c hirr g) = kleinHom K g :=
  apply_liftHom _ _ _ _ g

omit [CharP K 2] [Finite K] in
theorem single_mul_apply' (a b c d : Fin 4) (M : Matrix (Fin 4) (Fin 4) K) :
    (single a b (1 : K) * M) c d = if c = a then M b d else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : c = a
  · subst h
    simp [Matrix.single_apply]
  · simp [Ne.symm h, h]

omit [CharP K 2] [Finite K] in
theorem mul_single_transpose_apply' (a b c d : Fin 4) (M : Matrix (Fin 4) (Fin 4) K) :
    (M * (single a b (1 : K))ᵀ) c d = if d = a then M c b else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : d = a
  · subst h
    simp [Matrix.single_apply]
  · simp [Ne.symm h, h]

omit [CharP K 2] [Finite K] in
theorem alt_apply_self (w : Fin 3 ⊕ Fin 3 → K) (i : Fin 4) : Klein.alt w i i = 0 := by
  fin_cases i <;> simp [Klein.alt, antiMat]

omit [CharP K 2] [Finite K] in
theorem cong_transvection_apply (a b : Fin 4) (w : Fin 3 ⊕ Fin 3 → K) (c d : Fin 4) :
    ((1 + single a b (1 : K)) * Klein.alt w * (1 + single a b (1 : K))ᵀ :
      Matrix (Fin 4) (Fin 4) K) c d =
      Klein.alt w c d + (if c = a then Klein.alt w b d else 0) +
        (if d = a then Klein.alt w c b else 0) := by
  have e : (1 + single a b (1 : K)) * Klein.alt w * (1 + single a b (1 : K))ᵀ =
      Klein.alt w + single a b (1 : K) * Klein.alt w + Klein.alt w * (single a b (1 : K))ᵀ +
        single a b (1 : K) * (Klein.alt w * (single a b (1 : K))ᵀ) := by
    simp only [transpose_add, transpose_one, add_mul, mul_add, one_mul, mul_one,
      Matrix.mul_assoc]
    abel
  rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.add_apply, single_mul_apply',
    mul_single_transpose_apply', single_mul_apply', mul_single_transpose_apply', alt_apply_self]
  split_ifs <;> simp

omit [CharP K 2] [Finite K] in
theorem cong_transvection_apply' (a b : Fin 4) (w : Fin 3 ⊕ Fin 3 → K) (c d : Fin 4) :
    ((1 + single a b (1 : K)) * Klein.alt w * (1 + single b a (1 : K)) :
      Matrix (Fin 4) (Fin 4) K) c d =
      Klein.alt w c d + (if c = a then Klein.alt w b d else 0) +
        (if d = a then Klein.alt w c b else 0) := by
  rw [← cong_transvection_apply, transpose_add, transpose_one, transpose_single]

theorem kleinSpin_eq_of_apply (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : SpecialLinearGroup (Fin 4) K) (x : spinGroup (quadMinus 4 K b c))
    (h : ∀ v, kleinFun g v = spinAction (quadMinus 4 K b c) x v) : kleinSpin b c hirr g = x := by
  apply spinAction_injective 4 hirr CharTwo.two_eq_zero
  rw [spinAction_kleinSpin]
  exact LinearEquiv.ext fun v => h v

syntax "klein_tac" : tactic
macro_rules
  | `(tactic| klein_tac) => `(tactic| (
      intro v
      rw [lr, HypFrame.spinAction_longRoot]
      simp only [minusFrame_vec, minusVec_true, minusVec_false, eVec, fVec,
        polar_quadMinus_single_inl, polar_quadMinus_single_inr_inl]
      funext x
      rcases x with i | i | t
      · rw [kleinFun_inl, Klein.rho_apply, Klein.cong_apply,
          SpecialLinearGroup.transvection_coe]
        fin_cases i <;>
          simp only [Klein.coords, Sum.elim_inl, transpose_add, transpose_one,
            transpose_single, cong_transvection_apply'] <;>
          simp [Klein.alt, antiMat, CharTwo.neg_eq, CharTwo.sub_eq_add]
      · rw [kleinFun_inr_inl, Klein.rho_apply, Klein.cong_apply,
          SpecialLinearGroup.transvection_coe]
        fin_cases i <;>
          simp only [Klein.coords, Sum.elim_inr, transpose_add, transpose_one,
            transpose_single, cong_transvection_apply'] <;>
          simp [Klein.alt, antiMat, CharTwo.neg_eq, CharTwo.sub_eq_add]
      · rw [kleinFun_inr_inr]
        simp))

theorem kleinSpin_E01 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 1) 1) =
      lr 4 b c (by decide : (1 : Fin (4 - 1)) ≠ 2) true true :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

theorem kleinSpin_E10 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 0) 1) =
      lr 4 b c (by decide : (1 : Fin (4 - 1)) ≠ 2) false false :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

theorem kleinSpin_E03 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (0 : Fin 4) ≠ 3) 1) =
      lr 4 b c (by decide : (0 : Fin (4 - 1)) ≠ 1) true true :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

theorem kleinSpin_E12 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 2) 1) =
      lr 4 b c (by decide : (0 : Fin (4 - 1)) ≠ 1) true false :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

theorem kleinSpin_E21 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 1) 1) =
      lr 4 b c (by decide : (1 : Fin (4 - 1)) ≠ 0) true false :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

theorem kleinSpin_E13 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (1 : Fin 4) ≠ 3) 1) =
      lr 4 b c (by decide : (0 : Fin (4 - 1)) ≠ 2) true false :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

theorem kleinSpin_E31 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 1) 1) =
      lr 4 b c (by decide : (2 : Fin (4 - 1)) ≠ 0) true false :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

theorem kleinSpin_E23 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (2 : Fin 4) ≠ 3) 1) =
      lr 4 b c (by decide : (1 : Fin (4 - 1)) ≠ 2) true false :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

theorem kleinSpin_E32 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    kleinSpin b c hirr (SpecialLinearGroup.transvection (by decide : (3 : Fin 4) ≠ 2) 1) =
      lr 4 b c (by decide : (2 : Fin (4 - 1)) ≠ 1) true false :=
  kleinSpin_eq_of_apply hirr _ _ (by klein_tac)

end CharTwo

variable [Finite K] {b c : K}

omit [Finite K] in
theorem charP_two_of_card (hK : Nat.card K = 2) : CharP K 2 :=
  CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero_of_card hK)

variable (b c) in
noncomputable def kleinZ (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) :
    SpecialLinearGroup (Fin 4) (ZMod 2) →* spinGroup (quadMinus 4 K b c) :=
  letI := charP_two_of_card hK
  (kleinSpin b c hirr).comp (slEquiv (ringEquivZModTwo K hK).symm).toMonoidHom

theorem kleinZ_elemTv (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
    {i j : Fin 4} (hij : i ≠ j) :
    letI := charP_two_of_card hK
    kleinZ b c hirr hK (elemTv i j) =
      kleinSpin b c hirr (SpecialLinearGroup.transvection hij 1) := by
  simp only [kleinZ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, elemTv_eq_transvection hij,
    slEquiv_transvection, map_one]

section Images

variable (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2)
include hirr hK

theorem kleinZ_E01 :
    kleinZ b c hirr hK (elemTv 0 1) = lr 4 b c (by decide : (1 : Fin (4 - 1)) ≠ 2) true true := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E01]

theorem kleinZ_E10 :
    kleinZ b c hirr hK (elemTv 1 0) =
      lr 4 b c (by decide : (1 : Fin (4 - 1)) ≠ 2) false false := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E10]

theorem kleinZ_E03 :
    kleinZ b c hirr hK (elemTv 0 3) = lr 4 b c (by decide : (0 : Fin (4 - 1)) ≠ 1) true true := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E03]

theorem kleinZ_E12 :
    kleinZ b c hirr hK (elemTv 1 2) = lr 4 b c (by decide : (0 : Fin (4 - 1)) ≠ 1) true false := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E12]

theorem kleinZ_E21 :
    kleinZ b c hirr hK (elemTv 2 1) = lr 4 b c (by decide : (1 : Fin (4 - 1)) ≠ 0) true false := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E21]

theorem kleinZ_E13 :
    kleinZ b c hirr hK (elemTv 1 3) = lr 4 b c (by decide : (0 : Fin (4 - 1)) ≠ 2) true false := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E13]

theorem kleinZ_E31 :
    kleinZ b c hirr hK (elemTv 3 1) = lr 4 b c (by decide : (2 : Fin (4 - 1)) ≠ 0) true false := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E31]

theorem kleinZ_E23 :
    kleinZ b c hirr hK (elemTv 2 3) = lr 4 b c (by decide : (1 : Fin (4 - 1)) ≠ 2) true false := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E23]

theorem kleinZ_E32 :
    kleinZ b c hirr hK (elemTv 3 2) = lr 4 b c (by decide : (2 : Fin (4 - 1)) ≠ 1) true false := by
  have := charP_two_of_card hK
  rw [kleinZ_elemTv hirr hK (by decide), kleinSpin_E32]

end Images

end CFSG.LargeExtraspecial.A2Mod.FrB
