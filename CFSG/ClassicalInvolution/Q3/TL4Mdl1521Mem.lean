module

public import CFSG.ClassicalInvolution.Q3.TL4Mdl1521Sig
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4TFrameL
public import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.TL4.E1521

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterL4
open scoped MatrixGroups

theorem quat_rel {G : Type*} [Group G] {A : Subgroup G}
    (hA : Nonempty (↥A ≃* QuaternionGroup 2)) :
    ∃ s a b : G, a ∈ A ∧ b ∈ A ∧ s ≠ 1 ∧ s * s = 1 ∧ a * a = s ∧ b * b = s ∧
      a * b * a⁻¹ = b⁻¹ ∧ ∀ x ∈ A, x = 1 ∨ x = s ∨ x * x = s := by
  obtain ⟨e⟩ := hA
  have hm : ∀ q r : QuaternionGroup 2,
      ((e.symm q : ↥A) : G) * (e.symm r : ↥A) = (e.symm (q * r) : ↥A) := fun q r => by
    rw [map_mul, Subgroup.coe_mul]
  have hi : ∀ q : QuaternionGroup 2, ((e.symm q : ↥A) : G)⁻¹ = (e.symm q⁻¹ : ↥A) := fun q => by
    rw [map_inv, Subgroup.coe_inv]
  have key : ∀ q : QuaternionGroup 2,
      q = 1 ∨ q = QuaternionGroup.a 2 ∨ q * q = QuaternionGroup.a 2 := by decide
  refine ⟨(e.symm (QuaternionGroup.a 2) : ↥A), (e.symm (QuaternionGroup.a 1) : ↥A),
    (e.symm (QuaternionGroup.xa 0) : ↥A), (e.symm _).2, (e.symm _).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    have h1 : e.symm (QuaternionGroup.a 2) = 1 := Subtype.ext h
    rw [MulEquiv.symm_apply_eq, map_one] at h1
    exact absurd h1 (by decide)
  · rw [hm, show QuaternionGroup.a 2 * QuaternionGroup.a 2 = (1 : QuaternionGroup 2) by decide,
      map_one]
    rfl
  · rw [hm]
    congr 2
  · rw [hm]
    congr 2
  · rw [hm, hi, hi, hm]
    congr 2
  · intro x hx
    have hx' : x = ((e.symm (e ⟨x, hx⟩) : ↥A) : G) := by simp
    rcases key (e ⟨x, hx⟩) with h | h | h
    · left
      rw [hx', h, map_one]
      rfl
    · right; left
      rw [hx', h]
    · right; right
      rw [hx', hm, h]

theorem quat_lift_sq {G : Type*} [Group G] {Z : Subgroup G} (hZ : Z ≤ Subgroup.center G)
    (hZ2 : ∀ z ∈ Z, z * z = 1) {g g' z₁ z₂ : G} (hz₁ : z₁ ∈ Z) (hz₂ : z₂ ∈ Z)
    (e1 : g' * g' = g * g * z₁) (e2 : g * g' * g⁻¹ = g'⁻¹ * z₂) :
    g' * g' * (g' * g') = 1 := by
  have c1 : g * z₁ = z₁ * g := Subgroup.mem_center_iff.mp (hZ hz₁) g
  have c2 : g'⁻¹ * z₂ = z₂ * g'⁻¹ := Subgroup.mem_center_iff.mp (hZ hz₂) g'⁻¹
  have k1 : g * (g' * g') * g⁻¹ = g' * g' := by
    calc g * (g' * g') * g⁻¹ = g * g * (g * z₁) * g⁻¹ := by rw [e1]; group
      _ = g * g * (z₁ * g) * g⁻¹ := by rw [c1]
      _ = g' * g' := by rw [e1]; group
  have k2 : g * (g' * g') * g⁻¹ = g'⁻¹ * g'⁻¹ := by
    calc g * (g' * g') * g⁻¹ = (g * g' * g⁻¹) * (g * g' * g⁻¹) := by group
      _ = g'⁻¹ * (z₂ * g'⁻¹) * z₂ := by rw [e2]; group
      _ = g'⁻¹ * (g'⁻¹ * z₂) * z₂ := by rw [c2]
      _ = g'⁻¹ * g'⁻¹ * (z₂ * z₂) := by group
      _ = g'⁻¹ * g'⁻¹ := by rw [hZ2 z₂ hz₂, mul_one]
  have k := k1.symm.trans k2
  calc g' * g' * (g' * g') = g' * g' * (g'⁻¹ * g'⁻¹)⁻¹ := by rw [_root_.mul_inv_rev, inv_inv]
    _ = 1 := by rw [← k, mul_inv_cancel]

theorem le_or_le_of_forall_mem {G : Type*} [Group G] {A H K : Subgroup G}
    (h : ∀ x ∈ A, x ∈ H ∨ x ∈ K) : A ≤ H ∨ A ≤ K := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨x, hxA, hxH⟩ := IsConcreteLE.not_le_iff_exists.mp hne.1
  obtain ⟨y, hyA, hyK⟩ := IsConcreteLE.not_le_iff_exists.mp hne.2
  have hxK : x ∈ K := (h x hxA).resolve_left hxH
  have hyH : y ∈ H := (h y hyA).resolve_right hyK
  rcases h (x * y) (A.mul_mem hxA hyA) with hxy | hxy
  · exact hxH (by simpa using H.mul_mem hxy (H.inv_mem hyH))
  · exact hyK (by simpa using K.mul_mem (K.inv_mem hxK) hxy)

variable {F : Type} [Field F]

theorem scalars_mul_self (hF : Nat.card F = 3) {z : SL(4, F)} (hz : z ∈ scalars 4 F) :
    z * z = 1 := by
  obtain ⟨c, -, hcz⟩ := mem_scalars.mp hz
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, hcz, Matrix.SpecialLinearGroup.coe_one,
    Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, card3_mul_self hF c.ne_zero,
    Matrix.diagonal_one]

theorem proj_eq_of_eq_smul {g g' : SL(4, F)} (c : Fˣ) (hc : c ^ 4 = 1)
    (h : (g : Matrix (Fin 4) (Fin 4) F) = (c : F) • (g' : Matrix (Fin 4) (Fin 4) F)) :
    proj 4 F g = proj 4 F g' := by
  have hg : g = g' * scalarElement c hc := by
    apply Subtype.ext
    rw [h, Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one]
  have h1 : proj 4 F (scalarElement c hc) = 1 := by
    rw [← MonoidHom.mem_ker, ker_proj]
    exact scalarElement_mem_scalars c hc
  rw [hg, map_mul, h1, mul_one]

abbrev mT (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F := blk 1 (-1) 0 0 (-1)

theorem blockdiag_of_comm_t (h2 : (2 : F) ≠ 0) {M : Matrix (Fin 4) (Fin 4) F}
    (h : M * mT F = mT F * M) :
    M = !![M 0 0, M 0 1, 0, 0; M 1 0, M 1 1, 0, 0; 0, 0, M 2 2, M 2 3; 0, 0, M 3 2, M 3 3] := by
  have e : ∀ k l, (M * mT F) k l = (mT F * M) k l := fun k l => congrFun (congrFun h k) l
  have e02 := e 0 2
  have e03 := e 0 3
  have e12 := e 1 2
  have e13 := e 1 3
  have e20 := e 2 0
  have e21 := e 2 1
  have e30 := e 3 0
  have e31 := e 3 1
  simp [Matrix.mul_apply, Fin.sum_univ_four] at e02 e03 e12 e13 e20 e21 e30 e31
  have h02 : M 0 2 = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination -e02)
  have h03 : M 0 3 = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination -e03)
  have h12 : M 1 2 = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination -e12)
  have h13 : M 1 3 = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination -e13)
  have h20 : M 2 0 = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination e20)
  have h21 : M 2 1 = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination e21)
  have h30 : M 3 0 = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination e30)
  have h31 : M 3 1 = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination e31)
  ext k l
  fin_cases k <;> fin_cases l <;> simp [h02, h03, h12, h13, h20, h21, h30, h31]

theorem sq_neg_one_entries [Finite F] (hF : Nat.card F = 3) {p q r s : F}
    (e00 : p * p + q * r = -1) (e01 : p * q + q * s = 0) : s = -p ∧ p * s - q * r = 1 := by
  have h2 := card3_two_ne_zero hF
  have htr : s = -p := by
    by_contra hne
    have hs : p + s ≠ 0 := fun h => hne (by linear_combination h)
    have hq : q = 0 :=
      (mul_eq_zero.mp (show q * (p + s) = 0 by linear_combination e01)).resolve_right hs
    rw [hq] at e00
    by_cases hp : p = 0
    · rw [hp] at e00
      exact one_ne_zero (by linear_combination e00)
    · exact h2 (by linear_combination e00 - card3_mul_self hF hp)
  refine ⟨htr, ?_⟩
  rw [htr]
  linear_combination -e00

theorem sq_one_det_one [Finite F] (hF : Nat.card F = 3) {p q r s : F}
    (e00 : p * p + q * r = 1) (e01 : p * q + q * s = 0) (e10 : r * p + s * r = 0)
    (e11 : r * q + s * s = 1) (hdet : p * s - q * r = 1) :
    q = 0 ∧ r = 0 ∧ s = p ∧ (p = 1 ∨ p = -1) := by
  have h2 := card3_two_ne_zero hF
  by_cases hns : q = 0 ∧ r = 0 ∧ p = s
  · obtain ⟨hq, hr, hps⟩ := hns
    refine ⟨hq, hr, hps.symm, mul_self_eq_one_iff.mp ?_⟩
    rw [hq] at e00
    linear_combination e00
  · exfalso
    have hs := trace_eq_zero_of_inv e00 e01 e10 e11 hns
    rw [hs] at hdet
    exact h2 (by linear_combination -hdet - e00)

@[expose] def sl2mk (p q r s : F) (h : p * s - q * r = 1) : SL(2, F) :=
  ⟨!![p, q; r, s], by rw [Matrix.det_fin_two_of]; exact h⟩

theorem sl2mk_mem [Finite F] (hF : Nat.card F = 3) {p q r s : F} (h : p * s - q * r = 1)
    (e00 : p * p + q * r = -1) (e01 : p * q + q * s = 0) (e10 : r * p + s * r = 0)
    (e11 : r * q + s * s = -1) : sl2mk p q r s h ∈ commutator SL(2, F) := by
  refine Q3T6.mem_commutator_of_two_element_of_oddKernel_of_card_three hF (MonoidHom.id _)
    Function.surjective_id odd_card_ker_id ⟨2, ?_⟩
  apply Subtype.ext
  have hsq : ((sl2mk p q r s h : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) * (sl2mk p q r s h) =
      -1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2mk, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
      | linear_combination e00
      | linear_combination e01
      | linear_combination e10
      | linear_combination e11
  rw [Matrix.SpecialLinearGroup.coe_pow, show 2 ^ 2 = 2 + 2 from rfl, pow_add, sq, hsq]
  simp

@[expose] noncomputable def blockQ2 (F : Type) [Field F] : Subgroup (projectiveSL 4 F) :=
  (commutator SL(2, F)).map ((proj 4 F).comp (blockSL F 4 2 2 (by norm_num)))

theorem mem_blockQ2 {c : SL(2, F)} (hc : c ∈ commutator SL(2, F)) :
    proj 4 F (blockSL F 4 2 2 (by norm_num) c) ∈ blockQ2 F :=
  Subgroup.mem_map_of_mem _ hc

theorem proj_block0_injective :
    Function.Injective ((proj 4 F).comp (blockSL F 4 2 0 (by norm_num))) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : blockSL F 4 2 0 (by norm_num) x ∈ scalars 4 F := by
    rw [← ker_proj, MonoidHom.mem_ker]
    exact hx
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h1
  rw [WeakCT.coe_blockSL, blockMat_four_zero] at hc
  have e33 := congrFun (congrFun hc 3) 3
  have e00 := congrFun (congrFun hc 0) 0
  have e01 := congrFun (congrFun hc 0) 1
  have e10 := congrFun (congrFun hc 1) 0
  have e11 := congrFun (congrFun hc 1) 1
  simp at e33 e00 e01 e10 e11
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e00, e01, e10, e11, ← e33]

theorem proj_block2_injective :
    Function.Injective ((proj 4 F).comp (blockSL F 4 2 2 (by norm_num))) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : blockSL F 4 2 2 (by norm_num) x ∈ scalars 4 F := by
    rw [← ker_proj, MonoidHom.mem_ker]
    exact hx
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h1
  rw [WeakCT.coe_blockSL, blockMat_four_two] at hc
  have e00 := congrFun (congrFun hc 0) 0
  have e22 := congrFun (congrFun hc 2) 2
  have e23 := congrFun (congrFun hc 2) 3
  have e32 := congrFun (congrFun hc 3) 2
  have e33 := congrFun (congrFun hc 3) 3
  simp at e00 e22 e23 e32 e33
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e22, e23, e32, e33, ← e00]

theorem card_blockQ0 [Finite F] (hF : Nat.card F = 3) : Nat.card (blockQ0 F) = 8 := by
  rw [blockQ0, Subgroup.card_map_of_injective proj_block0_injective,
    Q3T6.natCard_commutator_of_equiv_sl2_of_card_three hF (MulEquiv.refl _)]

theorem card_blockQ2 [Finite F] (hF : Nat.card F = 3) : Nat.card (blockQ2 F) = 8 := by
  rw [blockQ2, Subgroup.card_map_of_injective proj_block2_injective,
    Q3T6.natCard_commutator_of_equiv_sl2_of_card_three hF (MulEquiv.refl _)]

theorem card_of_quat {G : Type*} [Group G] {A : Subgroup G}
    (hA : Nonempty (↥A ≃* QuaternionGroup 2)) : Nat.card A = 8 := by
  obtain ⟨e⟩ := hA
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem det_bdiag (a b c d p q r s : F) :
    (!![a, b, 0, 0; c, d, 0, 0; 0, 0, p, q; 0, 0, r, s] : Matrix (Fin 4) (Fin 4) F).det =
      (a * d - b * c) * (p * s - q * r) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_succ_row_zero, Matrix.submatrix, Fin.succAbove]
  ring

theorem mem_blockQ0_or_blockQ2 [Finite F] (hF : Nat.card F = 3) (g : SL(4, F)) {c : F}
    (hc : c * c = 1) (hg : (g : Matrix (Fin 4) (Fin 4) F) * g = c • mT F) :
    proj 4 F g ∈ blockQ0 F ∨ proj 4 F g ∈ blockQ2 F := by
  have h2 := card3_two_ne_zero hF
  have hc0 : c ≠ 0 := fun h => by rw [h, mul_zero] at hc; exact zero_ne_one hc
  have hcomm : (g : Matrix (Fin 4) (Fin 4) F) * mT F = mT F * g := by
    have h1 : (g : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) * g) =
        ((g : Matrix (Fin 4) (Fin 4) F) * g) * g := (Matrix.mul_assoc _ _ _).symm
    rw [hg, Matrix.mul_smul, Matrix.smul_mul] at h1
    exact smul_right_injective _ hc0 h1
  obtain ⟨x00, x01, x10, x11, y00, y01, y10, y11, hM⟩ : ∃ x00 x01 x10 x11 y00 y01 y10 y11 : F,
      (g : Matrix (Fin 4) (Fin 4) F) =
        !![x00, x01, 0, 0; x10, x11, 0, 0; 0, 0, y00, y01; 0, 0, y10, y11] :=
    ⟨_, _, _, _, _, _, _, _, blockdiag_of_comm_t h2 hcomm⟩
  have hdet : (x00 * x11 - x01 * x10) * (y00 * y11 - y01 * y10) = 1 := by
    rw [← det_bdiag, ← hM]
    exact g.2
  rw [hM] at hg
  rcases mul_self_eq_one_iff.mp hc with rfl | rfl
  · have q00 := congrFun (congrFun hg 0) 0
    have q01 := congrFun (congrFun hg 0) 1
    have q10 := congrFun (congrFun hg 1) 0
    have q11 := congrFun (congrFun hg 1) 1
    have q22 := congrFun (congrFun hg 2) 2
    have q23 := congrFun (congrFun hg 2) 3
    have q32 := congrFun (congrFun hg 3) 2
    have q33 := congrFun (congrFun hg 3) 3
    simp [Matrix.mul_apply, Fin.sum_univ_four] at q00 q01 q10 q11 q22 q23 q32 q33
    obtain ⟨hy, hdy⟩ := sq_neg_one_entries hF q22 q23
    have hdx : x00 * x11 - x01 * x10 = 1 := by rw [hdy, mul_one] at hdet; exact hdet
    obtain ⟨h01, h10, h11, hx⟩ := sq_one_det_one hF q00 q01 q10 q11 hdx
    have hε : x00 * x00 = 1 := by rcases hx with hx | hx <;> rw [hx] <;> norm_num
    have hε0 : x00 ≠ 0 := fun h => by rw [h, mul_zero] at hε; exact zero_ne_one hε
    right
    have hdk : x00 * y00 * (x00 * y11) - x00 * y01 * (x00 * y10) = 1 := by
      linear_combination (y00 * y11 - y01 * y10) * hε + hdy
    have hu4 : (Units.mk0 x00 hε0) ^ 4 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      linear_combination (x00 * x00 + 1) * hε
    refine ⟨sl2mk (x00 * y00) (x00 * y01) (x00 * y10) (x00 * y11) hdk, ?_, ?_⟩
    · refine sl2mk_mem hF _ ?_ ?_ ?_ ?_
      · linear_combination (y00 * y00 + y01 * y10) * hε + q22
      · linear_combination (y00 * y01 + y01 * y11) * hε + q23
      · linear_combination (y10 * y00 + y11 * y10) * hε + q32
      · linear_combination (y10 * y01 + y11 * y11) * hε + q33
    · refine (proj_eq_of_eq_smul (Units.mk0 x00 hε0) hu4 ?_).symm
      rw [Units.val_mk0, hM, WeakCT.coe_blockSL, blockMat_four_two, h01,
        h10, h11]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2mk] <;>
        first
        | linear_combination (-y00) * hε
        | linear_combination (-y01) * hε
        | linear_combination (-y10) * hε
        | linear_combination (-y11) * hε
  · have q00 := congrFun (congrFun hg 0) 0
    have q01 := congrFun (congrFun hg 0) 1
    have q10 := congrFun (congrFun hg 1) 0
    have q11 := congrFun (congrFun hg 1) 1
    have q22 := congrFun (congrFun hg 2) 2
    have q23 := congrFun (congrFun hg 2) 3
    have q32 := congrFun (congrFun hg 3) 2
    have q33 := congrFun (congrFun hg 3) 3
    simp [Matrix.mul_apply, Fin.sum_univ_four] at q00 q01 q10 q11 q22 q23 q32 q33
    obtain ⟨hx, hdx⟩ := sq_neg_one_entries hF q00 q01
    have hdy : y00 * y11 - y01 * y10 = 1 := by rw [hdx, one_mul] at hdet; exact hdet
    obtain ⟨h23, h32, h33, hy⟩ := sq_one_det_one hF q22 q23 q32 q33 hdy
    have hε : y00 * y00 = 1 := by rcases hy with hy | hy <;> rw [hy] <;> norm_num
    have hε0 : y00 ≠ 0 := fun h => by rw [h, mul_zero] at hε; exact zero_ne_one hε
    left
    have hdk : y00 * x00 * (y00 * x11) - y00 * x01 * (y00 * x10) = 1 := by
      linear_combination (x00 * x11 - x01 * x10) * hε + hdx
    have hu4 : (Units.mk0 y00 hε0) ^ 4 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      linear_combination (y00 * y00 + 1) * hε
    refine ⟨sl2mk (y00 * x00) (y00 * x01) (y00 * x10) (y00 * x11) hdk, ?_, ?_⟩
    · refine sl2mk_mem hF _ ?_ ?_ ?_ ?_
      · linear_combination (x00 * x00 + x01 * x10) * hε + q00
      · linear_combination (x00 * x01 + x01 * x11) * hε + q01
      · linear_combination (x10 * x00 + x11 * x10) * hε + q10
      · linear_combination (x10 * x01 + x11 * x11) * hε + q11
    · refine (proj_eq_of_eq_smul (Units.mk0 y00 hε0) hu4 ?_).symm
      rw [Units.val_mk0, hM, WeakCT.coe_blockSL, blockMat_four_zero, h23, h32, h33]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2mk] <;>
        first
        | linear_combination (-x00) * hε
        | linear_combination (-x01) * hε
        | linear_combination (-x10) * hε
        | linear_combination (-x11) * hε

@[expose] def tSL (F : Type) [Field F] : SL(4, F) :=
  ⟨mT F, by rw [det_blk]; ring⟩

theorem exists_conj_tSL [Finite F] (hF : Nat.card F = 3) {h : SL(4, F)} (hh : h * h = 1)
    (hne : proj 4 F h ≠ 1) : ∃ P : GL (Fin 4) F, conjAut 4 F P (proj 4 F h) = proj 4 F (tSL F) := by
  have h2 := card3_two_ne_zero hF
  have hXX : (h : Matrix (Fin 4) (Fin 4) F) * h = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hh, Matrix.SpecialLinearGroup.coe_one]
  have h1 : (h : Matrix (Fin 4) (Fin 4) F) ≠ 1 := fun h1 =>
    hne (by rw [show h = 1 from Subtype.ext h1, map_one])
  have hm1 : (h : Matrix (Fin 4) (Fin 4) F) ≠ -1 := by
    intro hm
    apply hne
    rw [← MonoidHom.mem_ker, ker_proj, mem_scalars]
    refine ⟨-1, by norm_num, ?_⟩
    rw [hm, Units.val_neg, Units.val_one, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      neg_smul, one_smul]
  obtain ⟨P, hP⟩ := CFSG.ComponentClassification.CatFactsL4U4.TBlocks.exists_frame_t2_L4 h2 hXX
    h.2 h1 hm1
  refine ⟨P⁻¹, ?_⟩
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, inv_inv, Matrix.mul_assoc, hP, ← Matrix.mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rfl

abbrev mW (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

theorem mW_mul_self : mW F * mW F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

@[expose] def wGL (F : Type) [Field F] : GL (Fin 4) F :=
  ⟨mW F, mW F, mW_mul_self, mW_mul_self⟩

theorem conjAut_wGL_block2 (x : SL(2, F)) :
    conjAut 4 F (wGL F) (proj 4 F (blockSL F 4 2 2 (by norm_num) x)) =
      proj 4 F (blockSL F 4 2 0 (by norm_num) x) := by
  rw [conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation, WeakCT.coe_blockSL, WeakCT.coe_blockSL, blockMat_four_two,
    blockMat_four_zero]
  show mW F * _ * mW F = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem map_blockQ2_swap : (blockQ2 F).map (conjAut 4 F (wGL F)).toMonoidHom = blockQ0 F := by
  rw [blockQ2, blockQ0, Subgroup.map_map]
  congr 1
  ext x
  exact conjAut_wGL_block2 x

theorem exists_aut_blockQ0 [Finite F] (hF : Nat.card F = 3) {A : Subgroup (projectiveSL 4 F)}
    (hA : Nonempty (↥A ≃* QuaternionGroup 2)) :
    ∃ φ : MulAut (projectiveSL 4 F), A.map φ.toMonoidHom = blockQ0 F := by
  obtain ⟨z, a, b, ha, hb, hz1, -, haz, hbz, hab, hall⟩ := quat_rel hA
  obtain ⟨g, rfl⟩ := proj_surjective 4 F a
  obtain ⟨g', rfl⟩ := proj_surjective 4 F b
  have hz₁ : (g * g)⁻¹ * (g' * g') ∈ scalars 4 F := by
    rw [← ker_proj, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, haz, hbz, inv_mul_cancel]
  have hz₂ : g' * (g * g' * g⁻¹) ∈ scalars 4 F := by
    rw [← ker_proj, MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hab, mul_inv_cancel]
  have hh := quat_lift_sq (g := g) (g' := g') (scalars_le_center 4 F)
    (fun _ hz => scalars_mul_self hF hz) hz₁ hz₂ (by group) (by group)
  have hzg : proj 4 F (g' * g') = z := by rw [map_mul, hbz]
  obtain ⟨P, hP⟩ := exists_conj_tSL hF hh (by rw [hzg]; exact hz1)
  rw [hzg] at hP
  have hsq : ∀ x : projectiveSL 4 F, x * x = proj 4 F (tSL F) → x ∈ blockQ0 F ∨ x ∈ blockQ2 F := by
    intro x hx
    obtain ⟨k, rfl⟩ := proj_surjective 4 F x
    rw [← map_mul] at hx
    obtain ⟨c, -, hc⟩ := proj_eq_exists hx.symm
    exact mem_blockQ0_or_blockQ2 hF k (card3_mul_self hF c.ne_zero)
      (by rw [← Matrix.SpecialLinearGroup.coe_mul]; exact hc)
  have hall₂ : ∀ x ∈ A.map (conjAut 4 F P).toMonoidHom, x ∈ blockQ0 F ∨ x ∈ blockQ2 F := by
    rintro _ ⟨y, hy, rfl⟩
    show conjAut 4 F P y ∈ blockQ0 F ∨ conjAut 4 F P y ∈ blockQ2 F
    have ha₂ : conjAut 4 F P (proj 4 F g) * conjAut 4 F P (proj 4 F g) = proj 4 F (tSL F) := by
      rw [← map_mul, haz, hP]
    rcases hall y hy with hy1 | hy1 | hy2
    · rw [hy1, map_one]
      exact Or.inl (one_mem _)
    · rw [hy1, hP, ← ha₂]
      rcases hsq _ ha₂ with h | h
      · exact Or.inl (mul_mem h h)
      · exact Or.inr (mul_mem h h)
    · exact hsq _ (by rw [← map_mul, hy2, hP])
  have hcard : Nat.card (A.map (conjAut 4 F P).toMonoidHom) = 8 := by
    rw [Subgroup.card_map_of_injective (f := (conjAut 4 F P).toMonoidHom)
      (conjAut 4 F P).injective, card_of_quat hA]
  rcases le_or_le_of_forall_mem hall₂ with hle | hle
  · exact ⟨conjAut 4 F P, Subgroup.eq_of_le_of_card_ge hle (by rw [card_blockQ0 hF, hcard])⟩
  · have hA2 := Subgroup.eq_of_le_of_card_ge hle (by rw [card_blockQ2 hF, hcard])
    refine ⟨conjAut 4 F (wGL F) * conjAut 4 F P, ?_⟩
    rw [show (conjAut 4 F (wGL F) * conjAut 4 F P).toMonoidHom =
      (conjAut 4 F (wGL F)).toMonoidHom.comp (conjAut 4 F P).toMonoidHom from rfl,
      ← Subgroup.map_map, hA2, map_blockQ2_swap]

theorem exists_mulEquiv_blockQ0 [Finite F] (hF : Nat.card F = 3) {S : Type} [Group S]
    (e₀ : S ≃* projectiveSL 4 F) {A : Subgroup S} (hA : Nonempty (↥A ≃* QuaternionGroup 2)) :
    ∃ e : S ≃* projectiveSL 4 F, A.map e.toMonoidHom = blockQ0 F := by
  obtain ⟨e⟩ := hA
  obtain ⟨φ, hφ⟩ := exists_aut_blockQ0 hF (A := A.map e₀.toMonoidHom)
    ⟨(A.equivMapOfInjective _ e₀.injective).symm.trans e⟩
  refine ⟨e₀.trans φ, ?_⟩
  rw [← hφ, Subgroup.map_map]
  rfl

theorem blockQ0_comm_blockQ2 {x y : projectiveSL 4 F} (hx : x ∈ blockQ0 F) (hy : y ∈ blockQ2 F) :
    x * y = y * x := by
  obtain ⟨c, -, rfl⟩ := hx
  obtain ⟨d, -, rfl⟩ := hy
  show proj 4 F (blockSL F 4 2 0 (by norm_num) c) * proj 4 F (blockSL F 4 2 2 (by norm_num) d) =
    proj 4 F (blockSL F 4 2 2 (by norm_num) d) * proj 4 F (blockSL F 4 2 0 (by norm_num) c)
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, WeakCT.coe_blockSL,
    WeakCT.coe_blockSL, blockMat_four_zero, blockMat_four_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem eq_blockQ2_of_comm [Finite F] (hF : Nat.card F = 3) {B : Subgroup (projectiveSL 4 F)}
    (hB : Nonempty (↥B ≃* QuaternionGroup 2)) (hc : ∀ x ∈ B, ∀ y ∈ blockQ0 F, x * y = y * x) :
    B = blockQ2 F := by
  obtain ⟨z, -, -, -, -, -, hzz, -, -, -, hall⟩ := quat_rel hB
  have hle : B ≤ blockQ2 F := by
    intro x hx
    have hx4 : x ^ 4 = 1 := by
      have h4 : x ^ 4 = x * x * (x * x) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      rcases hall x hx with h | h | h
      · rw [h4, h, one_mul, one_mul]
      · rw [h4, h, hzz, one_mul]
      · rw [h4, h, hzz]
    obtain ⟨g, rfl, hg⟩ := exists_blk_of_comm hF (hc _ hx)
    set c := (g : Matrix (Fin 4) (Fin 4) F) 0 0
    set p := (g : Matrix (Fin 4) (Fin 4) F) 2 2
    set q := (g : Matrix (Fin 4) (Fin 4) F) 2 3
    set r := (g : Matrix (Fin 4) (Fin 4) F) 3 2
    set s := (g : Matrix (Fin 4) (Fin 4) F) 3 3
    have hdg : c * c * (p * s - q * r) = 1 := by
      rw [← det_blk, ← hg]
      exact g.2
    have hc0 : c ≠ 0 := fun h0 => by rw [h0] at hdg; simp at hdg
    have hcc := card3_mul_self hF hc0
    have hdk : c * p * (c * s) - c * q * (c * r) = 1 := by linear_combination hdg
    have hu4 : (Units.mk0 c hc0) ^ 4 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
      linear_combination (c * c + 1) * hcc
    have hgk : proj 4 F g = proj 4 F (blockSL F 4 2 2 (by norm_num) (sl2mk _ _ _ _ hdk)) := by
      refine proj_eq_of_eq_smul (Units.mk0 c hc0) hu4 ?_
      rw [Units.val_mk0, hg, WeakCT.coe_blockSL, blockMat_four_two]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2mk] <;>
        first
        | linear_combination (-p) * hcc
        | linear_combination (-q) * hcc
        | linear_combination (-r) * hcc
        | linear_combination (-s) * hcc
    refine ⟨sl2mk _ _ _ _ hdk, ?_, hgk.symm⟩
    refine Q3T6.mem_commutator_of_two_element_of_oddKernel_of_card_three hF (MonoidHom.id _)
      Function.surjective_id odd_card_ker_id ⟨2, proj_block2_injective ?_⟩
    rw [map_pow, map_one]
    show (proj 4 F (blockSL F 4 2 2 (by norm_num) (sl2mk _ _ _ _ hdk))) ^ 4 = 1
    rw [← hgk, hx4]
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_blockQ2 hF, card_of_quat hB])

abbrev mI2 (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, -1, 0]

abbrev mJ2 (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 1, -1]

abbrev mJ2' (F : Type) [Field F] : Matrix (Fin 4) (Fin 4) F :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, -1; 0, 0, -1, 1]

theorem coe_block2_qI :
    ((blockSL F 4 2 2 (by norm_num) (qI F) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = mI2 F := by
  rw [WeakCT.coe_blockSL, blockMat_four_two]
  simp [qI]

theorem coe_block2_qJ (h3 : (3 : F) = 0) :
    ((blockSL F 4 2 2 (by norm_num) (qJ h3) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      mJ2 F := by
  rw [WeakCT.coe_blockSL, blockMat_four_two]
  simp [qJ]

theorem coe_block2_inv_transpose (X : SL(2, F)) :
    ((((blockSL F 4 2 2 (by norm_num) X)⁻¹).transpose : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
      !![1, 0, 0, 0; 0, 1, 0, 0;
        0, 0, (X : Matrix (Fin 2) (Fin 2) F) 1 1, -(X : Matrix (Fin 2) (Fin 2) F) 1 0;
        0, 0, -(X : Matrix (Fin 2) (Fin 2) F) 0 1, (X : Matrix (Fin 2) (Fin 2) F) 0 0] := by
  rw [← map_inv, Matrix.SpecialLinearGroup.coe_transpose, WeakCT.coe_blockSL, blockMat_four_two,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem coe_block2_qI_inv_transpose :
    ((((blockSL F 4 2 2 (by norm_num) (qI F))⁻¹).transpose : SL(4, F)) :
      Matrix (Fin 4) (Fin 4) F) = mI2 F := by
  rw [coe_block2_inv_transpose]
  simp [qI]

theorem coe_block2_qJ_inv_transpose (h3 : (3 : F) = 0) :
    ((((blockSL F 4 2 2 (by norm_num) (qJ h3))⁻¹).transpose : SL(4, F)) :
      Matrix (Fin 4) (Fin 4) F) = mJ2' F := by
  rw [coe_block2_inv_transpose]
  simp [qJ]

theorem trace_mI2 (h2 : (2 : F) ≠ 0) : (mI2 F).trace ≠ 0 := by
  rw [show (mI2 F).trace = 2 by simp [Matrix.trace, Fin.sum_univ_four]; norm_num]
  exact h2

theorem trace_mJ2 (h2 : (2 : F) ≠ 0) : (mJ2 F).trace ≠ 0 := by
  rw [show (mJ2 F).trace = 2 by simp [Matrix.trace, Fin.sum_univ_four]; norm_num]
  exact h2

theorem trace_mJ2' : (mJ2' F).trace = (mJ2 F).trace := by
  simp [Matrix.trace, Fin.sum_univ_four]

theorem conjAut_dualAut_sq (A : GL (Fin 4) F) :
    (conjAut 4 F A * dualAut 4 F) * (conjAut 4 F A * dualAut 4 F) =
      conjAut 4 F (A * Matrix.GeneralLinearGroup.inverseTranspose A) := by
  obtain ⟨-, -, -, hdd, -⟩ := standard_automorphism_transport (n := 4) (K := F)
  calc (conjAut 4 F A * dualAut 4 F) * (conjAut 4 F A * dualAut 4 F)
      = conjAut 4 F A * (dualAut 4 F * conjAut 4 F A) * dualAut 4 F := by
        simp only [mul_assoc]
    _ = conjAut 4 F A * conjAut 4 F (Matrix.GeneralLinearGroup.inverseTranspose A) *
        (dualAut 4 F * dualAut 4 F) := by
        rw [dualAut_mul_conjAut]
        simp only [mul_assoc]
    _ = _ := by rw [hdd, mul_one, map_mul]

theorem aut_fix_Q0_Q2_sq [Finite F] (hF : Nat.card F = 3) (β : MulAut (projectiveSL 4 F))
    (h0 : ∀ x ∈ blockQ0 F, β x = x) (h2' : ∀ x ∈ blockQ2 F, β x = x) : β * β = 1 := by
  have h2 := card3_two_ne_zero hF
  have h3 := card3_three_eq_zero hF
  obtain ⟨-, hform⟩ := automorphism_generation (K := F) (n := 4) (by norm_num)
  obtain ⟨A, σ, ε, hε, hβ⟩ := hform β
  rw [card3_ringEquiv hF σ, show fieldAut 4 F (RingEquiv.refl F) = 1 from map_one _,
    mul_one] at hβ
  have hfI := h0 _ (mem_blockQ0 (qI_mem hF))
  have hfJ := h0 _ (mem_blockQ0 (qJ_mem hF h3))
  have hgI := h2' _ (mem_blockQ2 (qI_mem hF))
  have hgJ := h2' _ (mem_blockQ2 (qJ_mem hF h3))
  interval_cases ε
  · rw [pow_zero, mul_one] at hβ
    subst hβ
    have hAI := comm_of_conjAut_fix A hfI (by rw [coe_block_qI]; exact trace_mI h2)
    have hAJ := comm_of_conjAut_fix A hfJ (by rw [coe_block_qJ]; exact trace_mJ h2)
    have hBI := comm_of_conjAut_fix A hgI (by rw [coe_block2_qI]; exact trace_mI2 h2)
    have hBJ := comm_of_conjAut_fix A hgJ (by rw [coe_block2_qJ]; exact trace_mJ2 h2)
    rw [coe_block_qI] at hAI
    rw [coe_block_qJ] at hAJ
    rw [coe_block2_qI] at hBI
    rw [coe_block2_qJ] at hBJ
    obtain ⟨a, p, q, r, s, hA⟩ : ∃ a p q r s : F,
        (A : Matrix (Fin 4) (Fin 4) F) = blk a p q r s :=
      ⟨_, _, _, _, _, eq_of_comm_IJ h2 hAI hAJ⟩
    rw [hA] at hBI hBJ
    have b22 := congrFun (congrFun hBI 2) 2
    have b23 := congrFun (congrFun hBI 2) 3
    have c22 := congrFun (congrFun hBJ 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_four] at b22 b23 c22
    have hr : r = -q := by linear_combination -b22
    have hq : q = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination c22 + hr)
    have hs : s = p := by linear_combination -b23
    rw [hq, neg_zero] at hr
    have hdA : a * a * (p * s - q * r) ≠ 0 := by
      rw [← det_blk, ← hA]
      exact det_ne_zero A
    have ha : a ≠ 0 := fun h0 => hdA (by rw [h0]; ring)
    have hp : p ≠ 0 := fun h0 => hdA (by rw [hs, h0, hq]; ring)
    have hAA : A * A = 1 := by
      apply Units.ext
      rw [Units.val_mul, hA, blk_mul, hq, hr, hs, Units.val_one, card3_mul_self hF ha,
        card3_mul_self hF hp]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [← map_mul, hAA, map_one]
  · rw [pow_one] at hβ
    subst hβ
    have hAI := rel_of_conjAut_dualAut_fix A hfI
      (by rw [coe_block_qI_inv_transpose, coe_block_qI]) (by rw [coe_block_qI]; exact trace_mI h2)
    have hAJ := rel_of_conjAut_dualAut_fix A hfJ
      (by rw [coe_block_qJ_inv_transpose, coe_block_qJ]; exact trace_mJ')
      (by rw [coe_block_qJ]; exact trace_mJ h2)
    have hBI := rel_of_conjAut_dualAut_fix A hgI
      (by rw [coe_block2_qI_inv_transpose, coe_block2_qI])
      (by rw [coe_block2_qI]; exact trace_mI2 h2)
    have hBJ := rel_of_conjAut_dualAut_fix A hgJ
      (by rw [coe_block2_qJ_inv_transpose, coe_block2_qJ]; exact trace_mJ2')
      (by rw [coe_block2_qJ]; exact trace_mJ2 h2)
    rw [coe_block_qI_inv_transpose, coe_block_qI] at hAI
    rw [coe_block_qJ_inv_transpose, coe_block_qJ] at hAJ
    rw [coe_block2_qI_inv_transpose, coe_block2_qI] at hBI
    rw [coe_block2_qJ_inv_transpose, coe_block2_qJ] at hBJ
    obtain ⟨b, p, q, r, s, hA⟩ : ∃ b p q r s : F,
        (A : Matrix (Fin 4) (Fin 4) F) = blkJ b p q r s :=
      ⟨_, _, _, _, _, eq_of_rel_dual h2 hAI hAJ⟩
    rw [hA] at hBI hBJ
    have b22 := congrFun (congrFun hBI 2) 2
    have b23 := congrFun (congrFun hBI 2) 3
    have c22 := congrFun (congrFun hBJ 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_four] at b22 b23 c22
    have hr : r = -q := by linear_combination -b22
    have hs : s = p := by linear_combination -b23
    have hp : p = 0 := eq_zero_of_eq_neg h2 rfl (by linear_combination -c22 - hr)
    rw [hp] at hs
    have hAT : (A : Matrix (Fin 4) (Fin 4) F)ᵀ = -(A : Matrix (Fin 4) (Fin 4) F) := by
      rw [hA, hp, hs, hr]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [conjAut_dualAut_sq]
    refine (RankThree.PartOne.KCLinComm.conjAut_eq_one_iff (by norm_num) _).mpr ⟨-1, ?_⟩
    apply Units.ext
    have h1 : (A : Matrix (Fin 4) (Fin 4) F)ᵀ * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
        1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.transpose_one]
    rw [hAT, Matrix.neg_mul] at h1
    rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_inverseTranspose,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]
    rw [show (A : Matrix (Fin 4) (Fin 4) F) * ((A⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)ᵀ =
      -1 by rw [← h1, neg_neg]]
    simp

theorem mul_conj_mul_inv {G : Type*} [Group G] (α : MulAut G) (x : G) :
    α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.inv_apply,
    MulEquiv.apply_symm_apply]

theorem no_sigma_blockQ [Finite F] (hF : Nat.card F = 3) (α : MulAut (projectiveSL 4 F))
    (hfix : ∀ a ∈ blockQ0 F, α a = a)
    (hw : ∃ w ∈ blockQ2 F, orderOf w = 4 ∧ ∀ b ∈ blockQ2 F, α b = w * b * w⁻¹) :
    α * α ≠ 1 := by
  obtain ⟨w, hw2, hwo, hact⟩ := hw
  intro hα2
  have hαw : α w = w := by rw [hact w hw2]; group
  set β := α * (MulAut.conj w)⁻¹ with hβ
  have hβx : ∀ x, β x = α (w⁻¹ * x * w) := fun x => by
    rw [hβ, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, inv_inv]
  have hβ0 : ∀ x ∈ blockQ0 F, β x = x := fun x hx => by
    rw [hβx, show w⁻¹ * x * w = x by rw [mul_assoc, blockQ0_comm_blockQ2 hx hw2]; group,
      hfix x hx]
  have hβ2 : ∀ x ∈ blockQ2 F, β x = x := fun x hx => by
    rw [hβx, map_mul, map_mul, map_inv, hαw, hact x hx]
    group
  have hββ := aut_fix_Q0_Q2_sq hF β hβ0 hβ2
  have hαc : α * MulAut.conj w = MulAut.conj w * α := by
    have h1 := mul_conj_mul_inv α w
    rw [hαw] at h1
    calc α * MulAut.conj w = α * MulAut.conj w * α⁻¹ * α := by group
      _ = MulAut.conj w * α := by rw [h1]
  have hc : MulAut.conj (w * w) = 1 := by
    have hαβ : α = β * MulAut.conj w := by rw [hβ]; group
    have hβc : β * MulAut.conj w = MulAut.conj w * β := by
      calc β * MulAut.conj w = α := by rw [hβ]; group
        _ = MulAut.conj w * β := by
          rw [hβ, ← mul_assoc, ← hαc, mul_assoc, mul_inv_cancel, mul_one]
    calc MulAut.conj (w * w) = β * β * (MulAut.conj w * MulAut.conj w) := by
          rw [hββ, one_mul, map_mul]
      _ = (β * MulAut.conj w) * (β * MulAut.conj w) := by
          rw [mul_assoc β (MulAut.conj w) (β * MulAut.conj w), ← mul_assoc (MulAut.conj w),
            ← hβc]
          group
      _ = 1 := by rw [← hαβ, hα2]
  have hwz : w * w ∈ Subgroup.center (projectiveSL 4 F) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun φ : MulAut (projectiveSL 4 F) => φ y) hc
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * (w * w) = (w * w) * y * (w * w)⁻¹ * (w * w) := by rw [this]
      _ = (w * w) * y := by group
  rw [RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num),
    Subgroup.mem_bot] at hwz
  have h2 : orderOf w ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq, hwz])
  rw [hwo] at h2
  exact absurd h2 (by norm_num)

end CFSG.ClassicalInvolution.Q3.TL4.E1521
