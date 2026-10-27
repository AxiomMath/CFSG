module

public import CFSG.GH74.Generic.BProg.B2.GenLocBasicRed
public import CFSG.GH74.Generic.BProg.B2.GenLocL4ExtAux

public section

open CFSG CFSG.GH74 Subgroup Matrix
open scoped MatrixGroups

namespace CFSG.GH74.Generic.BProg.B2.GenLocL4Out

section GroupAbs

variable {J : Type} [Group J] {A : Type} [Group A]

theorem index_le_two_of_card [Finite A] (E : Subgroup A) (hcard : Nat.card A ≤ 2 * Nat.card ↥E) : E.index ≤ 2 := by
  have h := Subgroup.card_mul_index E
  have hpos : 0 < Nat.card ↥E := Nat.card_pos
  by_contra hlt
  push Not at hlt
  have : Nat.card ↥E * 3 ≤ Nat.card ↥E * E.index := Nat.mul_le_mul_left _ hlt
  omega

theorem stab_closure (α : A →* MulAut J) (S : Set A) (x : J) (hS : ∀ a ∈ S, α a x = x) :
    ∀ a ∈ Subgroup.closure S, α a x = x := by
  have : Subgroup.closure S ≤ (MulAction.stabilizer (MulAut J) x).comap α := by
    refine (Subgroup.closure_le _).2 ?_
    intro a ha
    exact hS a ha
  intro a ha
  exact this ha

theorem mem_gamma_of_card [Finite A] (hA : CFSG.IsElementaryAbelian 2 A) (α : A →* MulAut J) (S : Set A)
    (hcard : Nat.card A ≤ 2 * Nat.card ↥(Subgroup.closure S)) (x : J) (hx : ∀ a ∈ S, α a x = x) :
    x ∈ gammaAct α :=
  le_gammaAct α ((GenLocBasic.adm_iff_index hA _).2 (index_le_two_of_card _ hcard))
    ((GenLocBasic.mem_fixedIn_map α _ x).2 (stab_closure α S x hx))

theorem card_zpowers_of_sq [Finite A] (a : A) (ha : a ≠ 1) (ha2 : a * a = 1) : Nat.card ↥(Subgroup.zpowers a) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact ha2) ha

theorem four_le_card_closure_pair [Finite A] (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b)
    (ha2 : a * a = 1) (hb2 : b * b = 1) : 4 ≤ Nat.card ↥(Subgroup.closure {a, b}) := by
  classical
  let S : Finset A := {1, a, b, a * b}
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hab
    calc a = a * (b * b) := by rw [hb2, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [h, one_mul]
  have h1 : (1 : A) ∉ ({a, b, a * b} : Finset A) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨fun h => ha h.symm, fun h => hb h.symm, hab1.symm⟩
  have h2 : a ∉ ({b, a * b} : Finset A) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    refine ⟨hab, fun h => hb ?_⟩
    have : a * b = a * 1 := by rw [mul_one]; exact h.symm
    exact mul_left_cancel this
  have h3 : b ∉ ({a * b} : Finset A) := by
    simp only [Finset.mem_singleton]
    intro h
    apply ha
    have : a * b = 1 * b := by rw [one_mul]; exact h.symm
    exact mul_right_cancel this
  have hS : S.card = 4 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h3,
      Finset.card_singleton]
  have hsub : (S : Set A) ⊆ (Subgroup.closure {a, b} : Set A) := by
    intro x hx
    simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact (Subgroup.closure {a, b}).one_mem
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact (Subgroup.closure {a, b}).mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  calc 4 = S.card := hS.symm
    _ = (S : Set A).ncard := (Set.ncard_coe_finset S).symm
    _ ≤ (Subgroup.closure {a, b} : Set A).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Nat.card ↥(Subgroup.closure {a, b}) := (Nat.card_coe_set_eq _).symm

end GroupAbs

section Forms

variable {F : Type} [Field F]

@[expose] def GraphForm (u : MulAut SL(4, F)) (B : GL (Fin 4) F) : Prop :=
  ∀ x : SL(4, F), ((u x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    (B : Matrix (Fin 4) (Fin 4) F) * ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).transpose *
      ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)

@[expose] def InnerLift (t : MulAut SL(4, F)) (g : GL (Fin 4) F) : Prop :=
  ∀ x : SL(4, F), ((t x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) =
    (g : Matrix (Fin 4) (Fin 4) F) * (x : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)

@[expose] def glT (g : GL (Fin 4) F) : GL (Fin 4) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (g : Matrix (Fin 4) (Fin 4) F)ᵀ (by
    rw [Matrix.det_transpose]; exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero)

theorem coe_glT (g : GL (Fin 4) F) : ((glT g : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = (g : Matrix (Fin 4) (Fin 4) F)ᵀ := rfl

theorem coe_mul_inv (g : GL (Fin 4) F) : (g : Matrix (Fin 4) (Fin 4) F) * ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem coe_inv_mul (g : GL (Fin 4) F) : ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem scalar_of_comm_invT (N : Matrix (Fin 4) (Fin 4) F)
    (h : ∀ x : SL(4, F), N * ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).transpose =
      ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).transpose * N) : ∃ ν : F, N = ν • (1 : Matrix (Fin 4) (Fin 4) F) := by
  refine GenLocL4Ext.exists_scalar_of_commute_sl (fun y => ?_)
  have := h (Matrix.SpecialLinearGroup.transpose y)⁻¹
  rw [inv_inv, Matrix.SpecialLinearGroup.coe_transpose, Matrix.transpose_transpose] at this
  exact this.symm

end Forms

section Forms2

variable {F : Type} [Field F]

@[expose] def GraphEq (u : MulAut SL(4, F)) (M : Matrix (Fin 4) (Fin 4) F) : Prop :=
  ∀ x : SL(4, F), ((u x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) * M = M * ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).transpose

theorem GraphForm.graphEq {u : MulAut SL(4, F)} {B : GL (Fin 4) F} (h : GraphForm u B) :
    GraphEq u (B : Matrix (Fin 4) (Fin 4) F) := by
  intro x
  rw [h x, Matrix.mul_assoc, Matrix.mul_assoc, coe_inv_mul B, Matrix.mul_one]

theorem graphEq_unique {u : MulAut SL(4, F)} {M1 M2 M1i : Matrix (Fin 4) (Fin 4) F} (h1 : M1i * M1 = 1) (h1' : M1 * M1i = 1)
    (e1 : GraphEq u M1) (e2 : GraphEq u M2) : ∃ ν : F, M2 = ν • M1 := by
  obtain ⟨ν, hν⟩ := scalar_of_comm_invT (M1i * M2) (fun x => by
    have a1 := e1 x
    have a2 := e2 x
    set X := ((x⁻¹ : SL(4, F)) : Matrix (Fin 4) (Fin 4) F).transpose with hX
    set U := ((u x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) with hU
    have hUe : U = M1 * X * M1i := by
      calc U = U * (M1 * M1i) := by rw [h1', Matrix.mul_one]
        _ = (U * M1) * M1i := by rw [Matrix.mul_assoc]
        _ = _ := by rw [a1]
    calc M1i * M2 * X = M1i * (M2 * X) := by rw [Matrix.mul_assoc]
      _ = M1i * (U * M2) := by rw [← a2]
      _ = M1i * (M1 * X * M1i) * M2 := by rw [hUe]; simp only [Matrix.mul_assoc]
      _ = X * (M1i * M2) := by
          calc M1i * (M1 * X * M1i) * M2 = (M1i * M1) * X * (M1i * M2) := by simp only [Matrix.mul_assoc]
            _ = _ := by rw [h1, Matrix.one_mul])
  refine ⟨ν, ?_⟩
  calc M2 = M1 * (M1i * M2) := by rw [← Matrix.mul_assoc, h1', Matrix.one_mul]
    _ = ν • M1 := by rw [hν, Matrix.mul_smul, Matrix.mul_one]

end Forms2

section Forms3

variable {F : Type} [Field F]

theorem graphEq_inner_mul {u t : MulAut SL(4, F)} {B g : GL (Fin 4) F} (hu : GraphForm u B) (ht : InnerLift t g) :
    GraphEq (t * u) ((g : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F)) := by
  intro x
  rw [MulAut.mul_apply, ht (u x), hu x]
  have hBBi : (B : Matrix (Fin 4) (Fin 4) F) * ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) = 1 := coe_mul_inv B
  have hgig : ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (g : Matrix (Fin 4) (Fin 4) F) = 1 := coe_inv_mul g
  have h1 : ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
      ((g : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F))) = 1 := by
    calc ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
        ((g : Matrix (Fin 4) (Fin 4) F) * (B : Matrix (Fin 4) (Fin 4) F)))
        = ((B⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) * (((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) *
          (g : Matrix (Fin 4) (Fin 4) F)) * (B : Matrix (Fin 4) (Fin 4) F) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hgig, Matrix.mul_one, coe_inv_mul B]
  simp only [Matrix.mul_assoc]
  rw [h1, Matrix.mul_one]

end Forms3

section Pkg

variable {F : Type} [Field F]

theorem innerLift_sq {t : MulAut SL(4, F)} {g : GL (Fin 4) F} (ht : InnerLift t g) (ht2 : t * t = 1) :
    ∃ μ : F, μ ≠ 0 ∧ (g : Matrix (Fin 4) (Fin 4) F) * g = μ • (1 : Matrix (Fin 4) (Fin 4) F) := by
  have hcomm : ∀ x : SL(4, F), (x : Matrix (Fin 4) (Fin 4) F) * ((g : Matrix (Fin 4) (Fin 4) F) * g) =
      ((g : Matrix (Fin 4) (Fin 4) F) * g) * (x : Matrix (Fin 4) (Fin 4) F) := by
    intro x
    have h1 : ((t (t x) : SL(4, F)) : Matrix (Fin 4) (Fin 4) F) = x := by
      have := congrArg (fun φ : MulAut SL(4, F) => ((φ x : SL(4, F)) : Matrix (Fin 4) (Fin 4) F)) ht2
      simpa using this
    rw [ht (t x), ht x] at h1
    set gm : Matrix (Fin 4) (Fin 4) F := (g : Matrix (Fin 4) (Fin 4) F)
    set gi : Matrix (Fin 4) (Fin 4) F := ((g⁻¹ : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)
    have hggi : gi * gm = 1 := coe_inv_mul g
    calc (x : Matrix (Fin 4) (Fin 4) F) * (gm * gm) = (gm * (gm * x * gi) * gi) * (gm * gm) := by rw [h1]
      _ = gm * (gm * (x * (gi * ((gi * gm) * gm)))) := by simp only [Matrix.mul_assoc]
      _ = (gm * gm) * x := by simp only [hggi, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  obtain ⟨μ, hμ⟩ := GenLocL4Ext.exists_scalar_of_commute_sl (fun x => hcomm x)
  refine ⟨μ, ?_, hμ⟩
  intro h0
  rw [h0, zero_smul] at hμ
  have hd := congrArg Matrix.det hμ
  rw [Matrix.det_mul, Matrix.det_zero] at hd
  have hg0 : (g : Matrix (Fin 4) (Fin 4) F).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).ne_zero
  exact hg0 (mul_self_eq_zero.1 hd)

end Pkg

end CFSG.GH74.Generic.BProg.B2.GenLocL4Out
