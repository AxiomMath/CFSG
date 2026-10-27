module

public import CFSG.GroupTheory.GL52.InvolutionsConj
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public noncomputable section

namespace CFSG.GroupTheory.GL52

open Matrix
open scoped Pointwise

theorem inv_add_self_fin {n : ℕ} (v : Fin n → ZMod 2) : v + v = 0 := by
  ext i
  simp only [Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

@[expose] def invEM (a : Fin 4 → ZMod 2) : M5 :=
  !![1, a 0, a 1, a 2, a 3; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]

theorem invEM_mul (a b : Fin 4 → ZMod 2) : invEM a * invEM b = invEM (a + b) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invEM, Matrix.mul_apply, Fin.sum_univ_five] <;> ring

theorem invEM_zero : invEM 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem invEM_self (a : Fin 4 → ZMod 2) : invEM a * invEM a = 1 := by
  rw [invEM_mul, inv_add_self_fin, invEM_zero]

@[expose] def invEHom : Multiplicative (Fin 4 → ZMod 2) →* G52 where
  toFun a := mk5 (invEM a.toAdd) (invEM a.toAdd) (invEM_self _)
  map_one' := Units.ext (by simp [invEM_zero])
  map_mul' a b := Units.ext (by simp [invEM_mul])

theorem coe_invEHom (a : Multiplicative (Fin 4 → ZMod 2)) :
    ((invEHom a : G52) : M5) = invEM a.toAdd :=
  rfl

theorem invEHom_injective : Function.Injective invEHom := by
  intro a b h
  have h' := congrArg (fun g : G52 => (g : M5)) h
  simp only [coe_invEHom] at h'
  apply Multiplicative.toAdd.injective
  funext k
  have := congrFun (congrFun h' 0) k.succ
  fin_cases k <;> simpa [invEM] using this

@[expose] def invE : Subgroup G52 :=
  invEHom.range

theorem inv_card_E : Nat.card invE = 16 := by
  rw [invE, ← Nat.card_congr (MonoidHom.ofInjective invEHom_injective).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun,
    ZMod.card, Fintype.card_fin]
  norm_num

theorem inv_E_comm : ∀ x ∈ invE, ∀ y ∈ invE, x * y = y * x := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

theorem invEM_eq (a : Fin 4 → ZMod 2) :
    invEM a = 1 + vecMulVec (Pi.single 0 1) ![0, a 0, a 1, a 2, a 3] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invEM, vecMulVec]

theorem inv_conj_mem_E {h : G52} (h0 : (h : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1)
    (h0' : ((h⁻¹ : G52) : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1) {x : G52} (hx : x ∈ invE) :
    h * x * h⁻¹ ∈ invE := by
  obtain ⟨a, rfl⟩ := hx
  set ψ : V5 := ![0, a.toAdd 0, a.toAdd 1, a.toAdd 2, a.toAdd 3] ᵥ* ((h⁻¹ : G52) : M5) with hψ
  have hψ0 : ψ 0 = 0 := by
    have hcol : ∀ k : Fin 5, ((h⁻¹ : G52) : M5) k 0 = (Pi.single 0 1 : V5) k := by
      intro k
      rw [mulVec_single_one] at h0'
      have := congrFun h0' k
      rwa [col_apply] at this
    rw [hψ, vecMul, dotProduct, Fin.sum_univ_five, hcol, hcol, hcol, hcol, hcol]
    simp
  refine ⟨Multiplicative.ofAdd (fun k : Fin 4 => ψ k.succ), Units.ext ?_⟩
  have hinv : (h : M5) * ((h⁻¹ : G52) : M5) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [coe_invEHom, Units.val_mul, Units.val_mul, coe_invEHom, toAdd_ofAdd, invEM_eq, invEM_eq,
    mul_add, mul_one, add_mul, hinv, mul_vecMulVec, h0, vecMulVec_mul, ← hψ]
  refine congrArg (fun φ => 1 + vecMulVec (Pi.single 0 1) φ) ?_
  funext k
  fin_cases k
  · exact hψ0.symm
  all_goals rfl

@[expose] def invAM (w : Fin 3 → ZMod 2) (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) : M5 :=
  !![1, 0, 0, 0, 0; 0, B 0 0, B 0 1, B 0 2, w 0; 0, B 1 0, B 1 1, B 1 2, w 1;
    0, B 2 0, B 2 1, B 2 2, w 2; 0, 0, 0, 0, 1]

theorem invAM_mul (w w' : Fin 3 → ZMod 2) (B B' : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    invAM w B * invAM w' B' = invAM (w + B *ᵥ w') (B * B') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invAM, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, mulVec, dotProduct] <;>
    ring

theorem invAM_one : invAM 0 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem invAM_trans_mul (w : Fin 3 → ZMod 2) : invAM w 1 * invAM w 1 = 1 := by
  rw [invAM_mul, one_mulVec, inv_add_self_fin, mul_one, invAM_one]

theorem invAM_lin_mul (B : GL (Fin 3) (ZMod 2)) :
    invAM 0 (B : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      invAM 0 ((B⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := by
  rw [invAM_mul, mulVec_zero, add_zero, ← Units.val_mul, mul_inv_cancel, Units.val_one, invAM_one]

@[expose] def invTransHom : Multiplicative (Fin 3 → ZMod 2) →* G52 where
  toFun w := mk5 (invAM w.toAdd 1) (invAM w.toAdd 1) (invAM_trans_mul _)
  map_one' := Units.ext (by simp [invAM_one])
  map_mul' w w' := Units.ext (by simp [invAM_mul])

@[expose] def invLinHom : GL (Fin 3) (ZMod 2) →* G52 where
  toFun B := mk5 (invAM 0 (B : Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (invAM 0 ((B⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) (invAM_lin_mul B)
  map_one' := Units.ext (by rw [coe_mk5, Units.val_one, Units.val_one, invAM_one])
  map_mul' B B' := Units.ext (by
    rw [coe_mk5, Units.val_mul, Units.val_mul, coe_mk5, coe_mk5, invAM_mul, mulVec_zero,
      add_zero])

theorem invTransHom_conj (B : GL (Fin 3) (ZMod 2)) :
    invTransHom.comp (affAct B).toMonoidHom =
      (MulAut.conj (invLinHom B)).toMonoidHom.comp invTransHom := by
  refine MonoidHom.ext fun w => ?_
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine Units.ext ?_
  simp only [invTransHom, invLinHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, coe_mk5,
    coe_mk5_inv]
  rw [invAM_mul, invAM_mul, mul_one, zero_add, mulVec_zero, add_zero, ← Units.val_mul,
    mul_inv_cancel, Units.val_one]
  rfl

@[expose] def invAHom : Hol8 →* G52 :=
  SemidirectProduct.lift invTransHom invLinHom invTransHom_conj

theorem coe_invAHom (x : Hol8) :
    ((invAHom x : G52) : M5) = invAM x.left.toAdd (x.right : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
  change (((invTransHom x.left * invLinHom x.right : G52)) : M5) = _
  simp only [invTransHom, invLinHom, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_mul, coe_mk5]
  rw [invAM_mul, mulVec_zero, add_zero, one_mul]

theorem invAHom_injective : Function.Injective invAHom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h' := congrArg (fun g : G52 => (g : M5)) hx
  simp only [coe_invAHom, Units.val_one] at h'
  have hw : x.left = 1 := by
    apply Multiplicative.toAdd.injective
    funext k
    have := congrFun (congrFun h' k.succ.castSucc) 4
    fin_cases k <;> simpa [invAM] using this
  have hB : x.right = 1 := by
    refine Units.ext ?_
    ext a b
    have := congrFun (congrFun h' a.succ.castSucc) b.succ.castSucc
    fin_cases a <;> fin_cases b <;> simpa [invAM, Matrix.one_apply] using this
  exact SemidirectProduct.ext hw hB

@[expose] def invA : Subgroup G52 :=
  invAHom.range

theorem inv_card_Hol8 : Nat.card Hol8 = 1344 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd, Matrix.card_GL_field, Nat.card_eq_fintype_card,
    Fintype.card_fun, ZMod.card, Fintype.card_fin, Fin.prod_univ_three]
  norm_num

theorem inv_card_A : Nat.card invA = 1344 := by
  rw [invA, ← Nat.card_congr (MonoidHom.ofInjective invAHom_injective).toEquiv, inv_card_Hol8]

theorem inv_t0_matrix_commute {g : G52} (hg : g ∈ Subgroup.centralizer {invT0}) :
    (g : M5) * invT0M = invT0M * (g : M5) := by
  have := congrArg (fun x : G52 => (x : M5)) (Subgroup.mem_centralizer_singleton_iff.1 hg)
  simpa [invT0] using this

theorem inv_t0_shape {g : G52} (hg : g ∈ Subgroup.centralizer {invT0}) :
    (∀ i : Fin 5, i ≠ 0 → (g : M5) i 0 = 0) ∧ (∀ j : Fin 5, j ≠ 4 → (g : M5) 4 j = 0) ∧
      (g : M5) 0 0 = 1 ∧ (g : M5) 4 4 = 1 := by
  have hc := inv_t0_matrix_commute hg
  have e : ∀ i j, ((g : M5) * invT0M) i j = (invT0M * (g : M5)) i j := fun i j => by rw [hc]
  have hcol : ∀ i : Fin 5, i ≠ 0 → (g : M5) i 0 = 0 := by
    intro i hi
    have := e i 4
    fin_cases i
    · exact absurd rfl hi
    all_goals simpa [invT0M, Matrix.mul_apply, Fin.sum_univ_five] using this
  have hrow : ∀ j : Fin 5, j ≠ 4 → (g : M5) 4 j = 0 := by
    intro j hj
    have := e 0 j
    fin_cases j
    all_goals first
      | exact absurd rfl hj
      | simpa [invT0M, Matrix.mul_apply, Fin.sum_univ_five] using this.symm
  have h04 : (g : M5) 0 0 = (g : M5) 4 4 := by
    have := e 0 4
    simp [invT0M, Matrix.mul_apply, Fin.sum_univ_five] at this
    linear_combination this
  have h00 : (g : M5) 0 0 = 1 := by
    have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
    refine key _ fun h0 => ?_
    have hz : (g : M5) *ᵥ Pi.single 0 1 = 0 := by
      ext i
      rw [mulVec_single_one, col_apply, Pi.zero_apply]
      by_cases hi : i = 0
      · rw [hi, h0]
      · exact hcol i hi
    exact (by decide : (Pi.single 0 1 : V5) ≠ 0) (eq_zero_of_mulVec_eq_zero g hz)
  exact ⟨hcol, hrow, h00, h04 ▸ h00⟩

theorem inv_t0_fix_e0 {g : G52} (hg : g ∈ Subgroup.centralizer {invT0}) :
    (g : M5) *ᵥ Pi.single 0 1 = Pi.single 0 1 := by
  obtain ⟨hcol, -, h00, -⟩ := inv_t0_shape hg
  ext i
  rw [mulVec_single_one, col_apply]
  by_cases hi : i = 0
  · rw [hi, h00]
    rfl
  · rw [hcol i hi, Pi.single_eq_of_ne hi]

@[expose] def invMid (g : M5) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Matrix.of fun a b => g a.succ.castSucc b.succ.castSucc

theorem invMid_mul {g h : M5} (hg : ∀ i : Fin 5, i ≠ 0 → g i 0 = 0)
    (hh : ∀ j : Fin 5, j ≠ 4 → h 4 j = 0) : invMid (g * h) = invMid g * invMid h := by
  ext a b
  have hg1 := hg 1 (by decide)
  have hg2 := hg 2 (by decide)
  have hg3 := hg 3 (by decide)
  have hh1 := hh 1 (by decide)
  have hh2 := hh 2 (by decide)
  have hh3 := hh 3 (by decide)
  fin_cases a <;> fin_cases b <;>
    simp [invMid, Matrix.mul_apply, Fin.sum_univ_five, Fin.sum_univ_three, hg1, hg2, hg3, hh1,
      hh2, hh3]

theorem invMid_one : invMid 1 = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

@[expose] def invMidUnit {g : G52} (hg : g ∈ Subgroup.centralizer {invT0}) :
    GL (Fin 3) (ZMod 2) :=
  ⟨invMid g, invMid ((g⁻¹ : G52) : M5), by
    rw [← invMid_mul (inv_t0_shape hg).1 (inv_t0_shape (inv_mem hg)).2.1, ← Units.val_mul,
      mul_inv_cancel, Units.val_one, invMid_one], by
    rw [← invMid_mul (inv_t0_shape (inv_mem hg)).1 (inv_t0_shape hg).2.1, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, invMid_one]⟩

theorem inv_t0_decomp {g : G52} (hg : g ∈ Subgroup.centralizer {invT0}) :
    g = invAHom ⟨Multiplicative.ofAdd ![(g : M5) 1 4, (g : M5) 2 4, (g : M5) 3 4],
        invMidUnit hg⟩ *
      invEHom (Multiplicative.ofAdd ![(g : M5) 0 1, (g : M5) 0 2, (g : M5) 0 3, (g : M5) 0 4]) := by
  obtain ⟨hcol, hrow, h00, h44⟩ := inv_t0_shape hg
  refine Units.ext ?_
  rw [Units.val_mul, coe_invAHom, coe_invEHom]
  have c1 := hcol 1 (by decide)
  have c2 := hcol 2 (by decide)
  have c3 := hcol 3 (by decide)
  have c4 := hcol 4 (by decide)
  have r0 := hrow 0 (by decide)
  have r1 := hrow 1 (by decide)
  have r2 := hrow 2 (by decide)
  have r3 := hrow 3 (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [invAM, invEM, invMidUnit, invMid, Matrix.mul_apply, Fin.sum_univ_five, c1, c2, c3, c4,
      r1, r2, r3, h00, h44]

theorem inv_E_le : invE ≤ Subgroup.centralizer {invT0} := by
  have ht : invT0 ∈ invE := by
    refine ⟨Multiplicative.ofAdd ![0, 0, 0, 1], Units.ext ?_⟩
    rw [coe_invEHom]
    decide
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact inv_E_comm x hx _ ht

theorem inv_A_le : invA ≤ Subgroup.centralizer {invT0} := by
  rintro _ ⟨x, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_invAHom]
  simp only [invT0, coe_mk5]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [invAM, invT0M, Matrix.mul_apply, Fin.sum_univ_five]

theorem inv_E_inf_A : invE ⊓ invA = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨⟨a, rfl⟩, ⟨x, hx⟩⟩ := Subgroup.mem_inf.1 hg
  have h' := congrArg (fun g : G52 => (g : M5)) hx
  simp only [coe_invAHom, coe_invEHom] at h'
  have ha : a = 1 := by
    apply Multiplicative.toAdd.injective
    funext k
    have := congrFun (congrFun h' 0) k.succ
    fin_cases k <;> simpa [invAM, invEM] using this.symm
  rw [ha, map_one]
  exact Subgroup.one_mem _

theorem inv_A_sup_E : invA ⊔ invE = Subgroup.centralizer {invT0} := by
  refine le_antisymm (sup_le inv_A_le inv_E_le) fun g hg => ?_
  rw [inv_t0_decomp hg]
  exact mul_mem (Subgroup.mem_sup_left ⟨_, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)

theorem inv_centralizer_le_normalizer_E :
    Subgroup.centralizer {invT0} ≤ Subgroup.normalizer (invE : Set G52) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact inv_conj_mem_E (inv_t0_fix_e0 hh) (inv_t0_fix_e0 (inv_mem hh)) hx
  · intro hx
    have := inv_conj_mem_E (inv_t0_fix_e0 (inv_mem hh)) (by rw [inv_inv]; exact inv_t0_fix_e0 hh)
      hx
    rwa [show h⁻¹ * (h * x * h⁻¹) * h⁻¹⁻¹ = x by group] at this

theorem inv_card_sup {G : Type*} [Group G] {E A : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (E : Set G)) (hinf : E ⊓ A = ⊥) :
    Nat.card (E ⊔ A : Subgroup G) = Nat.card E * Nat.card A := by
  have hmul : ((E ⊔ A : Subgroup G) : Set G) = (E : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left E A hA
  let f : E × A → (E ⊔ A : Subgroup G) := fun x =>
    ⟨(x.1 : G) * x.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2)
      (Subgroup.mem_sup_right x.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨e, he⟩, ⟨a, ha⟩⟩ ⟨⟨e', he'⟩, ⟨a', ha'⟩⟩ h
      have h' : e * a = e' * a' := congrArg Subtype.val h
      have hm : e'⁻¹ * e ∈ E ⊓ A := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem he') he, ?_⟩
        have : e'⁻¹ * e = a' * a⁻¹ := by
          calc e'⁻¹ * e = e'⁻¹ * (e * a) * a⁻¹ := by group
            _ = e'⁻¹ * (e' * a') * a⁻¹ := by rw [h']
            _ = a' * a⁻¹ := by group
        rw [this]
        exact mul_mem ha' (inv_mem ha)
      rw [hinf, Subgroup.mem_bot] at hm
      have hee : e = e' := by
        calc e = e' * (e'⁻¹ * e) := by group
          _ = e' := by rw [hm, mul_one]
      subst hee
      have haa : a = a' := mul_left_cancel h'
      subst haa
      rfl
    · rintro ⟨g, hg⟩
      have hg' : g ∈ ((E ⊔ A : Subgroup G) : Set G) := hg
      rw [hmul] at hg'
      obtain ⟨e, he, a, ha, rfl⟩ := hg'
      exact ⟨(⟨e, he⟩, ⟨a, ha⟩), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]

theorem inv_card_centralizer_t0 : Nat.card (Subgroup.centralizer {invT0}) = 2 ^ 10 * 3 * 7 := by
  rw [← inv_A_sup_E, sup_comm,
    inv_card_sup (inv_A_le.trans inv_centralizer_le_normalizer_E) inv_E_inf_A, inv_card_E,
    inv_card_A]
  norm_num

end CFSG.GroupTheory.GL52
