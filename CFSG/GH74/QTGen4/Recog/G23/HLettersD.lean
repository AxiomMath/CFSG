module

public import CFSG.GH74.QTGen4.Recog.G23.HLetters
public import CFSG.GH74.QTGen4.Recog.G23.HLettersC
public meta import CFSG.GH74.QTGen4.Recog.G23.HSL
public meta import Mathlib.Data.ZMod.Defs
public meta import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.GH74.QTGen4.Recog.G23

open CFSG.Quasithin.G23Type
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem G23One.conj_two_mem_one {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) {a b : G}
    (hb : b ∈ H₂) (ha : a ∈ H₁) : b * a * b⁻¹ ∈ H₁ :=
  ((Subgroup.mem_normalizer_iff).mp (hH.normal_one (hH.le_two hb)) a).mp ha

theorem G23One.mem_sup_iff {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) {k : G} :
    k ∈ H₁ ⊔ H₂ ↔ ∃ a ∈ H₁, ∃ b ∈ H₂, k = a * b := by
  let P : Subgroup G :=
    { carrier := {g | ∃ a ∈ H₁, ∃ b ∈ H₂, g = a * b}
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * (b * a' * b⁻¹), H₁.mul_mem ha (G23One.conj_two_mem_one hH hb ha'), b * b',
          H₂.mul_mem hb hb', ?_⟩
        group
      one_mem' := ⟨1, H₁.one_mem, 1, H₂.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hc := G23One.conj_two_mem_one hH (H₂.inv_mem hb) (H₁.inv_mem ha)
        rw [inv_inv] at hc
        exact ⟨b⁻¹ * a⁻¹ * b, hc, b⁻¹, H₂.inv_mem hb, by group⟩ }
  have hle : H₁ ⊔ H₂ ≤ P := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨a, ha, 1, H₂.one_mem, by simp⟩
    · intro b hb
      exact ⟨1, H₁.one_mem, b, hb, by simp⟩
  constructor
  · intro hk
    exact hle hk
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem _ ((le_sup_left : H₁ ≤ H₁ ⊔ H₂) ha)
      ((le_sup_right : H₂ ≤ H₁ ⊔ H₂) hb)

noncomputable def cpMap {H₁ H₂ : Subgroup G} (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (p : M2 × M2) : G :=
  if h : p.1.det = 1 ∧ p.2.det = 1 then
    ((ψ₁.symm ⟨p.1, h.1⟩ : ↥H₁) : G) * ((ψ₂.symm ⟨p.2, h.2⟩ : ↥H₂) : G)
  else 1

theorem cpMap_apply_eq {H₁ H₂ : Subgroup G}
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (a : ↥H₁) (b : ↥H₂) :
    cpMap ψ₁ ψ₂ ((ψ₁ a).1, (ψ₂ b).1) = (a : G) * (b : G) := by
  have hd : (ψ₁ a).1.det = 1 ∧ (ψ₂ b).1.det = 1 := ⟨(ψ₁ a).2, (ψ₂ b).2⟩
  unfold cpMap
  dsimp only
  split_ifs
  show ((ψ₁.symm (ψ₁ a) : ↥H₁) : G) * ((ψ₂.symm (ψ₂ b) : ↥H₂) : G) = (a : G) * (b : G)
  rw [MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]

theorem G23One.inf_data {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) :
    ∃ z : G, z ∈ H₁ ∧ z ∈ H₂ ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ y ∈ H₁ ⊓ H₂, y = 1 ∨ y = z := by
  obtain ⟨z, hzmem, hz1, huniq⟩ := G23One.exists_unique_inf hH
  exact ⟨z, (Subgroup.mem_inf.mp hzmem).1, (Subgroup.mem_inf.mp hzmem).2, hz1,
    G23One.sq_inf hH hzmem, huniq⟩

theorem sq_map_mul {K : Subgroup G}
    (ψ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (x : ↥K) :
    (ψ x).1 * (ψ x).1 = (ψ (x * x)).1 := by
  simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul]

theorem G23One.sq_of_mat {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂)
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) {a b : G} (ha : a ∈ H₁)
    (hb : b ∈ H₂)
    (hm : ((ψ₁ ⟨a, ha⟩).1 * (ψ₁ ⟨a, ha⟩).1 = 1 ∧ (ψ₂ ⟨b, hb⟩).1 * (ψ₂ ⟨b, hb⟩).1 = 1) ∨
      ((ψ₁ ⟨a, ha⟩).1 * (ψ₁ ⟨a, ha⟩).1 = -1 ∧ (ψ₂ ⟨b, hb⟩).1 * (ψ₂ ⟨b, hb⟩).1 = -1)) :
    (a * b) * (a * b) = 1 := by
  obtain ⟨z, hzH₁, hzH₂, hz1, hz2, -⟩ := G23One.inf_data hH
  have hzA : (ψ₁ ⟨z, hzH₁⟩).1 = -1 := by
    have hzz : (⟨z, hzH₁⟩ : ↥H₁) * ⟨z, hzH₁⟩ = 1 :=
      Subtype.ext (show z * z = 1 by rw [← pow_two]; exact hz2)
    have hAA : ψ₁ ⟨z, hzH₁⟩ * ψ₁ ⟨z, hzH₁⟩ = 1 := by rw [← map_mul, hzz, map_one]
    have hA1 : ψ₁ ⟨z, hzH₁⟩ ≠ 1 := fun h =>
      hz1 (congrArg Subtype.val (ψ₁.injective (h.trans (map_one ψ₁).symm)))
    exact sl_unique_invol (ψ₁ ⟨z, hzH₁⟩).1 (ψ₁ ⟨z, hzH₁⟩).2
      (congrArg Subtype.val hAA) (fun h => hA1 (Subtype.ext h))
  have hzB : (ψ₂ ⟨z, hzH₂⟩).1 = -1 := by
    have hzz : (⟨z, hzH₂⟩ : ↥H₂) * ⟨z, hzH₂⟩ = 1 :=
      Subtype.ext (show z * z = 1 by rw [← pow_two]; exact hz2)
    have hAA : ψ₂ ⟨z, hzH₂⟩ * ψ₂ ⟨z, hzH₂⟩ = 1 := by rw [← map_mul, hzz, map_one]
    have hA1 : ψ₂ ⟨z, hzH₂⟩ ≠ 1 := fun h =>
      hz1 (congrArg Subtype.val (ψ₂.injective (h.trans (map_one ψ₂).symm)))
    exact sl_unique_invol (ψ₂ ⟨z, hzH₂⟩).1 (ψ₂ ⟨z, hzH₂⟩).2
      (congrArg Subtype.val hAA) (fun h => hA1 (Subtype.ext h))
  have hone₁ : (ψ₁ (1 : ↥H₁)).1 = 1 := by simp
  have hone₂ : (ψ₂ (1 : ↥H₂)).1 = 1 := by simp
  have e : (a * b) * (a * b) = a * a * (b * b) := by
    have hc := G23One.comm_one_two hH ha hb
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hc]
      _ = a * a * (b * b) := by group
  rcases hm with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hxx : (⟨a, ha⟩ : ↥H₁) * ⟨a, ha⟩ = 1 :=
      ψ₁.injective (Subtype.ext (((sq_map_mul ψ₁ ⟨a, ha⟩).symm.trans h1).trans hone₁.symm))
    have hyy : (⟨b, hb⟩ : ↥H₂) * ⟨b, hb⟩ = 1 :=
      ψ₂.injective (Subtype.ext (((sq_map_mul ψ₂ ⟨b, hb⟩).symm.trans h2).trans hone₂.symm))
    have haa : a * a = 1 := congrArg Subtype.val hxx
    have hbb : b * b = 1 := congrArg Subtype.val hyy
    rw [e, haa, hbb, one_mul]
  · have hxz : (⟨a, ha⟩ : ↥H₁) * ⟨a, ha⟩ = ⟨z, hzH₁⟩ :=
      ψ₁.injective (Subtype.ext (((sq_map_mul ψ₁ ⟨a, ha⟩).symm.trans h1).trans hzA.symm))
    have hyz : (⟨b, hb⟩ : ↥H₂) * ⟨b, hb⟩ = ⟨z, hzH₂⟩ :=
      ψ₂.injective (Subtype.ext (((sq_map_mul ψ₂ ⟨b, hb⟩).symm.trans h2).trans hzB.symm))
    have haa : a * a = z := congrArg Subtype.val hxz
    have hbb : b * b = z := congrArg Subtype.val hyz
    rw [e, haa, hbb, ← pow_two, hz2]

theorem invol_val_neg {K : Subgroup G} (ψ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    {z : G} (hzK : z ∈ K) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : (ψ ⟨z, hzK⟩).1 = -1 := by
  have hzz : (⟨z, hzK⟩ : ↥K) * ⟨z, hzK⟩ = 1 :=
    Subtype.ext (show z * z = 1 by rw [← pow_two]; exact hz2)
  have hAA : ψ ⟨z, hzK⟩ * ψ ⟨z, hzK⟩ = 1 := by rw [← map_mul, hzz, map_one]
  have hA1 : ψ ⟨z, hzK⟩ ≠ 1 := fun h =>
    hz1 (congrArg Subtype.val (ψ.injective (h.trans (map_one ψ).symm)))
  exact sl_unique_invol (ψ ⟨z, hzK⟩).1 (ψ ⟨z, hzK⟩).2
    (congrArg Subtype.val hAA) (fun h => hA1 (Subtype.ext h))

theorem G23One.mat_of_sq {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂)
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) {a b : G} (ha : a ∈ H₁)
    (hb : b ∈ H₂) (h : (a * b) * (a * b) = 1) :
    ((ψ₁ ⟨a, ha⟩).1 * (ψ₁ ⟨a, ha⟩).1 = 1 ∧ (ψ₂ ⟨b, hb⟩).1 * (ψ₂ ⟨b, hb⟩).1 = 1) ∨
      ((ψ₁ ⟨a, ha⟩).1 * (ψ₁ ⟨a, ha⟩).1 = -1 ∧ (ψ₂ ⟨b, hb⟩).1 * (ψ₂ ⟨b, hb⟩).1 = -1) := by
  obtain ⟨z, hzH₁, hzH₂, hz1, hz2, huniq⟩ := G23One.inf_data hH
  have hzA : (ψ₁ ⟨z, hzH₁⟩).1 = -1 := invol_val_neg ψ₁ hzH₁ hz2 hz1
  have hzB : (ψ₂ ⟨z, hzH₂⟩).1 = -1 := invol_val_neg ψ₂ hzH₂ hz2 hz1
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hz2)
  have e : (a * b) * (a * b) = a * a * (b * b) := by
    have hc := G23One.comm_one_two hH ha hb
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hc]
      _ = a * a * (b * b) := by group
  have h' : a * a * (b * b) = 1 := by rw [← e]; exact h
  have hab' : a * a = (b * b)⁻¹ := eq_inv_of_mul_eq_one_left h'
  have hmem : a * a ∈ H₁ ⊓ H₂ :=
    ⟨H₁.mul_mem ha ha, by rw [hab']; exact H₂.inv_mem (H₂.mul_mem hb hb)⟩
  rcases huniq (a * a) hmem with h1 | h1
  · have hbb : b * b = 1 := inv_eq_one.mp (hab'.symm.trans h1)
    have hxx : (⟨a, ha⟩ : ↥H₁) * ⟨a, ha⟩ = 1 := Subtype.ext h1
    have hyy : (⟨b, hb⟩ : ↥H₂) * ⟨b, hb⟩ = 1 := Subtype.ext hbb
    left
    constructor
    · simp [sq_map_mul ψ₁ ⟨a, ha⟩, hxx]
    · simp [sq_map_mul ψ₂ ⟨b, hb⟩, hyy]
  · have hbb : b * b = z := by
      rw [inv_eq_iff_eq_inv.mp (hab'.symm.trans h1), hzinv]
    have hxz : (⟨a, ha⟩ : ↥H₁) * ⟨a, ha⟩ = ⟨z, hzH₁⟩ := Subtype.ext h1
    have hyz : (⟨b, hb⟩ : ↥H₂) * ⟨b, hb⟩ = ⟨z, hzH₂⟩ := Subtype.ext hbb
    right
    constructor
    · rw [sq_map_mul ψ₁ ⟨a, ha⟩, hxz]
      exact hzA
    · rw [sq_map_mul ψ₂ ⟨b, hb⟩, hyz]
      exact hzB

theorem G23One.good_iff {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂)
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) {a b : G} (ha : a ∈ H₁)
    (hb : b ∈ H₂) :
    (a * b) * (a * b) = 1 ↔
      ((ψ₁ ⟨a, ha⟩).1.det = 1 ∧ (ψ₂ ⟨b, hb⟩).1.det = 1 ∧
        (((ψ₁ ⟨a, ha⟩).1 * (ψ₁ ⟨a, ha⟩).1 = 1 ∧ (ψ₂ ⟨b, hb⟩).1 * (ψ₂ ⟨b, hb⟩).1 = 1) ∨
          ((ψ₁ ⟨a, ha⟩).1 * (ψ₁ ⟨a, ha⟩).1 = -1 ∧ (ψ₂ ⟨b, hb⟩).1 * (ψ₂ ⟨b, hb⟩).1 = -1))) := by
  constructor
  · intro h
    exact ⟨(ψ₁ ⟨a, ha⟩).2, (ψ₂ ⟨b, hb⟩).2, G23One.mat_of_sq hH ψ₁ ψ₂ ha hb h⟩
  · rintro ⟨-, -, hm⟩
    exact G23One.sq_of_mat hH ψ₁ ψ₂ ha hb hm

theorem neg_symm_eq {K : Subgroup G} (ψ : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    {x w : ↥K} (hw : (ψ w).1 = -1) {s s' : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)}
    (hx : ψ x = s) (hs' : s'.1 = -s.1) :
    ((ψ.symm s' : ↥K) : G) = (x : G) * (w : G) := by
  have h : ψ.symm s' = x * w := by
    apply ψ.injective
    rw [MulEquiv.apply_symm_apply, map_mul]
    apply Subtype.ext
    rw [hs', Matrix.SpecialLinearGroup.coe_mul, hx, hw]
    exact (mul_neg_one _).symm
  rw [h, Subgroup.coe_mul]

theorem cpMap_eq_of {H₁ H₂ : Subgroup G}
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (p : M2 × M2)
    (h : p.1.det = 1 ∧ p.2.det = 1) (s t : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (hs : s.1 = p.1) (ht : t.1 = p.2) :
    cpMap ψ₁ ψ₂ p = ((ψ₁.symm s : ↥H₁) : G) * ((ψ₂.symm t : ↥H₂) : G) := by
  have e1 : s = ⟨p.1, h.1⟩ := Subtype.ext hs
  have e2 : t = ⟨p.2, h.2⟩ := Subtype.ext ht
  subst e1 e2
  unfold cpMap
  split_ifs
  rfl

theorem mul_cancel_central (a b z : G) (hzb : z * b = b * z) (hz2 : z * z = 1) :
    (a * z) * (b * z) = a * b := by
  calc a * z * (b * z) = a * (z * b) * z := by group
    _ = a * (b * z) * z := by rw [hzb]
    _ = a * b * (z * z) := by group
    _ = a * b := by rw [hz2, mul_one]

theorem cpMap_neg_eq {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂)
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) {A B : M2}
    (hA : A.det = 1) (hB : B.det = 1) (hA' : (-A).det = 1) (hB' : (-B).det = 1) :
    cpMap ψ₁ ψ₂ (-A, -B) = cpMap ψ₁ ψ₂ (A, B) := by
  obtain ⟨z, hzH₁, hzH₂, hz1, hz2, -⟩ := G23One.inf_data hH
  have hzA : (ψ₁ ⟨z, hzH₁⟩).1 = -1 := invol_val_neg ψ₁ hzH₁ hz2 hz1
  have hzB : (ψ₂ ⟨z, hzH₂⟩).1 = -1 := invol_val_neg ψ₂ hzH₂ hz2 hz1
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  obtain ⟨sA, hsA⟩ : ∃ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), s.1 = A := ⟨⟨A, hA⟩, rfl⟩
  obtain ⟨sB, hsB⟩ : ∃ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), s.1 = B := ⟨⟨B, hB⟩, rfl⟩
  obtain ⟨sA', hsA'⟩ : ∃ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), s.1 = -A := ⟨⟨-A, hA'⟩, rfl⟩
  obtain ⟨sB', hsB'⟩ : ∃ s : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), s.1 = -B := ⟨⟨-B, hB'⟩, rfl⟩
  have h1 := neg_symm_eq ψ₁ hzA (ψ₁.apply_symm_apply sA) (s' := sA') (by rw [hsA', hsA])
  have h2 := neg_symm_eq ψ₂ hzB (ψ₂.apply_symm_apply sB) (s' := sB') (by rw [hsB', hsB])
  have hbC : ((ψ₂.symm sB : ↥H₂) : G) ∈
      Subgroup.centralizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := by
    rw [← hH.eq_centralizer]
    exact hH.le_two (ψ₂.symm sB).2
  have hzb : z * ((ψ₂.symm sB : ↥H₂) : G) = ((ψ₂.symm sB : ↥H₂) : G) * z :=
    Subgroup.mem_centralizer_iff.mp hbC z (Subgroup.mem_inf.mpr ⟨hzH₁, hzH₂⟩)
  have e1 : cpMap ψ₁ ψ₂ (-A, -B) = ((ψ₁.symm sA' : ↥H₁) : G) *
      ((ψ₂.symm sB' : ↥H₂) : G) := cpMap_eq_of ψ₁ ψ₂ (-A, -B) ⟨hA', hB'⟩ sA' sB' hsA' hsB'
  have e2 : cpMap ψ₁ ψ₂ (A, B) = ((ψ₁.symm sA : ↥H₁) : G) *
      ((ψ₂.symm sB : ↥H₂) : G) := cpMap_eq_of ψ₁ ψ₂ (A, B) ⟨hA, hB⟩ sA sB hsA hsB
  rw [e1, e2, h1, h2]
  exact mul_cancel_central _ _ z hzb hzz

@[irreducible] def sqPairs : Finset (M2 × M2) := Finset.univ.filter (fun p : M2 × M2 => p.1.det = 1 ∧
    p.2.det = 1 ∧ ((p.1 * p.1 = 1 ∧ p.2 * p.2 = 1) ∨ (p.1 * p.1 = -1 ∧ p.2 * p.2 = -1)))

theorem mem_sqPairs {p : M2 × M2} : p ∈ sqPairs ↔ p.1.det = 1 ∧ p.2.det = 1 ∧
    ((p.1 * p.1 = 1 ∧ p.2 * p.2 = 1) ∨ (p.1 * p.1 = -1 ∧ p.2 * p.2 = -1)) := by
  unfold sqPairs
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]

theorem card_sqPairs : sqPairs.card = 40 := by
  unfold sqPairs
  exact card_sq_pairs

theorem M2_neg_facts : ∀ A : M2, A.det = 1 → (-A).det = 1 ∧ -A ≠ A := by
  decide +kernel

theorem sqPairs_neg {p : M2 × M2} (hp : p ∈ sqPairs) : (-p.1, -p.2) ∈ sqPairs := by
  rw [mem_sqPairs] at hp ⊢
  obtain ⟨hA, hB, h⟩ := hp
  refine ⟨(M2_neg_facts _ hA).1, (M2_neg_facts _ hB).1, ?_⟩
  have hn : ∀ A : M2, -A * -A = A * A := fun A => neg_mul_neg A A
  show (-p.1 * -p.1 = 1 ∧ -p.2 * -p.2 = 1) ∨ (-p.1 * -p.1 = -1 ∧ -p.2 * -p.2 = -1)
  rw [hn p.1, hn p.2]
  exact h

theorem sqPairs_ne_neg {p : M2 × M2} (hp : p ∈ sqPairs) : p ≠ (-p.1, -p.2) := by
  rw [mem_sqPairs] at hp
  intro h
  exact (M2_neg_facts _ hp.1).2 (congrArg Prod.fst h).symm

theorem sqPairs_fibre_two [DecidableEq G] {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂)
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) {p : M2 × M2} (hp : p ∈ sqPairs) :
    2 ≤ (sqPairs.filter (fun x => cpMap ψ₁ ψ₂ x = cpMap ψ₁ ψ₂ p)).card := by
  have hq : (-p.1, -p.2) ∈ sqPairs.filter (fun x => cpMap ψ₁ ψ₂ x = cpMap ψ₁ ψ₂ p) := by
    rw [Finset.mem_filter]
    refine ⟨sqPairs_neg hp, ?_⟩
    rw [mem_sqPairs] at hp
    exact cpMap_neg_eq hH ψ₁ ψ₂ hp.1 hp.2.1 (M2_neg_facts _ hp.1).1 (M2_neg_facts _ hp.2.1).1
  have hp' : p ∈ sqPairs.filter (fun x => cpMap ψ₁ ψ₂ x = cpMap ψ₁ ψ₂ p) :=
    Finset.mem_filter.mpr ⟨hp, rfl⟩
  have h1 := Finset.one_lt_card.mpr ⟨p, hp', (-p.1, -p.2), hq, sqPairs_ne_neg hp⟩
  omega

@[irreducible] noncomputable def cpImage [DecidableEq G] {H₁ H₂ : Subgroup G}
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) : Finset G :=
  sqPairs.image (fun p => cpMap ψ₁ ψ₂ p)

theorem mem_cpImage [DecidableEq G] {H₁ H₂ : Subgroup G}
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) {k : G} :
    k ∈ cpImage ψ₁ ψ₂ ↔ ∃ p ∈ sqPairs, cpMap ψ₁ ψ₂ p = k := by
  unfold cpImage
  exact Finset.mem_image

theorem card_cpImage_le [DecidableEq G] {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂)
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (cpImage ψ₁ ψ₂).card ≤ 20 := by
  have hb := card_image_mul_two_le sqPairs (fun p => cpMap ψ₁ ψ₂ p) (fun y hy => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
    exact sqPairs_fibre_two hH ψ₁ ψ₂ hp)
  rw [card_sqPairs] at hb
  unfold cpImage
  omega

theorem one_mem_cpImage [DecidableEq G] {H₁ H₂ : Subgroup G}
    (ψ₁ : ↥H₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
    (ψ₂ : ↥H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) :
    (1 : G) ∈ cpImage ψ₁ ψ₂ := by
  rw [mem_cpImage]
  refine ⟨((ψ₁ 1).1, (ψ₂ 1).1), ?_, ?_⟩
  · rw [mem_sqPairs]
    simp
  · rw [cpMap_apply_eq]
    simp

theorem G23One.card_invol_sup_aux [DecidableEq G] {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) :
    Nat.card {k : ↥(H₁ ⊔ H₂) // orderOf k = 2} ≤ 19 := by
  obtain ⟨ψ₁⟩ := hH.iso_one
  obtain ⟨ψ₂⟩ := hH.iso_two
  have hmem : ∀ k : {k : ↥(H₁ ⊔ H₂) // orderOf k = 2}, (k.1 : G) ∈ (cpImage ψ₁ ψ₂).erase 1 := by
    intro k
    have ho : orderOf (k.1 : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact k.2
    have hk2 : (k.1 : G) * (k.1 : G) = 1 := by
      have h := pow_orderOf_eq_one (k.1 : G)
      rw [ho, pow_two] at h
      exact h
    have hk1 : (k.1 : G) ≠ 1 := by
      intro h
      rw [h, orderOf_one] at ho
      norm_num at ho
    obtain ⟨a, ha, b, hb, hab⟩ := (G23One.mem_sup_iff hH).mp k.1.2
    rw [Finset.mem_erase]
    refine ⟨hk1, ?_⟩
    rw [mem_cpImage]
    refine ⟨((ψ₁ ⟨a, ha⟩).1, (ψ₂ ⟨b, hb⟩).1), ?_, ?_⟩
    · rw [mem_sqPairs]
      exact (G23One.good_iff hH ψ₁ ψ₂ ha hb).mp (by rw [← hab]; exact hk2)
    · rw [cpMap_apply_eq]
      exact hab.symm
  have hinj : Function.Injective
      (fun k : {k : ↥(H₁ ⊔ H₂) // orderOf k = 2} => (⟨(k.1 : G), hmem k⟩ : ↥((cpImage ψ₁ ψ₂).erase 1))) := by
    intro k₁ k₂ h
    have h' : (k₁.1 : G) = (k₂.1 : G) :=
      congrArg (fun x : ↥((cpImage ψ₁ ψ₂).erase 1) => (x : G)) h
    exact Subtype.ext (Subtype.ext h')
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard, Finset.card_erase_of_mem (one_mem_cpImage ψ₁ ψ₂)] at hle
  have hc := card_cpImage_le hH ψ₁ ψ₂
  omega

theorem G23One.card_invol_sup_le {H H₁ H₂ : Subgroup G} (hH : G23One H H₁ H₂) :
    Nat.card {k : ↥(H₁ ⊔ H₂) // orderOf k = 2} ≤ 19 := by
  classical
  exact G23One.card_invol_sup_aux hH

end CFSG.GH74.QTGen4.Recog.G23
