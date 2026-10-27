module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Field.ZMod
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BinaryThreeSpaceFixedCodimensions
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.EvenSporadicStandard.J1Std

open Subgroup

theorem exists_pow_or_pow_mul_of_mem_closure_dihedral {K : Type*} [Group K] {a b : K}
    (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 4 = 1) {x : K}
    (hx : x ∈ Subgroup.closure {a, b}) :
    ∃ n : ℕ, x = (a * b) ^ n ∨ x = (a * b) ^ n * a := by
  set c : K := a * b with hc
  have hac : a * c * a = c ^ 3 := by
    have h1 : c * (b * a) = 1 := by
      calc c * (b * a) = a * (b * b) * a := by rw [hc]; group
        _ = 1 := by rw [hb, mul_one, ha]
    have h2 : c ^ 3 = (c ^ 4) * c⁻¹ := by group
    have h3 : c⁻¹ = b * a := inv_eq_of_mul_eq_one_right h1
    rw [h2, hab, one_mul, h3, hc]
    calc a * (a * b) * a = (a * a) * b * a := by group
      _ = b * a := by rw [ha, one_mul]
  have hba : b = a * c := by rw [hc, ← mul_assoc, ha, one_mul]
  have haca : a * c * a * a = a * c := by rw [mul_assoc (a * c) a a, ha, mul_one]
  have hca : ∀ n : ℕ, a * c ^ n = c ^ (3 * n) * a := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a * c ^ (n + 1) = (a * c ^ n) * c := by group
        _ = c ^ (3 * n) * (a * c) := by rw [ih, mul_assoc]
        _ = c ^ (3 * n) * (a * c * a * a) := by rw [haca]
        _ = c ^ (3 * n) * c ^ 3 * a := by rw [hac, mul_assoc]
        _ = c ^ (3 * (n + 1)) * a := by rw [← pow_add]; ring_nf
  have hcaa : ∀ n : ℕ, a * (c ^ n * a) = c ^ (3 * n) := by
    intro n
    rw [← mul_assoc, hca, mul_assoc, ha, mul_one]
  have step : ∀ x ∈ ({a, b} : Set K), ∀ y : K, (∃ n : ℕ, y = c ^ n ∨ y = c ^ n * a) →
      ∃ n : ℕ, x * y = c ^ n ∨ x * y = c ^ n * a := by
    intro x hx y ⟨n, hn⟩
    rcases hx with rfl | hx
    · rcases hn with rfl | rfl
      · exact ⟨3 * n, Or.inr (hca n)⟩
      · exact ⟨3 * n, Or.inl (hcaa n)⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rcases hn with rfl | rfl
      · refine ⟨3 * (n + 1), Or.inr ?_⟩
        rw [hba, mul_assoc, ← pow_succ' c n, hca]
      · refine ⟨3 * (n + 1), Or.inl ?_⟩
        rw [hba, mul_assoc, ← mul_assoc c, ← pow_succ', ← mul_assoc, hca, mul_assoc, ha, mul_one]
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨0, Or.inl (by simp)⟩
  | mul_left x hx y hy ih => exact step x hx y ih
  | inv_mul_cancel x hx y hy ih =>
    have hxinv : x⁻¹ = x := by
      rcases hx with rfl | hx
      · exact inv_eq_of_mul_eq_one_right ha
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact inv_eq_of_mul_eq_one_right hb
    rw [hxinv]
    exact step x hx y ih

theorem card_closure_le_of_dihedral {K : Type*} [Group K] [Finite K] {a b : K}
    (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 4 = 1) :
    Nat.card (Subgroup.closure {a, b}) ≤ 8 := by
  classical
  have hsub : ((Subgroup.closure {a, b} : Subgroup K) : Set K) ⊆
      ((Finset.univ.image (fun i : Fin 4 => (a * b) ^ (i : ℕ)) ∪
        Finset.univ.image (fun i : Fin 4 => (a * b) ^ (i : ℕ) * a) : Finset K) : Set K) := by
    intro x hx
    obtain ⟨n, hn | hn⟩ := exists_pow_or_pow_mul_of_mem_closure_dihedral ha hb hab hx
    · simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_union, Set.mem_range]
      left
      exact ⟨⟨n % 4, Nat.mod_lt _ (by norm_num)⟩, by rw [hn, pow_eq_pow_mod n hab]⟩
    · simp only [Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
        Set.mem_union, Set.mem_range]
      right
      exact ⟨⟨n % 4, Nat.mod_lt _ (by norm_num)⟩, by rw [hn, pow_eq_pow_mod n hab]⟩
  calc Nat.card (Subgroup.closure {a, b})
      = Set.ncard ((Subgroup.closure {a, b} : Subgroup K) : Set K) :=
        (Nat.card_coe_set_eq _).symm
    _ ≤ Set.ncard (((Finset.univ.image (fun i : Fin 4 => (a * b) ^ (i : ℕ)) ∪
        Finset.univ.image (fun i : Fin 4 => (a * b) ^ (i : ℕ) * a) : Finset K)) : Set K) :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (Finset.univ.image (fun i : Fin 4 => (a * b) ^ (i : ℕ)) ∪
        Finset.univ.image (fun i : Fin 4 => (a * b) ^ (i : ℕ) * a) : Finset K).card :=
        Set.ncard_coe_finset _
    _ ≤ 4 + 4 := by
        refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
        · exact (Finset.card_image_le).trans (by simp)
        · exact (Finset.card_image_le).trans (by simp)

theorem card_closure_eq_eight {G : Type*} [Group G] [Finite G] {a b : G}
    (ha : a * a = 1) (hb : b * b = 1) (hab : orderOf (a * b) = 4) :
    Nat.card (Subgroup.closure {a, b}) = 8 := by
  have hle := card_closure_le_of_dihedral ha hb (hab ▸ pow_orderOf_eq_one (a * b))
  set Q := Subgroup.closure {a, b} with hQ
  have hc : a * b ∈ Q := Subgroup.mul_mem _ (subset_closure (by simp)) (subset_closure (by simp))
  have hz : Subgroup.zpowers (a * b) ≤ Q := (Subgroup.zpowers_le).2 hc
  have hdvd : 4 ∣ Nat.card Q := by
    have := Subgroup.card_dvd_of_le hz
    rwa [Nat.card_zpowers, hab] at this
  have hpos : 0 < Nat.card Q := Nat.card_pos
  have h48 : Nat.card Q = 4 ∨ Nat.card Q = 8 := by omega
  rcases h48 with h4 | h8
  · exfalso
    have hEq : Subgroup.zpowers (a * b) = Q :=
      Subgroup.eq_of_le_of_card_ge hz (by rw [Nat.card_zpowers, hab, h4])
    have haQ : a ∈ Subgroup.zpowers (a * b) := hEq ▸ subset_closure (by simp)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp haQ
    have hcomm : Commute a (a * b) := by
      have := (Commute.refl (a * b)).zpow_left k
      rwa [hk] at this
    have h1 : b = a * b * a := by
      have := hcomm.eq
      rwa [← mul_assoc, ha, one_mul] at this
    have h2 : b * a = a * b := by
      calc b * a = (a * b * a) * a := by rw [← h1]
        _ = a * b := by rw [mul_assoc (a * b) a a, ha, mul_one]
    have h3 : (a * b) ^ 2 = 1 := by
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [sq]; group
        _ = a * (a * b) * b := by rw [h2]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, one_mul]
    have h4' := orderOf_dvd_of_pow_eq_one h3
    rw [hab] at h4'
    omega
  · exact h8

theorem exists_le_map_conj_of_isPGroup {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 168)
    {Q : Subgroup G} (hQ : Nat.card Q = 8) {H : Subgroup G} (hH : IsPGroup 2 H) :
    ∃ g : G, H ≤ Q.map (MulAut.conj g).toMonoidHom := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ Q.index := by
    intro h2d
    have h := Subgroup.card_mul_index Q
    rw [hQ, hG] at h
    omega
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hQ]; norm_num)
  let Q' : Sylow 2 G := hQp.toSylow hidx
  obtain ⟨S, hS⟩ := hH.exists_le_sylow
  have : Finite (Sylow 2 G) := Sylow.finite_of_finiteIndex Q'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q' S
  refine ⟨g, hS.trans ?_⟩
  have h1 : ((g • Q' : Sylow 2 G) : Subgroup G) = (S : Subgroup G) := by rw [hg]
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
  exact le_of_eq h1.symm

theorem exists_map_conj_eq_of_card {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 168)
    {P Q : Subgroup G} (hP : Nat.card P = 8) (hQ : Nat.card Q = 8) :
    ∃ g : G, P = Q.map (MulAut.conj g).toMonoidHom := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_isPGroup hG hQ
    (IsPGroup.of_card (n := 3) (by rw [hP]; norm_num) : IsPGroup 2 P)
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hg ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP, hQ]

theorem exists_dihedral_pair_of_card {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 168)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : orderOf (a * b) = 4)
    {P : Subgroup G} (hP : Nat.card P = 8) :
    ∃ α β : G, α ∈ P ∧ β ∈ P ∧ α * α = 1 ∧ β * β = 1 ∧ orderOf (α * β) = 4 ∧
      P ≤ Subgroup.closure {α, β} := by
  obtain ⟨g, hg⟩ := exists_map_conj_eq_of_card hG hP (card_closure_eq_eight ha hb hab)
  refine ⟨g * a * g⁻¹, g * b * g⁻¹, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg]
    exact Subgroup.mem_map_of_mem _ (subset_closure (by simp))
  · rw [hg]
    exact Subgroup.mem_map_of_mem _ (subset_closure (by simp))
  · calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha]; group
  · calc g * b * g⁻¹ * (g * b * g⁻¹) = g * (b * b) * g⁻¹ := by group
      _ = 1 := by rw [hb]; group
  · have h := (MulAut.conj g).orderOf_eq (a * b)
    rw [MulAut.conj_apply] at h
    rw [show g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ by group, h, hab]
  · rw [hg, MonoidHom.map_closure, Set.image_pair]
    exact le_rfl

theorem isConj_of_involutions_of_card {G : Type*} [Group G] [Finite G] (hG : Nat.card G = 168)
    {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : orderOf (a * b) = 4)
    (hba : IsConj a b) (hac : IsConj a ((a * b) ^ 2)) {s : G} (hs : s ≠ 1) (hs2 : s * s = 1) :
    IsConj a s := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hab4 : (a * b) ^ 4 = 1 := hab ▸ pow_orderOf_eq_one (a * b)
  have hs_ord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs
  have hzp : IsPGroup 2 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs_ord]; norm_num)
  obtain ⟨g, hg⟩ := exists_le_map_conj_of_isPGroup hG (card_closure_eq_eight ha hb hab) hzp
  obtain ⟨x, hxQ, hxs⟩ := Subgroup.mem_map.mp (hg (Subgroup.mem_zpowers s))
  have hxs' : (MulAut.conj g) x = s := hxs
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hs (by rw [← hxs', map_one])
  have hx2 : x * x = 1 := by
    apply (MulAut.conj g).injective
    rw [map_mul, hxs', hs2, map_one]
  have hinv : (a * b)⁻¹ = b * a := by
    rw [_root_.mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb]
  have hax : IsConj a x := by
    obtain ⟨n, hn | hn⟩ := exists_pow_or_pow_mul_of_mem_closure_dihedral ha hb hab4 hxQ
    · rw [pow_eq_pow_mod n hab4] at hn
      have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
      generalize n % 4 = r at hn hr
      subst hn
      have h4 : 4 ∣ r + r := by
        have := orderOf_dvd_of_pow_eq_one (show (a * b) ^ (r + r) = 1 by
          rw [pow_add]; exact hx2)
        rwa [hab] at this
      have hr' : r = 0 ∨ r = 2 := by omega
      rcases hr' with rfl | rfl
      · exact absurd (pow_zero _) hx1
      · exact hac
    · rw [pow_eq_pow_mod n hab4] at hn
      have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
      generalize n % 4 = r at hn hr
      subst hn
      interval_cases r
      · exact isConj_iff.mpr ⟨1, by simp⟩
      · have h1 : IsConj b ((a * b) ^ 1 * a) := by
          rw [isConj_iff]
          exact ⟨a, by rw [inv_eq_of_mul_eq_one_right ha, pow_one]⟩
        exact hba.trans h1
      · rw [isConj_iff]
        refine ⟨a * b, ?_⟩
        rw [hinv, sq]
        group
      · have h3 : (a * b) ^ 3 * a = b := by
          have : (a * b) ^ 3 = b * a := by
            rw [← hinv]
            exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hab4)
          rw [this, mul_assoc, ha, mul_one]
        rw [h3]
        exact hba
  exact hax.trans (isConj_iff.mpr ⟨g, hxs'⟩)

private def mulAutEquivLinearEquiv (E : Type*) [CommGroup E] [Module (ZMod 2) (Additive E)] :
    MulAut E ≃* (Additive E ≃ₗ[ZMod 2] Additive E) where
  toFun φ := { MulEquiv.toAdditive φ with map_smul' := ZMod.map_smul (MulEquiv.toAdditive φ) }
  invFun L := MulEquiv.toAdditive.symm L.toAddEquiv
  left_inv φ := by ext; rfl
  right_inv L := by ext; rfl
  map_mul' φ ψ := by ext; rfl

private noncomputable def mulAutEquivGL (E : Type*) [CommGroup E] [Module (ZMod 2) (Additive E)]
    (b : Module.Basis (Fin 3) (ZMod 2) (Additive E)) :
    MulAut E ≃* GL (Fin 3) (ZMod 2) :=
  (mulAutEquivLinearEquiv E).trans
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.trans
      (Matrix.GeneralLinearGroup.toLin' b).symm)

theorem nonempty_mulAut_equiv_GL {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (hcomm : ∀ a b : E, a * b = b * a) (hsq : ∀ a : E, a * a = 1) :
    Nonempty (MulAut E ≃* GL (Fin 3) (ZMod 2)) := by
  let _ : CommGroup E := { ‹Group E› with mul_comm := hcomm }
  let _ : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]
    exact hsq (Additive.toMul x))
  have hfin : Module.finrank (ZMod 2) (Additive E) = 3 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    rw [Nat.card_zmod, show Nat.card (Additive E) = 8 from hE] at h
    exact Nat.pow_right_injective (le_refl 2) (h.symm.trans (by norm_num))
  exact ⟨mulAutEquivGL E (Module.finBasisOfFinrankEq (ZMod 2) (Additive E) hfin)⟩

private theorem card_GL_three_two : Nat.card (GL (Fin 3) (ZMod 2)) = 168 :=
  CFSG.ProperTwoGeneratedCore.BinaryThreeSpace.FixedCodim.card_GL3

private def glA : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], !![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide, by decide⟩

private def glB : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], !![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide, by decide⟩

private def glC : GL (Fin 3) (ZMod 2) :=
  ⟨!![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0], by decide, by decide⟩

private def glD : GL (Fin 3) (ZMod 2) :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], !![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide, by decide⟩

private theorem glA_mul_self : glA * glA = 1 := Units.ext (by decide)

private theorem glB_mul_self : glB * glB = 1 := Units.ext (by decide)

private theorem orderOf_glA_mul_glB : orderOf (glA * glB) = 4 := by
  have h : orderOf (glA * glB) = 2 ^ (1 + 1) := by
    apply orderOf_eq_prime_pow
    · intro hx
      have := congrArg (fun g : GL (Fin 3) (ZMod 2) => (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) hx
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one] at this
      revert this
      decide
    · apply Units.ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_one]
      decide
  simpa using h

private theorem glC_conj : glC * glA * glC⁻¹ = glB := by decide

private theorem glD_conj : glD * glA * glD⁻¹ = (glA * glB) ^ 2 := by decide

theorem card_mulAut_of_elemAbelian_eight {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (hcomm : ∀ a b : E, a * b = b * a) (hsq : ∀ a : E, a * a = 1) :
    Nat.card (MulAut E) = 168 := by
  obtain ⟨Φ⟩ := nonempty_mulAut_equiv_GL hE hcomm hsq
  rw [Nat.card_congr Φ.toEquiv, card_GL_three_two]

private theorem exists_dihedral_data {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (hcomm : ∀ a b : E, a * b = b * a) (hsq : ∀ a : E, a * a = 1) :
    ∃ a b : MulAut E, a * a = 1 ∧ b * b = 1 ∧ orderOf (a * b) = 4 ∧ IsConj a b ∧
      IsConj a ((a * b) ^ 2) := by
  obtain ⟨Φ⟩ := nonempty_mulAut_equiv_GL hE hcomm hsq
  refine ⟨Φ.symm glA, Φ.symm glB, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_mul Φ.symm, glA_mul_self, map_one]
  · rw [← map_mul Φ.symm, glB_mul_self, map_one]
  · rw [← map_mul Φ.symm, MulEquiv.orderOf_eq, orderOf_glA_mul_glB]
  · refine isConj_iff.mpr ⟨Φ.symm glC, ?_⟩
    simpa only [map_mul, map_inv] using congrArg Φ.symm glC_conj
  · refine isConj_iff.mpr ⟨Φ.symm glD, ?_⟩
    simpa only [map_mul, map_inv, map_pow] using congrArg Φ.symm glD_conj

theorem exists_dihedral_pair {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (hcomm : ∀ a b : E, a * b = b * a) (hsq : ∀ a : E, a * a = 1)
    {P : Subgroup (MulAut E)} (hP : Nat.card P = 8) :
    ∃ α β : MulAut E, α ∈ P ∧ β ∈ P ∧ α * α = 1 ∧ β * β = 1 ∧ orderOf (α * β) = 4 ∧
      P ≤ Subgroup.closure {α, β} := by
  obtain ⟨a, b, ha, hb, hab, -, -⟩ := exists_dihedral_data hE hcomm hsq
  have hG := card_mulAut_of_elemAbelian_eight hE hcomm hsq
  have : Finite (MulAut E) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  exact exists_dihedral_pair_of_card hG ha hb hab hP

theorem isConj_of_involutions {E : Type*} [Group E] [Finite E] (hE : Nat.card E = 8)
    (hcomm : ∀ a b : E, a * b = b * a) (hsq : ∀ a : E, a * a = 1)
    {α β : MulAut E} (hα : α ≠ 1) (hβ : β ≠ 1) (hα2 : α * α = 1) (hβ2 : β * β = 1) :
    IsConj α β := by
  obtain ⟨a, b, ha, hb, hab, hba, hac⟩ := exists_dihedral_data hE hcomm hsq
  have hG := card_mulAut_of_elemAbelian_eight hE hcomm hsq
  have : Finite (MulAut E) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  exact (isConj_of_involutions_of_card hG ha hb hab hba hac hα hα2).symm.trans
    (isConj_of_involutions_of_card hG ha hb hab hba hac hβ hβ2)

end CFSG.EvenSporadicStandard.J1Std
