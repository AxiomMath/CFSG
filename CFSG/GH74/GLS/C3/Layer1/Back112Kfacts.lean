module

public import CFSG.GH74.GLS.C3.Layer1.Back113A
public import CFSG.GH74.GLS.IVK.L2.Lemma19Aux

public section

namespace CFSG.GH74.GLS.C3.Layer1.Back

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS

open Equiv Perm in
theorem cycleType_involution_alt7 (σ : alternatingGroup (Fin 7)) (hσ : orderOf σ = 2) :
    (σ : Perm (Fin 7)).cycleType = {2, 2} := by
  obtain ⟨s, hs'⟩ : ∃ s : Perm (Fin 7), s = (σ : Perm (Fin 7)) := ⟨_, rfl⟩
  rw [← hs']
  have hs2 : orderOf s = 2 := by
    rw [hs']; rw [Subgroup.orderOf_coe]; exact hσ
  have hsign : Perm.sign s = 1 := by rw [hs']; exact mem_alternatingGroup.1 σ.2
  have hall : ∀ n ∈ s.cycleType, n = 2 := by
    intro n hn
    have h1 : n ∣ orderOf s := Perm.dvd_of_mem_cycleType hn
    rw [hs2] at h1
    have h2 : 2 ≤ n := Perm.two_le_of_mem_cycleType hn
    exact (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) h1) h2)
  have hrep : s.cycleType = Multiset.replicate (Multiset.card s.cycleType) 2 :=
    Multiset.eq_replicate_of_mem hall
  obtain ⟨k, hk⟩ : ∃ k, k = Multiset.card s.cycleType := ⟨_, rfl⟩
  rw [← hk] at hrep
  have hsum : s.cycleType.sum = 2 * k := by
    rw [hrep]; simp [Multiset.sum_replicate, mul_comm]
  have hsupp : s.support.card = 2 * k := by
    rw [← Perm.sum_cycleType]; exact hsum
  have hle : s.support.card ≤ 7 := by
    calc s.support.card ≤ Fintype.card (Fin 7) := Finset.card_le_univ _
      _ = 7 := by simp
  have hk3 : k ≤ 3 := by omega
  have hk0 : k ≠ 0 := by
    intro h0
    have : s.cycleType = 0 := by rw [hrep, h0]; rfl
    have hs1 : s = 1 := Perm.cycleType_eq_zero.1 this
    rw [hs1, orderOf_one] at hs2
    omega
  have hsg : Perm.sign s = (-1) ^ (s.cycleType.sum + Multiset.card s.cycleType) :=
    Perm.sign_of_cycleType s
  rw [hsum, ← hk, hsign] at hsg
  interval_cases k
  · exact absurd rfl hk0
  · norm_num at hsg
  · rw [hrep]; rfl
  · norm_num at hsg

open Equiv Perm in
theorem involutions_conj_alt7 (a b : alternatingGroup (Fin 7)) (ha : orderOf a = 2)
    (hb : orderOf b = 2) : IsConj a b := by
  have hc : IsConj (a : Perm (Fin 7)) (b : Perm (Fin 7)) := by
    rw [Perm.isConj_iff_cycleType_eq, cycleType_involution_alt7 a ha, cycleType_involution_alt7 b hb]
  refine alternatingGroup.isConj_of hc ?_
  have h1 : (a : Perm (Fin 7)).cycleType = {2, 2} := cycleType_involution_alt7 a ha
  have h2 : (a : Perm (Fin 7)).support.card = 4 := by
    rw [← Perm.sum_cycleType, h1]; rfl
  rw [h2]; simp

theorem isPGroup_closure_dihedral {H : Type} [Group H] {a b : H} (ha : a * a = 1) (hb : b * b = 1)
    (hab4 : (a * b) ^ 4 = 1) : IsPGroup 2 ↥(Subgroup.closure {a, b}) := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  obtain ⟨r, hr⟩ : ∃ r, r = a * b := ⟨_, rfl⟩
  have hr4 : r ^ 4 = 1 := by rw [hr]; exact hab4
  have hinv : r⁻¹ = b * a := by rw [hr, mul_inv_rev, hainv, hbinv]
  have hconj : a * r * a⁻¹ = r⁻¹ := by
    rw [hinv, hr, hainv]
    calc a * (a * b) * a = (a * a) * (b * a) := by group
      _ = b * a := by rw [ha, one_mul]
  have hconjz : ∀ j : ℤ, a * r ^ j = r ^ (-j) * a := by
    intro j
    have h1 : a * r ^ j * a⁻¹ = (a * r * a⁻¹) ^ j := (conj_zpow).symm
    rw [hconj, inv_zpow, ← zpow_neg] at h1
    calc a * r ^ j = (a * r ^ j * a⁻¹) * a := by group
      _ = r ^ (-j) * a := by rw [h1]
  have hb' : b = r ^ (-1 : ℤ) * a := by
    have := hconjz 1
    rw [zpow_one] at this
    calc b = a * (a * b) := by rw [← mul_assoc, ha, one_mul]
      _ = a * r := by rw [hr]
      _ = r ^ (-1 : ℤ) * a := this
  have hsq : ∀ i j : ℤ, (r ^ i * a) * (r ^ j * a) = r ^ (i - j) := by
    intro i j
    calc (r ^ i * a) * (r ^ j * a) = r ^ i * ((a * r ^ j) * a) := by rw [mul_assoc, mul_assoc]
      _ = r ^ i * ((r ^ (-j) * a) * a) := by rw [hconjz]
      _ = r ^ i * (r ^ (-j) * (a * a)) := by rw [mul_assoc (r ^ (-j))]
      _ = r ^ (i - j) := by rw [ha, mul_one, ← zpow_add, sub_eq_add_neg]
  have hall : ∀ x ∈ Subgroup.closure ({a, b} : Set H), ∃ i : ℤ, x = r ^ i ∨ x = r ^ i * a := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | hx
      · exact ⟨0, Or.inr (by simp)⟩
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨-1, Or.inr hb'⟩
    | one => exact ⟨0, Or.inl (by simp)⟩
    | mul x y _ _ hx hy =>
      obtain ⟨i, hi | hi⟩ := hx <;> obtain ⟨j, hj | hj⟩ := hy
      · exact ⟨i + j, Or.inl (by rw [hi, hj, zpow_add])⟩
      · exact ⟨i + j, Or.inr (by rw [hi, hj, zpow_add, mul_assoc])⟩
      · refine ⟨i - j, Or.inr ?_⟩
        rw [hi, hj]
        calc r ^ i * a * r ^ j = r ^ i * (a * r ^ j) := mul_assoc _ _ _
          _ = r ^ i * (r ^ (-j) * a) := by rw [hconjz]
          _ = (r ^ i * r ^ (-j)) * a := (mul_assoc _ _ _).symm
          _ = r ^ (i - j) * a := by rw [← zpow_add, sub_eq_add_neg]
      · exact ⟨i - j, Or.inl (by rw [hi, hj]; exact hsq i j)⟩
    | inv x _ hx =>
      obtain ⟨i, hi | hi⟩ := hx
      · exact ⟨-i, Or.inl (by rw [hi, zpow_neg])⟩
      · refine ⟨i, Or.inr ?_⟩
        rw [hi, mul_inv_rev, hainv, ← zpow_neg, hconjz, neg_neg]
  intro g
  refine ⟨2, ?_⟩
  apply Subtype.ext
  show (g : H) ^ (2 ^ 2) = 1
  obtain ⟨i, h | h⟩ := hall g g.2
  · rw [h]
    have : (r ^ i) ^ 4 = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp [hr4]
    simpa using this
  · rw [h]
    have h2 : (r ^ i * a) * (r ^ i * a) = 1 := by rw [hsq, sub_self, zpow_zero]
    have h2' : (r ^ i * a) ^ 2 = 1 := by rw [sq]; exact h2
    calc (r ^ i * a) ^ (2 ^ 2) = (r ^ i * a) ^ (2 * 2) := by norm_num
      _ = ((r ^ i * a) ^ 2) ^ 2 := pow_mul _ 2 2
      _ = 1 := by rw [h2', one_pow]

theorem exists_noncomm_in_sylow {H : Type} [Group H] [Finite H] {a b : H} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab4 : (a * b) ^ 4 = 1) (hab2 : (a * b) ^ 2 ≠ 1) (Q : Sylow 2 H) :
    ∃ x ∈ (Q : Subgroup H), ∃ y ∈ (Q : Subgroup H), orderOf x = 2 ∧ orderOf y = 2 ∧
      x * y ≠ y * x := by
  have ha2 : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha, sq] at this
  have hb2 : b * b = 1 := by
    have := pow_orderOf_eq_one b
    rwa [hb, sq] at this
  have hD := isPGroup_closure_dihedral ha2 hb2 hab4
  obtain ⟨Q₀, hQ₀⟩ := hD.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q₀ Q
  have hmem : ∀ x ∈ (Q₀ : Subgroup H), g * x * g⁻¹ ∈ (Q : Subgroup H) := by
    intro x hx
    rw [← hg]
    rw [Sylow.coe_subgroup_smul]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have haD : a ∈ Subgroup.closure ({a, b} : Set H) := Subgroup.subset_closure (by simp)
  have hbD : b ∈ Subgroup.closure ({a, b} : Set H) := Subgroup.subset_closure (by simp)
  have hconjord : ∀ c : H, orderOf (g * c * g⁻¹) = orderOf c := fun c => by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
    simpa [MulAut.conj_apply] using this
  refine ⟨g * a * g⁻¹, hmem a (hQ₀ haD), g * b * g⁻¹, hmem b (hQ₀ hbD), ?_, ?_, ?_⟩
  · rw [hconjord, ha]
  · rw [hconjord, hb]
  · intro h
    apply hab2
    have h1 : g * (a * b) * g⁻¹ = g * (b * a) * g⁻¹ := by
      calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        _ = (g * b * g⁻¹) * (g * a * g⁻¹) := h
        _ = g * (b * a) * g⁻¹ := by group
    have h2 : a * b = b * a := mul_left_cancel (mul_right_cancel h1)
    calc (a * b) ^ 2 = (a * b) * (a * b) := sq _
      _ = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← h2]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha2, hb2, one_mul]

@[expose] def DihedralPair (H : Type) [Group H] : Prop :=
  ∃ a b : H, orderOf a = 2 ∧ orderOf b = 2 ∧ (a * b) ^ 4 = 1 ∧ (a * b) ^ 2 ≠ 1

theorem dihedralPair_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H')
    (h : DihedralPair H) : DihedralPair H' := by
  obtain ⟨a, b, ha, hb, h4, h2⟩ := h
  refine ⟨e a, e b, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]; exact ha
  · rw [MulEquiv.orderOf_eq]; exact hb
  · rw [← map_mul, ← map_pow, h4, map_one]
  · intro h'
    apply h2
    apply e.injective
    rw [map_pow, map_mul, h', map_one]

theorem exists_noncomm_in_sylow_of_dihedralPair {H : Type} [Group H] [Finite H]
    (hD : DihedralPair H) (Q : Sylow 2 H) :
    ∃ x ∈ (Q : Subgroup H), ∃ y ∈ (Q : Subgroup H), orderOf x = 2 ∧ orderOf y = 2 ∧
      x * y ≠ y * x := by
  obtain ⟨a, b, ha, hb, h4, h2⟩ := hD
  exact exists_noncomm_in_sylow ha hb h4 h2 Q

open Equiv Perm in
theorem dihedralPair_alt7 : DihedralPair (alternatingGroup (Fin 7)) := by
  let a : alternatingGroup (Fin 7) := ⟨swap 0 2 * swap 4 5, mem_alternatingGroup.2 (by decide)⟩
  let b : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.2 (by decide)⟩
  have ha2 : a * a = 1 := by decide
  have hb2 : b * b = 1 := by decide
  have ha1 : a ≠ 1 := by decide
  have hb1 : b ≠ 1 := by decide
  exact ⟨a, b, orderOf_eq_prime (by rw [sq]; exact ha2) ha1,
    orderOf_eq_prime (by rw [sq]; exact hb2) hb1, by decide, by decide⟩

open Equiv Perm in
theorem dihedralPair_alt6 : DihedralPair (alternatingGroup (Fin 6)) := by
  let a : alternatingGroup (Fin 6) := ⟨swap 0 2 * swap 4 5, mem_alternatingGroup.2 (by decide)⟩
  let b : alternatingGroup (Fin 6) := ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.2 (by decide)⟩
  have ha2 : a * a = 1 := by decide
  have hb2 : b * b = 1 := by decide
  have ha1 : a ≠ 1 := by decide
  have hb1 : b ≠ 1 := by decide
  exact ⟨a, b, orderOf_eq_prime (by rw [sq]; exact ha2) ha1,
    orderOf_eq_prime (by rw [sq]; exact hb2) hb1, by decide, by decide⟩

open CFSG.GorensteinWalter in
theorem exists_psl_model_of_hasL2Model {H : Type} [Group H] {P : ℕ → Prop} (h : HasL2Model H P) :
    ∃ (p f : ℕ) (_ : p.Prime) (F : Type) (_ : Field F) (_ : Finite F),
      1 ≤ f ∧ P (p ^ f) ∧ Nat.card F = p ^ f ∧ Nonempty (H ≃* PSL2 F) := by
  obtain ⟨p, f, hp, hf, hP, hL⟩ := h
  rcases hL with ⟨-, hmod⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨-, F, hF, hFin, hcard, ⟨e⟩⟩ := hmod
    exact ⟨p, f, hp, F, hF, hFin, hf, hP, hcard, ⟨e.trans (IVK.L2.equivPSL F)⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem isConj_of_mulEquiv {H H' : Type} [Group H] [Group H'] (e : H ≃* H') {a b : H}
    (h : IsConj (e a) (e b)) : IsConj a b := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  exact hc

theorem involutions_conj_of_model {H : Type} [Group H]
    (h : HasL2Model H Odd ∨ Nonempty (H ≃* alternatingGroup (Fin 7))) (a b : H)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : IsConj a b := by
  rcases h with h | h
  · obtain ⟨p, f, hp, F, hF, hFin, hf, hP, hcard, ⟨e⟩⟩ := exists_psl_model_of_hasL2Model h
    have : Fact p.Prime := ⟨hp⟩
    have hpodd : Odd p := by
      by_contra hne
      rw [Nat.not_odd_iff_even] at hne
      exact (Nat.not_even_iff_odd.2 hP) ((Nat.even_pow).2 ⟨hne, by omega⟩)
    have h1 := CFSG.Walter.psl2_isConj_of_orderOf_eq_two F hcard hpodd hf
      (x := e a) (y := e b) (by rw [MulEquiv.orderOf_eq]; exact ha)
      (by rw [MulEquiv.orderOf_eq]; exact hb)
    exact isConj_of_mulEquiv e h1
  · obtain ⟨e⟩ := h
    have h1 := involutions_conj_alt7 (e a) (e b) (by rw [MulEquiv.orderOf_eq]; exact ha)
      (by rw [MulEquiv.orderOf_eq]; exact hb)
    exact isConj_of_mulEquiv e h1

open CFSG.GorensteinWalter in
theorem exists_involution_of_model {H : Type} [Group H]
    (h : HasL2Model H Odd ∨ Nonempty (H ≃* alternatingGroup (Fin 7))) : ∃ a : H, orderOf a = 2 := by
  rcases h with h | h
  · obtain ⟨p, f, hp, F, hF, hFin, hf, hP, hcard, ⟨e⟩⟩ := exists_psl_model_of_hasL2Model h
    obtain ⟨y, hy1, hy2⟩ := IVK.exists_involution_psl2 (F := F)
    have hy2' : y ^ 2 = 1 := by
      apply Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
      rw [map_pow, hy2, map_one]
    refine ⟨e.symm y, orderOf_eq_prime ?_ ?_⟩
    · have hh : e.symm (y ^ 2) = e.symm y ^ 2 := map_pow e.symm y 2
      rw [← hh, hy2', map_one]
    · intro h1
      apply hy1
      have := congrArg e h1
      simpa using this
  · obtain ⟨e⟩ := h
    have h2 : 2 ∣ Nat.card H := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
        Fintype.card_fin]
      decide
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite H := Finite.of_equiv _ e.symm.toEquiv
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' 2 h2
    exact ⟨a, ha⟩

@[expose] def glA : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 1, 0; 0, 0, 1]

@[expose] def glB : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 1, 1; 0, 0, 1]

theorem glA_sq : glA * glA = 1 := by decide

theorem glB_sq : glB * glB = 1 := by decide

@[expose] def glMkA : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) := ⟨glA, glA, glA_sq, glA_sq⟩

@[expose] def glMkB : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) := ⟨glB, glB, glB_sq, glB_sq⟩

theorem glMkA_sq : glMkA * glMkA = 1 := Units.ext glA_sq

theorem glMkB_sq : glMkB * glMkB = 1 := Units.ext glB_sq

theorem dihedralPair_gl3 : DihedralPair (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) := by
  have ha1 : glMkA ≠ 1 := by decide
  have hb1 : glMkB ≠ 1 := by decide
  exact ⟨glMkA, glMkB, orderOf_eq_prime (by rw [sq]; exact glMkA_sq) ha1,
    orderOf_eq_prime (by rw [sq]; exact glMkB_sq) hb1, by decide, by decide⟩

open CFSG.GorensteinWalter in
theorem dihedralPair_of_model_seven {H : Type} [Group H] (h : HasL2Model H (fun r => r = 7)) :
    DihedralPair H := by
  obtain ⟨p, f, hp, F, hF, hFin, hf, hP, hcard, ⟨e⟩⟩ := exists_psl_model_of_hasL2Model h
  have hF7 : Nat.card F = 7 := by rw [hcard, hP]
  have : Fintype F := Fintype.ofFinite F
  have hFc : Fintype.card F = 7 := by rw [← Nat.card_eq_fintype_card]; exact hF7
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  let eK : ZMod 7 ≃+* F := ZMod.ringEquivOfPrime F (by norm_num) hFc
  obtain ⟨eGL⟩ := CFSG.LocalAnalysis.ComponentInitial.nonempty_GL_three_two_equiv_PSL_two_seven
  have eH : H ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) :=
    (e.trans (psl2RingEquiv eK).symm).trans eGL.symm
  exact dihedralPair_of_mulEquiv eH.symm dihedralPair_gl3

theorem sylow_noncomm_involutions {H : Type} [Group H] [Finite H]
    (h : HasL2Model H (fun r => r = 7 ∨ r = 9) ∨ Nonempty (H ≃* alternatingGroup (Fin 7)))
    (P : Subgroup H) (hP : IsSylowOf 2 P ⊤) :
    ∃ a ∈ P, ∃ b ∈ P, orderOf a = 2 ∧ orderOf b = 2 ∧ a * b ≠ b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD : DihedralPair H := by
    rcases h with h | h
    · obtain ⟨p, f, hp, hf, hP', hL⟩ := h
      rcases hP' with h7 | h9
      · exact dihedralPair_of_model_seven ⟨p, f, hp, hf, h7, hL⟩
      · obtain ⟨e⟩ := nonempty_alt6_of_hasL2Model9 (⟨p, f, hp, hf, h9, hL⟩ : HasL2Model H (fun r => r = 9))
        exact dihedralPair_of_mulEquiv e.symm dihedralPair_alt6
    · obtain ⟨e⟩ := h
      exact dihedralPair_of_mulEquiv e.symm dihedralPair_alt7
  let Q : Sylow 2 H := Sylow.ofCard P (by rw [hP.card_eq, Subgroup.card_top])
  obtain ⟨x, hx, y, hy, hx2, hy2, hxy⟩ := exists_noncomm_in_sylow_of_dihedralPair hD Q
  exact ⟨x, hx, y, hy, hx2, hy2, hxy⟩

end CFSG.GH74.GLS.C3.Layer1.Back
