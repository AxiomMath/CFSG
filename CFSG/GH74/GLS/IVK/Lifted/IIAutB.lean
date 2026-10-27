module

public import CFSG.GH74.GLS.IVK.Lifted.IIAut
public import CFSG.GH74.GLS.IVK.Lifted.Companion
public import CFSG.GH74.GLS.IVK.Lifted.TwoCoverRank
public import CFSG.LinearAlgebra.LinearGroups.TwoQuadraticOddSections

public section

namespace CFSG.GH74.GLS.IVK.Lifted

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage1.Thm2.Recip

section SL2

variable {F : Type} [Field F]

theorem trace_eq_zero_of_sq_eq_neg_one (A : Matrix (Fin 2) (Fin 2) F) (hsq : A * A = -1)
    (hdet : A.det = 1) : A 0 0 + A 1 1 = 0 := by
  have e00 := congrFun (congrFun hsq 0) 0
  have e01 := congrFun (congrFun hsq 0) 1
  have e10 := congrFun (congrFun hsq 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.neg_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e00 e01 e10
  rw [Matrix.det_fin_two] at hdet
  by_contra ht
  have h01 : A 0 1 = 0 := by
    have : A 0 1 * (A 0 0 + A 1 1) = 0 := by linear_combination e01
    exact (mul_eq_zero.mp this).resolve_right ht
  have h10 : A 1 0 = 0 := by
    have : A 1 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e10
    exact (mul_eq_zero.mp this).resolve_right ht
  rw [h01, h10] at hdet e00
  have h00 : A 0 0 * (A 0 0 + A 1 1) = 0 := by linear_combination e00 + hdet
  have hA00 : A 0 0 ≠ 0 := by
    intro h
    rw [h] at e00
    simp at e00
  exact ht ((mul_eq_zero.mp h00).resolve_left hA00)

theorem det_smul_add_smul (A : Matrix (Fin 2) (Fin 2) F) (hsq : A * A = -1) (hdet : A.det = 1)
    (x y : F) : (x • (1 : Matrix (Fin 2) (Fin 2) F) + y • A).det = x ^ 2 + y ^ 2 := by
  have ht := trace_eq_zero_of_sq_eq_neg_one A hsq hdet
  rw [Matrix.det_fin_two] at hdet ⊢
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul]
  linear_combination (x * y) * ht + y ^ 2 * hdet

theorem exists_sq_add_sq_of_odd [Finite F] (hodd : Odd (Nat.card F)) (d : F) :
    ∃ x y : F, x ^ 2 + y ^ 2 = d := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.odd_iff.mp hodd
  obtain ⟨a, b, h⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2) (g := Polynomial.X ^ 2 - Polynomial.C d)
    (by rw [Polynomial.degree_X_pow]; rfl) (Polynomial.degree_X_pow_sub_C (by norm_num) d) hcard
  refine ⟨a, b, ?_⟩
  simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C] at h
  linear_combination h

theorem two_ne_zero_of_odd_card [Finite F] (hodd : Odd (Nat.card F)) : (2 : F) ≠ 0 := by
  intro h
  apply CFSG.GH74.GLS.neg_one_ne_one_of_odd_card F hodd
  have h11 : (1 : F) + 1 = 0 := by
    rw [one_add_one_eq_two]
    exact h
  exact neg_eq_of_add_eq_zero_right h11

theorem sl2_order_four_conj [Finite F] (hodd : Odd (Nat.card F))
    {a b : Matrix.SpecialLinearGroup (Fin 2) F} (ha : orderOf a = 4) (hb : orderOf b = 4) :
    IsConj a b := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  have hsq : ∀ s : Matrix.SpecialLinearGroup (Fin 2) F, orderOf s = 4 →
      (s : Matrix (Fin 2) (Fin 2) F) * s = -1 := by
    intro s hs
    have ho : orderOf (s ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hs]; norm_num), hs]
    have h1 : (s ^ 2) ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ho]
    have h1' : s ^ 2 ≠ 1 := fun h => by
      rw [h, orderOf_one] at ho
      omega
    have := CFSG.LinearGroups.SL2_coe_eq_neg_one_of_sq h2 (s ^ 2) h1 h1'
    rwa [Matrix.SpecialLinearGroup.coe_pow, pow_two] at this
  have hnonsc : ∀ s : Matrix.SpecialLinearGroup (Fin 2) F, orderOf s = 4 →
      ∀ r : F, (s : Matrix (Fin 2) (Fin 2) F) ≠ r • (1 : Matrix (Fin 2) (Fin 2) F) := by
    intro s hs r hr
    have h1 := hsq s hs
    have hd : (s : Matrix (Fin 2) (Fin 2) F).det = 1 := s.2
    rw [hr] at h1 hd
    have e := congrFun (congrFun h1 0) 0
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, Matrix.neg_apply,
      Matrix.one_apply_eq, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), smul_eq_mul] at e
    rw [Matrix.det_smul, Matrix.det_one] at hd
    simp only [Fintype.card_fin] at hd
    apply h2
    linear_combination e - hd
  have hdetg : ∀ s : Matrix.SpecialLinearGroup (Fin 2) F, (s : Matrix (Fin 2) (Fin 2) F).det = 1 :=
    fun s => s.2
  obtain ⟨Pa, hPa, hPaeq⟩ := companion_conj (a : Matrix (Fin 2) (Fin 2) F) (hdetg a) (hnonsc a ha)
  obtain ⟨Pb, hPb, hPbeq⟩ := companion_conj (b : Matrix (Fin 2) (Fin 2) F) (hdetg b) (hnonsc b hb)
  have ta := trace_eq_zero_of_sq_eq_neg_one _ (hsq a ha) (hdetg a)
  have tb := trace_eq_zero_of_sq_eq_neg_one _ (hsq b hb) (hdetg b)
  rw [ta] at hPaeq
  rw [tb] at hPbeq
  set A : Matrix (Fin 2) (Fin 2) F := (a : Matrix (Fin 2) (Fin 2) F) with hA
  set B : Matrix (Fin 2) (Fin 2) F := (b : Matrix (Fin 2) (Fin 2) F) with hB
  set C : Matrix (Fin 2) (Fin 2) F := !![0, -1; 1, 0] with hC
  have hPadet : IsUnit Pa.det := (Matrix.isUnit_iff_isUnit_det Pa).1 hPa
  have hPbdet : IsUnit Pb.det := (Matrix.isUnit_iff_isUnit_det Pb).1 hPb
  have hPaPa : Pa * Pa⁻¹ = 1 := Matrix.mul_nonsing_inv Pa hPadet
  have hPainv : Pa⁻¹ * A = C * Pa⁻¹ := by
    calc Pa⁻¹ * A = Pa⁻¹ * A * (Pa * Pa⁻¹) := by rw [hPaPa, Matrix.mul_one]
      _ = Pa⁻¹ * (A * Pa) * Pa⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Pa⁻¹ * (Pa * C) * Pa⁻¹ := by rw [hPaeq]
      _ = C * Pa⁻¹ := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul Pa hPadet, Matrix.one_mul]
  set G₁ : Matrix (Fin 2) (Fin 2) F := Pb * Pa⁻¹ with hG₁
  have hG₁A : G₁ * A = B * G₁ := by
    calc G₁ * A = Pb * (Pa⁻¹ * A) := by rw [hG₁, Matrix.mul_assoc]
      _ = Pb * (C * Pa⁻¹) := by rw [hPainv]
      _ = (Pb * C) * Pa⁻¹ := by rw [Matrix.mul_assoc]
      _ = (B * Pb) * Pa⁻¹ := by rw [hPbeq]
      _ = B * G₁ := by rw [hG₁, Matrix.mul_assoc]
  have hG₁det : IsUnit G₁.det := by
    rw [hG₁, Matrix.det_mul]
    exact hPbdet.mul (by
      rw [Matrix.det_nonsing_inv]
      exact (Ring.inverse_unit hPadet.unit ▸ (hPadet.unit⁻¹).isUnit))
  obtain ⟨x, y, hxy⟩ := exists_sq_add_sq_of_odd hodd (G₁.det)⁻¹
  set Hm : Matrix (Fin 2) (Fin 2) F := x • (1 : Matrix (Fin 2) (Fin 2) F) + y • A with hHm
  have hHdet : Hm.det = (G₁.det)⁻¹ := by
    rw [hHm, det_smul_add_smul A (hsq a ha) (hdetg a) x y, hxy]
  have hHA : Hm * A = A * Hm := by
    rw [hHm]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  set G : Matrix (Fin 2) (Fin 2) F := G₁ * Hm with hG
  have hGdet : G.det = 1 := by
    rw [hG, Matrix.det_mul, hHdet]
    exact mul_inv_cancel₀ hG₁det.ne_zero
  have hGA : G * A = B * G := by
    calc G * A = G₁ * (Hm * A) := Matrix.mul_assoc G₁ Hm A
      _ = G₁ * (A * Hm) := by rw [hHA]
      _ = (G₁ * A) * Hm := (Matrix.mul_assoc G₁ A Hm).symm
      _ = (B * G₁) * Hm := by rw [hG₁A]
      _ = B * G := Matrix.mul_assoc B G₁ Hm
  let g : Matrix.SpecialLinearGroup (Fin 2) F := ⟨G, hGdet⟩
  have hg : g * a = b * g := by
    apply Subtype.ext
    exact hGA
  exact isConj_iff.2 ⟨g, mul_inv_eq_iff_eq_mul.2 hg⟩

end SL2

section A7

open Equiv Equiv.Perm CFSG.GH74.Uniqueness.SU.SU13.TA

theorem cycleType_two_two_of_sq_eq_one_alt_seven {σ : alternatingGroup (Fin 7)} (hσ2 : σ ^ 2 = 1)
    (hσ1 : σ ≠ 1) : (σ : Perm (Fin 7)).cycleType = {2, 2} := by
  have hp2 : (σ : Perm (Fin 7)) ^ 2 = 1 := by
    have := congrArg Subtype.val hσ2
    simpa using this
  have hne : (σ : Perm (Fin 7)) ≠ 1 := fun h => hσ1 (Subtype.ext h)
  have hsign : Perm.sign (σ : Perm (Fin 7)) = 1 := Perm.mem_alternatingGroup.mp σ.2
  obtain ⟨k, hk⟩ : ∃ k, (σ : Perm (Fin 7)).cycleType = Multiset.replicate k 2 :=
    ⟨_, Perm.cycleType_of_pow_prime_eq_one hp2⟩
  have hsum := Perm.sum_cycleType_le (σ : Perm (Fin 7))
  rw [hk, Multiset.sum_replicate, smul_eq_mul, Fintype.card_fin] at hsum
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne (Perm.cycleType_eq_zero.mp hk)
  rw [Perm.sign_of_cycleType, hk, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hsign
  have hk3 : k ≤ 3 := by omega
  have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
  interval_cases k
  · exact absurd hsign (by decide)
  · rw [hk]
    rfl
  · exact absurd hsign (by decide)

variable {Q : Type} [Group Q] {π : Q →* alternatingGroup (Fin 7)}

theorem twoCover_order_four_conj (hπ : TwoCover π) {a b : Q} (ha : orderOf a = 4)
    (hb : orderOf b = 4) : IsConj a b := by
  obtain ⟨z, hzc, hz1, hz2, hzk⟩ := hπ.exists_z
  have hz2' : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzcomm : ∀ g : Q, g * z = z * g := fun g => Subgroup.mem_center_iff.mp hzc g
  have : Finite Q := hπ.finite'
  have hdd : ∀ x : Q, orderOf x = 4 →
      ((π x : alternatingGroup (Fin 7)) : Perm (Fin 7)).cycleType = {2, 2} := by
    intro x hx
    have hx2 : orderOf (x ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hx]; norm_num), hx]
    have hker : x ^ 2 ∈ π.ker := mem_ker_of_orderOf_eq_two_alt_seven hπ hx2
    have hs2 : (π x) ^ 2 = 1 := by
      rw [← map_pow]
      exact hker
    have hs1 : π x ≠ 1 := by
      intro h1
      have hxk : x ∈ π.ker := h1
      have h3 := hπ.sq_eq_one_of_mem_ker' hxk
      rw [h3, orderOf_one] at hx2
      omega
    exact cycleType_two_two_of_sq_eq_one_alt_seven hs2 hs1
  let β₀ : alternatingGroup (Fin 7) := ⟨swap 0 1 * swap 2 3, Perm.mem_alternatingGroup.2 (by
    rw [map_mul, sign_swap (by decide), sign_swap (by decide)]
    decide)⟩
  let γ₀ : alternatingGroup (Fin 7) := ⟨swap 0 2 * swap 1 3, Perm.mem_alternatingGroup.2 (by
    rw [map_mul, sign_swap (by decide), sign_swap (by decide)]
    decide)⟩
  have hβ₀ : (β₀ : Perm (Fin 7)).cycleType = {2, 2} :=
    cycleType_swap_mul_swap_of_nodup (by decide)
  have hγ₀ : (γ₀ : Perm (Fin 7)).cycleType = {2, 2} :=
    cycleType_swap_mul_swap_of_nodup (by decide)
  have hβγ : ((β₀ * γ₀ : alternatingGroup (Fin 7)) : Perm (Fin 7)).cycleType = {2, 2} := by
    have h : ((β₀ * γ₀ : alternatingGroup (Fin 7)) : Perm (Fin 7)) = swap 0 3 * swap 1 2 := by
      show swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3) = swap 0 3 * swap 1 2
      decide
    rw [h]
    exact cycleType_swap_mul_swap_of_nodup (by decide)
  obtain ⟨b₀, hb₀⟩ := hπ.surj β₀
  obtain ⟨y₀, hy₀⟩ := hπ.surj γ₀
  have hsq : ∀ x : Q, ((π x : alternatingGroup (Fin 7)) : Perm (Fin 7)).cycleType = {2, 2} →
      x ^ 2 = z := by
    intro x hx
    obtain ⟨hk, h1⟩ := hπ.sq_mem_ker_ne_one_of_cycleType_two_two (by norm_num) hx
    exact (hzk _ hk).resolve_left h1
  have hb₀sq : b₀ ^ 2 = z := hsq b₀ (by rw [hb₀]; exact hβ₀)
  have hy₀sq : y₀ ^ 2 = z := hsq y₀ (by rw [hy₀]; exact hγ₀)
  have hby : (b₀ * y₀) ^ 2 = z := hsq _ (by rw [map_mul, hb₀, hy₀]; exact hβγ)
  have hQ8 : y₀ * b₀ * y₀⁻¹ = b₀ * z := by
    have hyi : y₀⁻¹ = y₀ * z := by
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, ← pow_two, hy₀sq, hz2']
    have hbi : b₀⁻¹ = b₀ * z := by
      apply inv_eq_of_mul_eq_one_right
      rw [← mul_assoc, ← pow_two, hb₀sq, hz2']
    have h1 : b₀ * y₀ * b₀ * y₀ = z := by
      have := hby
      rw [pow_two] at this
      simpa [mul_assoc] using this
    have h2 : y₀ * b₀ * y₀ = b₀ := by
      calc y₀ * b₀ * y₀ = b₀⁻¹ * (b₀ * y₀ * b₀ * y₀) := by group
        _ = b₀⁻¹ * z := by rw [h1]
        _ = b₀ := by rw [hbi, mul_assoc, hz2', mul_one]
    calc y₀ * b₀ * y₀⁻¹ = (y₀ * b₀ * y₀) * z := by rw [hyi]; simp only [mul_assoc]
      _ = b₀ * z := by rw [h2]
  have key : ∀ x : Q, ((π x : alternatingGroup (Fin 7)) : Perm (Fin 7)).cycleType = {2, 2} →
      IsConj x b₀ := by
    intro x hx
    have hconj : IsConj (π x) (π b₀) := by
      rw [hb₀]
      exact isConj_alternatingGroup_of_cycleType_eq_two_two hx hβ₀
    obtain ⟨g, k, hk, hg⟩ := hπ.exists_conj_mul_ker_of_isConj hconj
    rcases hzk k hk with rfl | rfl
    · exact isConj_iff.2 ⟨g, by rw [hg, mul_one]⟩
    · refine isConj_iff.2 ⟨y₀⁻¹ * g, ?_⟩
      calc y₀⁻¹ * g * x * (y₀⁻¹ * g)⁻¹ = y₀⁻¹ * (g * x * g⁻¹) * y₀ := by group
        _ = y₀⁻¹ * (b₀ * k) * y₀ := by rw [hg]
        _ = y₀⁻¹ * (y₀ * b₀ * y₀⁻¹) * y₀ := by rw [hQ8]
        _ = b₀ := by group
  exact (key a (hdd a ha)).trans (key b (hdd b hb)).symm

end A7

theorem ii4_aut_b : II4_Aut_b := by
  intro Q _ _ hQ a b ha hb
  rcases sl_or_a7 hQ with ⟨F, _, _, hodd, -, ⟨e⟩⟩ | h7
  · have h := sl2_order_four_conj hodd (a := e a) (b := e b)
      (by rwa [MulEquiv.orderOf_eq]) (by rwa [MulEquiv.orderOf_eq])
    obtain ⟨c, hc⟩ := isConj_iff.1 h
    refine isConj_iff.2 ⟨e.symm c, e.injective ?_⟩
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  · have hT : CFSG.GH74.Uniqueness.SU.K.IsTwoAlt Q 7 :=
      ⟨h7.1, (inferInstance : Finite Q), h7.2.1, h7.2.2⟩
    obtain ⟨π, hπ⟩ := CFSG.GH74.Uniqueness.SU.SU13.TA.TwoCover.exists_of_isTwoAlt hT
    exact twoCover_order_four_conj hπ ha hb

end CFSG.GH74.GLS.IVK.Lifted
