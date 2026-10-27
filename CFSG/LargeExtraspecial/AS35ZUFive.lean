module

public import CFSG.LargeExtraspecial.AS35LInvB

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35Z

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary CFSG.LargeExtraspecial.AS35L
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

@[expose] noncomputable def fivePrd (p x q y : Fin n → K) : SUid frob n :=
  tvU p * tvU x * tvU (q + y) * tvU y

theorem herm_qy_qy {q y : Fin n → K} (hqq : herm frob q q = 0) (hyy : herm frob y y = 0)
    (hqy : herm frob q y = 0) : herm frob (q + y) (q + y) = 0 := by
  have hyq : herm frob y q = 0 := herm_eq_zero_comm frob frob_frob hqy
  simp only [herm_add_left, herm_add_right, hqq, hqy, hyq, hyy, add_zero]

section Prd

variable {p x q y : Fin n → K} (hpp : herm frob p p = 0) (hxx : herm frob x x = 0)
  (hqq : herm frob q q = 0) (hyy : herm frob y y = 0) (hpx : herm frob p x = 0)
  (hpq : herm frob p q = 1) (hpy : herm frob p y = 0) (hxq : herm frob x q = 0)
  (hxy : herm frob x y = 1) (hqy : herm frob q y = 0)
include hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy

theorem fivePrd_smul_p : fivePrd p x q y • p = x + q + y := by
  have hqp : herm frob q p = 1 := by rw [herm_conj frob frob_frob p q, hpq, map_one]
  have hyp : herm frob y p = 0 := herm_eq_zero_comm frob frob_frob hpy
  have hxp : herm frob x p = 0 := herm_eq_zero_comm frob frob_frob hpx
  have hb := herm_qy_qy hqq hyy hqy
  rw [fivePrd, mul_smul, mul_smul, mul_smul, tvU_smul_of_herm_eq_zero hyy hyp, tvU_smul hb,
    tvU_smul hxx, tvU_smul hpp]
  simp only [herm_add_left, herm_add_right, hqp, hyp, hxp, hxq, hxy, hpp, hpx, hpq, hpy,
    one_smul, add_zero, zero_add]
  linear_combination (norm := module) two_eq_zero • p

theorem fivePrd_smul_x : fivePrd p x q y • x = p + x + q := by
  have hyx : herm frob y x = 1 := by rw [herm_conj frob frob_frob x y, hxy, map_one]
  have hqx : herm frob q x = 0 := herm_eq_zero_comm frob frob_frob hxq
  have hb := herm_qy_qy hqq hyy hqy
  rw [fivePrd, mul_smul, mul_smul, mul_smul, tvU_smul hyy, tvU_smul hb, tvU_smul hxx,
    tvU_smul hpp]
  simp only [herm_add_left, herm_add_right, herm_smul_right, hyx, hqx, hqy, hyy, hxx, hxq,
    hxy, hpx, hpq, hpy, one_smul, add_zero, zero_add]
  linear_combination (norm := module) two_eq_zero • (x + y)

omit hpx hpy hxy in
theorem fivePrd_smul_q : fivePrd p x q y • q = p + q := by
  have hyq : herm frob y q = 0 := herm_eq_zero_comm frob frob_frob hqy
  have hb := herm_qy_qy hqq hyy hqy
  rw [fivePrd, mul_smul, mul_smul, mul_smul, tvU_smul_of_herm_eq_zero hyy hyq,
    tvU_smul_of_herm_eq_zero hb (by simp only [herm_add_left, hqq, hyq, add_zero]),
    tvU_smul_of_herm_eq_zero hxx hxq, tvU_smul hpp, hpq, one_smul]
  exact add_comm _ _

omit hpq hxq in
theorem fivePrd_smul_y : fivePrd p x q y • y = x + y := by
  have hb := herm_qy_qy hqq hyy hqy
  rw [fivePrd, mul_smul, mul_smul, mul_smul, tvU_smul_self hyy,
    tvU_smul_of_herm_eq_zero hb (by simp only [herm_add_left, hqy, hyy, add_zero]),
    tvU_smul hxx, hxy, one_smul,
    tvU_smul_of_herm_eq_zero hpp (by simp only [herm_add_right, hpx, hpy, add_zero])]
  exact add_comm _ _

omit hpx hpq hpy hxq hxy in
theorem fivePrd_smul_of_perp {z : Fin n → K} (hpz : herm frob p z = 0)
    (hxz : herm frob x z = 0) (hqz : herm frob q z = 0) (hyz : herm frob y z = 0) :
    fivePrd p x q y • z = z := by
  have hb := herm_qy_qy hqq hyy hqy
  rw [fivePrd, mul_smul, mul_smul, mul_smul, tvU_smul_of_herm_eq_zero hyy hyz,
    tvU_smul_of_herm_eq_zero hb (by rw [herm_add_left, hqz, hyz, add_zero]),
    tvU_smul_of_herm_eq_zero hxx hxz, tvU_smul_of_herm_eq_zero hpp hpz]

theorem fivePrd_pow_five_smul_frame :
    fivePrd p x q y ^ 5 • p = p ∧ fivePrd p x q y ^ 5 • x = x ∧
      fivePrd p x q y ^ 5 • q = q ∧ fivePrd p x q y ^ 5 • y = y := by
  set F := fivePrd p x q y with hF
  have h1 : F • p = x + q + y := fivePrd_smul_p hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy
  have h2 : F • x = p + x + q := fivePrd_smul_x hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy
  have h3 : F • q = p + q := fivePrd_smul_q hpp hxx hqq hyy hpq hxq hqy
  have h4 : F • y = x + y := fivePrd_smul_y hpp hxx hqq hyy hpx hpy hxy hqy
  have hA : F • (x + q + y) = y := by
    rw [smul_add, smul_add, h2, h3, h4]
    linear_combination (norm := module) two_eq_zero • (p + x + q)
  have hB : F • (x + y) = p + q + y := by
    rw [smul_add, h2, h4]
    linear_combination (norm := module) two_eq_zero • x
  have hC : F • (p + q + y) = p := by
    rw [smul_add, smul_add, h1, h3, h4]
    linear_combination (norm := module) two_eq_zero • (x + q + y)
  have hD : F • (p + x + q) = q + y := by
    rw [smul_add, smul_add, h1, h2, h3]
    linear_combination (norm := module) two_eq_zero • (p + x + q)
  have hE : F • (q + y) = p + x + q + y := by
    rw [smul_add, h3, h4]
    abel
  have hG : F • (p + x + q + y) = x + q := by
    rw [smul_add, smul_add, smul_add, h1, h2, h3, h4]
    linear_combination (norm := module) two_eq_zero • (p + x + q + y)
  have hH : F • (x + q) = x := by
    rw [smul_add, h2, h3]
    linear_combination (norm := module) two_eq_zero • (p + q)
  have hI : F • (p + q) = p + x + y := by
    rw [smul_add, h1, h3]
    linear_combination (norm := module) two_eq_zero • q
  have hJ : F • (p + x + y) = p + x := by
    rw [smul_add, smul_add, h1, h2, h4]
    linear_combination (norm := module) two_eq_zero • (x + q + y)
  have hL : F • (p + x) = p + y := by
    rw [smul_add, h1, h2]
    linear_combination (norm := module) two_eq_zero • (x + q)
  have hN : F • (p + y) = q := by
    rw [smul_add, h1, h4]
    linear_combination (norm := module) two_eq_zero • (x + y)
  have e5 : ∀ v : Fin n → K, F ^ 5 • v = F • F • F • F • F • v := by
    intro v
    simp only [pow_succ, pow_zero, one_mul, mul_smul]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e5]
  · rw [h1, hA, h4, hB, hC]
  · rw [h2, hD, hE, hG, hH]
  · rw [h3, hI, hJ, hL, hN]
  · rw [h4, hB, hC, h1, hA]

theorem fivePrd_pow_five : fivePrd p x q y ^ 5 = 1 := by
  obtain ⟨hp5, hx5, hq5, hy5⟩ :=
    fivePrd_pow_five_smul_frame hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy
  have hqp : herm frob q p = 1 := by rw [herm_conj frob frob_frob p q, hpq, map_one]
  have hyx : herm frob y x = 1 := by rw [herm_conj frob frob_frob x y, hxy, map_one]
  have hxp : herm frob x p = 0 := herm_eq_zero_comm frob frob_frob hpx
  have hyp : herm frob y p = 0 := herm_eq_zero_comm frob frob_frob hpy
  have hqx : herm frob q x = 0 := herm_eq_zero_comm frob frob_frob hxq
  have hyq : herm frob y q = 0 := herm_eq_zero_comm frob frob_frob hqy
  refine ext_smul _ fun z => ?_
  set u := herm frob q z • p + herm frob y z • x + herm frob p z • q + herm frob x z • y
    with hu
  set z' := z - u with hz'
  have hpz' : herm frob p z' = 0 := by
    simp only [hz', hu, herm_sub_right, herm_add_right, herm_smul_right, hpp, hpx, hpq, hpy]
    ring
  have hxz' : herm frob x z' = 0 := by
    simp only [hz', hu, herm_sub_right, herm_add_right, herm_smul_right, hxp, hxx, hxq, hxy]
    ring
  have hqz' : herm frob q z' = 0 := by
    simp only [hz', hu, herm_sub_right, herm_add_right, herm_smul_right, hqp, hqx, hqq, hqy]
    ring
  have hyz' : herm frob y z' = 0 := by
    simp only [hz', hu, herm_sub_right, herm_add_right, herm_smul_right, hyp, hyx, hyq, hyy]
    ring
  have hfix : ∀ k : ℕ, fivePrd p x q y ^ k • z' = z' := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ k ih =>
      rw [pow_succ, mul_smul,
        fivePrd_smul_of_perp hpp hxx hqq hyy hqy hpz' hxz' hqz' hyz', ih]
  have hz : z = u + z' := by rw [hz']; abel
  rw [hz, smul_add, hfix, hu, smul_add, smul_add, smul_add, smul_comm _ (herm frob q z) p,
    smul_comm _ (herm frob y z) x, smul_comm _ (herm frob p z) q,
    smul_comm _ (herm frob x z) y, hp5, hx5, hq5, hy5, one_smul]

theorem fivePrd_not_mem_center (hn : 3 ≤ n) :
    fivePrd p x q y ∉ Subgroup.center (SUid frob n) := by
  intro hc
  rw [center_SUid hn] at hc
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hc
  have h := congrArg (herm frob p) (hc p)
  rw [fivePrd_smul_p hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy, herm_smul_right, hpp, mul_zero]
    at h
  simp only [herm_add_right, hpx, hpq, hpy, zero_add, add_zero] at h
  exact one_ne_zero h

end Prd

section Conj

variable {e : SUid frob n} (he : e * e = 1) {p x q y : Fin n → K}
  (hNp : invN e p = 0) (hNx : invN e x = 0) (hNq : invN e q = p) (hNy : invN e y = x)
  (hpp : herm frob p p = 0) (hxx : herm frob x x = 0) (hqq : herm frob q q = 0)
  (hyy : herm frob y y = 0) (hpx : herm frob p x = 0) (hpq : herm frob p q = 1)
  (hpy : herm frob p y = 0) (hxq : herm frob x q = 0) (hxy : herm frob x y = 1)
  (hqy : herm frob q y = 0)
include he hNp hNx hNq hNy hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy

theorem mul_conj_eq_fivePrd :
    e * ((tvU (x + y) * tvU (p + x + q)) * e * (tvU (x + y) * tvU (p + x + q))⁻¹) =
      fivePrd p x q y := by
  have hxp : herm frob x p = 0 := herm_eq_zero_comm frob frob_frob hpx
  have hyp : herm frob y p = 0 := herm_eq_zero_comm frob frob_frob hpy
  have hqx : herm frob q x = 0 := herm_eq_zero_comm frob frob_frob hxq
  have hyq : herm frob y q = 0 := herm_eq_zero_comm frob frob_frob hqy
  have hqp : herm frob q p = 1 := by rw [herm_conj frob frob_frob p q, hpq, map_one]
  have hyx : herm frob y x = 1 := by rw [herm_conj frob frob_frob x y, hxy, map_one]
  have hep : e • p = p := (invN_eq_zero_iff e p).1 hNp
  have hex : e • x = x := (invN_eq_zero_iff e x).1 hNx
  have heq : e • q = p + q := by rw [smul_eq_invN_add, hNq]
  have hey : e • y = x + y := by rw [smul_eq_invN_add, hNy]
  have hA : herm frob (x + y) (x + y) = 0 := by
    simp only [herm_add_left, herm_add_right, hxx, hyy, hxy, hyx, add_zero, zero_add]
    exact add_self_K 1
  have hB : herm frob (p + x + q) (p + x + q) = 0 := by
    simp only [herm_add_left, herm_add_right, hpp, hxx, hqq, hpx, hpq, hxq, hxp, hqp, hqx,
      add_zero, zero_add]
    exact add_self_K 1
  have hC : herm frob (q + y) (q + y) = 0 := herm_qy_qy hqq hyy hqy
  set R := tvU x * tvU p * e with hRdef
  have hRp : R • p = p := by
    rw [hRdef, mul_smul, mul_smul, hep, tvU_smul_self hpp, tvU_smul_of_herm_eq_zero hxx hxp]
  have hRx : R • x = x := by
    rw [hRdef, mul_smul, mul_smul, hex, tvU_smul_of_herm_eq_zero hpp hpx, tvU_smul_self hxx]
  have hRq : R • q = q := by
    rw [hRdef, mul_smul, mul_smul, heq, tvU_smul hpp, herm_add_right, hpp, hpq, zero_add,
      one_smul, tvU_smul_of_herm_eq_zero hxx (by
        simp only [herm_add_right, hxp, hxq, add_zero])]
    linear_combination (norm := module) two_eq_zero • p
  have hRy : R • y = y := by
    rw [hRdef, mul_smul, mul_smul, hey, tvU_smul_of_herm_eq_zero hpp (by
        simp only [herm_add_right, hpx, hpy, add_zero]), tvU_smul hxx, herm_add_right, hxx,
      hxy, zero_add, one_smul]
    linear_combination (norm := module) two_eq_zero • x
  have hRA : R • (x + y) = x + y := by rw [smul_add, hRx, hRy]
  have hRB : R • (p + x + q) = p + x + q := by rw [smul_add, smul_add, hRp, hRx, hRq]
  have hRC : R • (q + y) = q + y := by rw [smul_add, hRq, hRy]
  have heR : e = tvU p * tvU x * R := by
    rw [hRdef, show tvU p * tvU x * (tvU x * tvU p * e) = tvU p * (tvU x * tvU x) * tvU p * e
      by group, tvU_mul_self hxx, mul_one, tvU_mul_self hpp, one_mul]
  have hRR : R * R = 1 := by
    have h1 : e * (tvU x * tvU p) = tvU x * tvU p * e := by
      rw [← mul_assoc, mul_tvU_comm_of_smul_eq hxx hex, mul_assoc,
        mul_tvU_comm_of_smul_eq hpp hep, mul_assoc]
    have h2 : tvU x * tvU p * (tvU x * tvU p) = 1 := by
      rw [show tvU x * tvU p * (tvU x * tvU p) = tvU x * (tvU p * tvU x) * tvU p by group,
        ← tvU_commute hxx hpp (herm_eq_zero_comm frob frob_frob hpx),
        show tvU x * (tvU x * tvU p) * tvU p = (tvU x * tvU x) * (tvU p * tvU p) by group,
        tvU_mul_self hxx, tvU_mul_self hpp, one_mul]
    rw [hRdef, show tvU x * tvU p * e * (tvU x * tvU p * e) =
      tvU x * tvU p * (e * (tvU x * tvU p)) * e by group, h1,
      show tvU x * tvU p * (tvU x * tvU p * e) * e = tvU x * tvU p * (tvU x * tvU p) * (e * e)
      by group, h2, he, one_mul]
  set g := tvU (x + y) * tvU (p + x + q) with hgdef
  have hgR : g * R = R * g := by
    rw [hgdef, show tvU (x + y) * tvU (p + x + q) * R = tvU (x + y) * (tvU (p + x + q) * R)
      by group, ← mul_tvU_comm_of_smul_eq hB hRB,
      show tvU (x + y) * (R * tvU (p + x + q)) = (tvU (x + y) * R) * tvU (p + x + q) by group,
      ← mul_tvU_comm_of_smul_eq hA hRA]
    group
  have hgp : g • p = q + y := by
    rw [hgdef, mul_smul, tvU_smul hB, tvU_smul hA]
    simp only [herm_add_left, herm_add_right, hpp, hxp, hqp, hxx, hxq, hyx, hyp,
      hyq, add_zero, zero_add, one_smul]
    linear_combination (norm := module) two_eq_zero • (p + x)
  have hgx : g • x = y := by
    rw [hgdef, mul_smul, tvU_smul_of_herm_eq_zero hB (by
        simp only [herm_add_left, hpx, hxx, hqx, add_zero]), tvU_smul hA]
    simp only [herm_add_left, hxx, hyx, zero_add, one_smul]
    linear_combination (norm := module) two_eq_zero • x
  have hge : g * e * g⁻¹ = tvU (q + y) * tvU y * R := by
    have hgRg : g * R * g⁻¹ = R := by rw [hgR, mul_inv_cancel_right]
    conv_lhs => rw [heR]
    rw [show g * (tvU p * tvU x * R) * g⁻¹ =
      (g * tvU p * g⁻¹) * (g * tvU x * g⁻¹) * (g * R * g⁻¹) by group, conj_tvU g hpp,
      conj_tvU g hxx, hgRg, hgp, hgx]
  rw [hge]
  conv_lhs => rw [heR]
  rw [show tvU p * tvU x * R * (tvU (q + y) * tvU y * R) =
    tvU p * tvU x * (R * tvU (q + y)) * tvU y * R by group,
    mul_tvU_comm_of_smul_eq hC hRC,
    show tvU p * tvU x * (tvU (q + y) * R) * tvU y * R =
      tvU p * tvU x * tvU (q + y) * (R * tvU y) * R by group,
    mul_tvU_comm_of_smul_eq hyy hRy,
    show tvU p * tvU x * tvU (q + y) * (tvU y * R) * R =
      tvU p * tvU x * tvU (q + y) * tvU y * (R * R) by group, hRR, mul_one]
  rfl

end Conj

theorem mem_DG_of_orderOf_mul_conj_le_four (hn : 3 ≤ n) {e : PG n} (he2 : orderOf e = 2)
    (h4 : ∀ c : PG n, orderOf (e * (c * e * c⁻¹)) ∈ ({1, 2, 3, 4} : Set ℕ)) : e ∈ DG n := by
  obtain ⟨e₀, rfl⟩ := QuotientGroup.mk_surjective e
  have hee : (QuotientGroup.mk e₀ : PG n) * QuotientGroup.mk e₀ = 1 := by
    have h := pow_orderOf_eq_one (QuotientGroup.mk e₀ : PG n)
    rwa [he2, sq] at h
  have hcen : e₀ * e₀ ∈ Subgroup.center (SUid frob n) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, hee]
  set e₁ := e₀ * e₀ * e₀ with he₁
  have he₁e₁ : e₁ * e₁ = 1 := by
    have h := AS35U.pow_three_eq_one_of_mem_center hn hcen
    rw [show e₁ * e₁ = (e₀ * e₀) ^ 3 by
      rw [he₁]; simp only [pow_succ, pow_zero, one_mul, mul_assoc], h]
  have hmk : (QuotientGroup.mk e₁ : PG n) = QuotientGroup.mk e₀ := by
    rw [he₁, QuotientGroup.mk_mul, QuotientGroup.mk_mul, hee, one_mul]
  have hne : (QuotientGroup.mk e₀ : PG n) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at he2
    exact absurd he2 (by norm_num)
  by_cases hall : ∀ a, herm frob a (invN e₁ a) = 0
  · exfalso
    apply hne
    rw [← hmk, show e₁ = 1 from ext_smul _ fun b => by
      rw [smul_eq_invN_add, invN_eq_zero_of_diag he₁e₁ hall, zero_add, one_smul],
      QuotientGroup.mk_one]
  push Not at hall
  obtain ⟨q₀, hq₀⟩ := hall
  have hq₁ := (herm_invN_self he₁e₁ q₀).resolve_left hq₀
  by_cases hrank : ∀ y, herm frob q₀ (invN e₁ y) = 0 → herm frob y (invN e₁ y) = 0
  · obtain ⟨hp0, hpp, heq⟩ := eq_tvU_of_rank_one he₁e₁ hq₁ hrank
    rw [← hmk, heq]
    exact tq_mem_DG hp0 hpp
  push Not at hrank
  obtain ⟨y₀, hqy, hy₀⟩ := hrank
  have hy₁ := (herm_invN_self he₁e₁ y₀).resolve_left hy₀
  obtain ⟨p, x, q, y, hNp, hNx, hNq, hNy, hpp, hxx, hqq, hyy, hpx, hpq, hpy, hxq, hxy, hqy⟩ :=
    exists_frame he₁e₁ hq₁ hy₁ hqy
  exfalso
  set g := tvU (x + y) * tvU (p + x + q) with hg
  have hF := mul_conj_eq_fivePrd he₁e₁ hNp hNx hNq hNy hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy
  have h := h4 (QuotientGroup.mk g)
  rw [← hmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, hF] at h
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : orderOf (QuotientGroup.mk (fivePrd p x q y) : PG n) = 5 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← QuotientGroup.mk_pow, fivePrd_pow_five hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy,
        QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact fivePrd_not_mem_center hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy hn
  rw [h5] at h
  norm_num at h

end CFSG.LargeExtraspecial.AS35Z
