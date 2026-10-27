module

public import CFSG.LargeExtraspecial.AS35LInvA
public import CFSG.LargeExtraspecial.AS35U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35L

open Matrix CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.Fischer.Classification.Unitary
open CFSG.Blueprint.Fischer (K)

variable {n : ℕ}

@[expose] noncomputable def framePrd (p x y : Fin n → K) : SUid frob n :=
  tvU p * tvU x * tvU (p + x + y) * tvU (x + y)

section Prd

variable {p x y : Fin n → K} (hpp : herm frob p p = 0) (hxx : herm frob x x = 0)
  (hyy : herm frob y y = 0) (hpx : herm frob p x = 0) (hpy : herm frob p y = 0)
  (hxy : herm frob x y = 1)
include hpp hxx hyy hpx hpy hxy

theorem framePrd_smul (z : Fin n → K) :
    framePrd p x y • z =
      z + (herm frob x z + herm frob y z) • p + herm frob x z • x + herm frob p z • y := by
  have hxp : herm frob x p = 0 := herm_eq_zero_comm frob frob_frob hpx
  have hyp : herm frob y p = 0 := herm_eq_zero_comm frob frob_frob hpy
  have hyx : herm frob y x = 1 := by rw [herm_conj frob frob_frob x y, hxy, map_one]
  have hb : herm frob (x + y) (x + y) = 0 := by
    simp only [herm_add_left, herm_add_right, hxx, hyy, hxy, hyx, add_zero, zero_add]
    exact add_self_K 1
  have ha : herm frob (p + x + y) (p + x + y) = 0 := by
    simp only [herm_add_left, herm_add_right, hpp, hxx, hyy, hpx, hpy, hxp, hyp, hxy, hyx,
      add_zero, zero_add]
    exact add_self_K 1
  set α := herm frob p z
  set β := herm frob x z
  set γ := herm frob y z
  have h1 : tvU (x + y) • z = z + (β + γ) • (x + y) := by
    rw [tvU_smul hb, herm_add_left]
  have h2 : tvU (p + x + y) • (z + (β + γ) • (x + y)) =
      z + (β + γ) • (x + y) + (α + β + γ) • (p + x + y) := by
    rw [tvU_smul ha]
    congr 2
    simp only [herm_add_left, herm_add_right, herm_smul_right, hpx, hpy, hxx, hxy, hyx, hyy]
    linear_combination (β + γ) * two_eq_zero
  have h3 : tvU x • (z + (β + γ) • (x + y) + (α + β + γ) • (p + x + y)) =
      z + (β + γ) • (x + y) + (α + β + γ) • (p + x + y) + (α + β) • x := by
    rw [tvU_smul hxx]
    congr 2
    simp only [herm_add_right, herm_smul_right, hxx, hxy, hxp]
    linear_combination (β + γ) * two_eq_zero
  have h4 : tvU p • (z + (β + γ) • (x + y) + (α + β + γ) • (p + x + y) + (α + β) • x) =
      z + (β + γ) • (x + y) + (α + β + γ) • (p + x + y) + (α + β) • x + α • p := by
    rw [tvU_smul hpp]
    congr 2
    simp only [herm_add_right, herm_smul_right, hpp, hpx, hpy]
    ring
  rw [framePrd, mul_smul, mul_smul, mul_smul, h1, h2, h3, h4]
  linear_combination (norm := module) two_eq_zero • (α • p + (α + β + γ) • x + (β + γ) • y)

theorem framePrd_sq_smul (z : Fin n → K) :
    (framePrd p x y * framePrd p x y) • z =
      z + (herm frob p z + herm frob x z) • p + herm frob p z • x := by
  have hxp : herm frob x p = 0 := herm_eq_zero_comm frob frob_frob hpx
  have hyp : herm frob y p = 0 := herm_eq_zero_comm frob frob_frob hpy
  have hyx : herm frob y x = 1 := by rw [herm_conj frob frob_frob x y, hxy, map_one]
  rw [mul_smul, framePrd_smul hpp hxx hyy hpx hpy hxy z,
    framePrd_smul hpp hxx hyy hpx hpy hxy]
  simp only [herm_add_right, herm_smul_right, hpp, hxx, hyy, hpx, hpy, hxp, hyp, hxy, hyx,
    mul_zero, mul_one, add_zero]
  linear_combination (norm := module) two_eq_zero •
    ((herm frob x z + herm frob y z) • p + herm frob x z • x + herm frob p z • y)

theorem framePrd_pow_four : framePrd p x y ^ 4 = 1 := by
  have hxp : herm frob x p = 0 := herm_eq_zero_comm frob frob_frob hpx
  refine ext_smul _ fun z => ?_
  rw [show framePrd p x y ^ 4 = (framePrd p x y * framePrd p x y) *
    (framePrd p x y * framePrd p x y) by rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq],
    mul_smul, framePrd_sq_smul hpp hxx hyy hpx hpy hxy z,
    framePrd_sq_smul hpp hxx hyy hpx hpy hxy, one_smul]
  simp only [herm_add_right, herm_smul_right, hpp, hpx, hxp, hxx, mul_zero, add_zero]
  linear_combination (norm := module) two_eq_zero •
    ((herm frob p z + herm frob x z) • p + herm frob p z • x)

end Prd

theorem mul_tvU_comm_of_smul_eq {R : SUid frob n} {w : Fin n → K} (hw : herm frob w w = 0)
    (hR : R • w = w) : R * tvU w = tvU w * R := by
  have h := conj_tvU R hw
  rw [hR] at h
  exact mul_inv_eq_iff_eq_mul.mp h

section Conj

variable {e : SUid frob n} (he : e * e = 1) {p x q y : Fin n → K}
  (hNp : invN e p = 0) (hNx : invN e x = 0) (hNq : invN e q = p) (hNy : invN e y = x)
  (hpp : herm frob p p = 0) (hxx : herm frob x x = 0) (hqq : herm frob q q = 0)
  (hyy : herm frob y y = 0) (hpx : herm frob p x = 0) (hpq : herm frob p q = 1)
  (hpy : herm frob p y = 0) (hxq : herm frob x q = 0) (hxy : herm frob x y = 1)
  (hqy : herm frob q y = 0)
include he hNp hNx hNq hNy hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy

theorem mul_conj_eq_framePrd :
    e * ((tvU q * tvU y * tvU (x + q)) * e * (tvU q * tvU y * tvU (x + q))⁻¹) =
      framePrd p x y := by
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
  have hxq' : herm frob (x + q) (x + q) = 0 := by
    simp only [herm_add_left, herm_add_right, hxx, hxq, hqx, hqq, add_zero]
  have hA : herm frob (p + x + y) (p + x + y) = 0 := by
    simp only [herm_add_left, herm_add_right, hpp, hxx, hyy, hpx, hpy, hxp, hyp, hxy, hyx,
      add_zero, zero_add]
    exact add_self_K 1
  have hB : herm frob (x + y) (x + y) = 0 := by
    simp only [herm_add_left, herm_add_right, hxx, hyy, hxy, hyx, add_zero, zero_add]
    exact add_self_K 1
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
  have hRxq : R • (x + q) = x + q := by rw [smul_add, hRx, hRq]
  have hRA : R • (p + x + y) = p + x + y := by rw [smul_add, smul_add, hRp, hRx, hRy]
  have hRB : R • (x + y) = x + y := by rw [smul_add, hRx, hRy]
  have heR : e = tvU p * tvU x * R := by
    rw [hRdef, show tvU p * tvU x * (tvU x * tvU p * e) = tvU p * (tvU x * tvU x) * tvU p * e
      by group, tvU_mul_self hxx, mul_one, tvU_mul_self hpp, one_mul]
  have hRR : R * R = 1 := by
    have h1 : e * (tvU x * tvU p) = tvU x * tvU p * e := by
      rw [← mul_assoc, mul_tvU_comm_of_smul_eq hxx hex, mul_assoc, mul_tvU_comm_of_smul_eq hpp hep,
        mul_assoc]
    have h2 : tvU x * tvU p * (tvU x * tvU p) = 1 := by
      rw [show tvU x * tvU p * (tvU x * tvU p) = tvU x * (tvU p * tvU x) * tvU p by group,
        ← tvU_commute hxx hpp (herm_eq_zero_comm frob frob_frob hpx),
        show tvU x * (tvU x * tvU p) * tvU p = (tvU x * tvU x) * (tvU p * tvU p) by group,
        tvU_mul_self hxx, tvU_mul_self hpp, one_mul]
    rw [hRdef, show tvU x * tvU p * e * (tvU x * tvU p * e) =
      tvU x * tvU p * (e * (tvU x * tvU p)) * e by group, h1,
      show tvU x * tvU p * (tvU x * tvU p * e) * e = tvU x * tvU p * (tvU x * tvU p) * (e * e)
      by group, h2, he, one_mul]
  set g := tvU q * tvU y * tvU (x + q) with hgdef
  have hgR : g * R = R * g := by
    rw [hgdef, show tvU q * tvU y * tvU (x + q) * R = tvU q * tvU y * (tvU (x + q) * R) by group,
      ← mul_tvU_comm_of_smul_eq hxq' hRxq,
      show tvU q * tvU y * (R * tvU (x + q)) = tvU q * (tvU y * R) * tvU (x + q) by group,
      ← mul_tvU_comm_of_smul_eq hyy hRy,
      show tvU q * (R * tvU y) * tvU (x + q) = (tvU q * R) * tvU y * tvU (x + q) by group,
      ← mul_tvU_comm_of_smul_eq hqq hRq]
    group
  have hgp : g • p = p + x + y := by
    rw [hgdef, mul_smul, mul_smul, tvU_smul hxq', tvU_smul hyy, tvU_smul hqq]
    simp only [herm_add_left, herm_add_right, herm_smul_right, hxp, hqp, hyp, hyx, hyq, hqx,
      hqq, hqy]
    linear_combination (norm := module) two_eq_zero • q
  have hgx : g • x = x + y := by
    rw [hgdef, mul_smul, mul_smul, tvU_smul_of_herm_eq_zero hxq' (by
        simp only [herm_add_left, hxx, hqx, add_zero]), tvU_smul hyy, hyx, one_smul,
      tvU_smul_of_herm_eq_zero hqq (by simp only [herm_add_right, hqx, hqy, add_zero])]
  have hge : g * e * g⁻¹ = tvU (p + x + y) * tvU (x + y) * R := by
    have hgRg : g * R * g⁻¹ = R := by rw [hgR, mul_inv_cancel_right]
    conv_lhs => rw [heR]
    rw [show g * (tvU p * tvU x * R) * g⁻¹ =
      (g * tvU p * g⁻¹) * (g * tvU x * g⁻¹) * (g * R * g⁻¹) by group, conj_tvU g hpp,
      conj_tvU g hxx, hgRg, hgp, hgx]
  rw [hge]
  conv_lhs => rw [heR]
  rw [show tvU p * tvU x * R * (tvU (p + x + y) * tvU (x + y) * R) =
    tvU p * tvU x * (R * tvU (p + x + y)) * tvU (x + y) * R by group,
    mul_tvU_comm_of_smul_eq hA hRA,
    show tvU p * tvU x * (tvU (p + x + y) * R) * tvU (x + y) * R =
      tvU p * tvU x * tvU (p + x + y) * (R * tvU (x + y)) * R by group,
    mul_tvU_comm_of_smul_eq hB hRB,
    show tvU p * tvU x * tvU (p + x + y) * (tvU (x + y) * R) * R =
      tvU p * tvU x * tvU (p + x + y) * tvU (x + y) * (R * R) by group, hRR, mul_one]
  rfl

end Conj

theorem eq_one_of_mem_center_of_smul_eq (hn : 3 ≤ n) {g : SUid frob n}
    (hg : g ∈ Subgroup.center (SUid frob n)) {v : Fin n → K} (hv0 : v ≠ 0) (hv : g • v = v) :
    g = 1 := by
  rw [center_SUid hn] at hg
  obtain ⟨c, hc⟩ := exists_smul_eq_of_mem_scalars hg
  have hc1 : c = 1 := by
    have h1 : (c - 1) • v = 0 := by rw [sub_smul, one_smul, ← hc, hv, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h1).resolve_right hv0)
  exact ext_smul _ fun z => by rw [hc, hc1, one_smul, one_smul]

theorem mem_DG_of_orderOf_mul_conj (hn : 3 ≤ n) {e : PG n} (he2 : orderOf e = 2)
    (h3 : ∀ c : PG n, orderOf (e * (c * e * c⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) : e ∈ DG n := by
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
  set g := tvU q * tvU y * tvU (x + q) with hg
  have hP := mul_conj_eq_framePrd he₁e₁ hNp hNx hNq hNy hpp hxx hqq hyy hpx hpq hpy hxq hxy hqy
  have h := h3 (QuotientGroup.mk g)
  rw [← hmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul, hP] at h
  have hxp : herm frob x p = 0 := herm_eq_zero_comm frob frob_frob hpx
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [herm_zero_left] at hpq
    exact zero_ne_one hpq
  have hnot : ¬ (QuotientGroup.mk (framePrd p x y) : PG n) ^ 2 ^ 1 = 1 := by
    intro h2
    rw [pow_one, sq, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff] at h2
    have h1 := eq_one_of_mem_center_of_smul_eq hn h2 hp0 (by
      rw [framePrd_sq_smul hpp hxx hyy hpx hpy hxy, hpp, hxp, add_zero, zero_smul, zero_smul,
        add_zero, add_zero])
    have hq := framePrd_sq_smul hpp hxx hyy hpx hpy hxy q
    rw [h1, one_smul, hpq, hxq, add_zero, one_smul, one_smul, add_assoc] at hq
    have hpx0 : p + x = 0 := by
      have := congrArg (fun v => v + q) hq
      simpa [add_comm q, add_assoc, vec_add_self] using this.symm
    have := congrArg (herm frob · y) hpx0
    simp only [herm_add_left, hpy, hxy, zero_add, herm_zero_left] at this
    exact one_ne_zero this
  have hfin : (QuotientGroup.mk (framePrd p x y) : PG n) ^ 2 ^ (1 + 1) = 1 := by
    rw [← QuotientGroup.mk_pow, show 2 ^ (1 + 1) = 4 by norm_num,
      framePrd_pow_four hpp hxx hyy hpx hpy hxy, QuotientGroup.mk_one]
  have h4 := orderOf_eq_prime_pow (p := 2) hnot hfin
  rw [h4] at h
  norm_num at h

end CFSG.LargeExtraspecial.AS35L
