module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAut74Cnt
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Outside.OutAut74Phi

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.Outside

open Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.GH74.GLS.Bg.TwoGroups.L23

@[expose] def Oq : Subgroup (Equiv.Perm V4) where
  carrier := {h | (∀ v w, h (v + w) = h v + h w) ∧ ∀ v, sqF (h v) = sqF v}
  mul_mem' := by
    intro h1 h2 h1m h2m
    refine ⟨?_, ?_⟩
    · intro v w
      calc (h1 * h2) (v + w) = h1 (h2 (v + w)) := Equiv.Perm.mul_apply h1 h2 (v + w)
        _ = h1 (h2 v + h2 w) := by rw [h2m.1]
        _ = h1 (h2 v) + h1 (h2 w) := h1m.1 (h2 v) (h2 w)
        _ = (h1 * h2) v + (h1 * h2) w := by
              rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    · intro v
      calc sqF ((h1 * h2) v) = sqF (h1 (h2 v)) := by rw [Equiv.Perm.mul_apply]
        _ = sqF (h2 v) := h1m.2 (h2 v)
        _ = sqF v := h2m.2 v
  one_mem' := by
    refine ⟨?_, ?_⟩
    · intro v w; rfl
    · intro v; rfl
  inv_mem' := by
    intro h hm
    refine ⟨?_, ?_⟩
    · intro v w
      apply Equiv.injective h
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply, hm.1, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply]
    · intro v
      have hh := hm.2 (h⁻¹ v)
      rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply] at hh
      exact hh.symm

private lemma oq_tup_mem (h : Oq) : tupOf h.1 ∈ oneTuples := by
  let g : V4 →+ V4 := AddMonoidHom.mk' h.1 h.2.1
  have hg : ⇑g = ⇑h.1 := rfl
  have hq : ∀ v, sqF (g v) = sqF v := by
    intro v
    rw [show g v = h.1 v from rfl]
    exact h.2.2 v
  have hmem := tupOf_mem_oneTuples g (by rw [hg]; exact Equiv.injective h.1) hq
  have htup : tupOf g = tupOf h.1 := by simp only [tupOf, hg]
  rwa [htup] at hmem

private lemma oq_tup_injective : Function.Injective (fun h : Oq => tupOf h.1) := by
  intro h1 h2 h
  let g1 : V4 →+ V4 := AddMonoidHom.mk' h1.1 h1.2.1
  let g2 : V4 →+ V4 := AddMonoidHom.mk' h2.1 h2.2.1
  have hg1 : ⇑g1 = ⇑h1.1 := rfl
  have hg2 : ⇑g2 = ⇑h2.1 := rfl
  have htup1 : tupOf g1 = tupOf h1.1 := by simp only [tupOf, hg1]
  have htup2 : tupOf g2 = tupOf h2.1 := by simp only [tupOf, hg2]
  have htup : tupOf g1 = tupOf g2 := by
    rw [htup1, htup2]
    exact h
  have hg : g1 = g2 := tupOf_injective htup
  have hfun : h1.1 = h2.1 := by
    apply Equiv.ext
    intro v
    exact congrArg (fun f : V4 →+ V4 => f v) hg
  exact Subtype.ext hfun

private def oqTup (h : Oq) : ↥(oneTuples.toFinset) :=
  ⟨tupOf h.1, by
    rw [List.mem_toFinset]
    exact oq_tup_mem h⟩

theorem card_Oq_le : Nat.card Oq ≤ 6 := by
  have hinj : Function.Injective oqTup := by
    intro h1 h2 h
    exact oq_tup_injective (congrArg Subtype.val h)
  have h := Nat.card_le_card_of_injective oqTup hinj
  have hcard : Nat.card ↥(oneTuples.toFinset) ≤ 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    calc oneTuples.toFinset.card ≤ oneTuples.length := List.toFinset_card_le oneTuples
      _ = 6 := length_oneTuples
  exact h.trans hcard

private lemma omg_mul_omgSq_mul (a : F4c) : omg * (omg * omg * a) = a := by
  revert a; decide +kernel

private lemma omgSq_mul_omg_mul (a : F4c) : omg * omg * (omg * a) = a := by
  revert a; decide +kernel

private lemma omg_pow_three_mul (a : F4c) : omg * (omg * (omg * a)) = a := by
  revert a; decide +kernel

private lemma omgSq_pow_three_mul (a : F4c) :
    (omg * omg) * ((omg * omg) * ((omg * omg) * a)) = a := by
  revert a; decide +kernel

private lemma omg_mul_sq (a b : F4c) : omg * a * (omg * omg * b) = a * b := by
  revert a b; decide +kernel

private def omgPerm : Equiv.Perm V4 where
  toFun v := (omg * v.1, (omg * omg) * v.2)
  invFun v := ((omg * omg) * v.1, omg * v.2)
  left_inv v := by
    refine Prod.ext ?_ ?_
    · exact omgSq_mul_omg_mul v.1
    · exact omg_mul_omgSq_mul v.2
  right_inv v := by
    refine Prod.ext ?_ ?_
    · exact omg_mul_omgSq_mul v.1
    · exact omgSq_mul_omg_mul v.2

private lemma omgPerm_add (v w : V4) : omgPerm (v + w) = omgPerm v + omgPerm w := by
  refine Prod.ext ?_ ?_
  · show omg * (v.1 + w.1) = omg * v.1 + omg * w.1
    rw [mul_add]
  · show (omg * omg) * (v.2 + w.2) = (omg * omg) * v.2 + (omg * omg) * w.2
    rw [mul_add]

private lemma omgPerm_sqF (v : V4) : sqF (omgPerm v) = sqF v := by
  show (omg * v.1) * ((omg * omg) * v.2) = v.1 * v.2
  exact omg_mul_sq v.1 v.2

private lemma omgPerm_mem : omgPerm ∈ Oq := ⟨omgPerm_add, omgPerm_sqF⟩

private lemma omgPerm_pow_three : omgPerm ^ 3 = 1 := by
  apply Equiv.ext
  intro v
  show omgPerm (omgPerm (omgPerm v)) = v
  refine Prod.ext ?_ ?_
  · exact omg_pow_three_mul v.1
  · exact omgSq_pow_three_mul v.2

private lemma omg_ne_one : omg ≠ 1 := by decide +kernel

private lemma omgPerm_ne_one : omgPerm ≠ 1 := by
  intro h
  have h2 := congrArg (fun e : Equiv.Perm V4 => e ((1 : F4c), 0)) h
  have h3 : omg = 1 := by
    have hf := congrArg Prod.fst h2
    simpa [omgPerm] using hf
  exact omg_ne_one h3

private lemma orderOf_omgPerm : orderOf omgPerm = 3 :=
  orderOf_eq_prime omgPerm_pow_three omgPerm_ne_one

theorem three_dvd_card_Oq : 3 ∣ Nat.card Oq := by
  let h0 : Oq := ⟨omgPerm, omgPerm_mem⟩
  have hord : orderOf h0 = 3 := by
    rw [Subgroup.orderOf_mk omgPerm omgPerm_mem]
    exact orderOf_omgPerm
  rw [← hord]
  exact orderOf_dvd_natCard h0

theorem card_le_two_of_pgroup (H : Subgroup (Equiv.Perm V4)) (hH : H ≤ Oq) (hp : IsPGroup 2 H) :
    Nat.card H ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hposO : 0 < Nat.card Oq := by
    haveI : Nonempty Oq := ⟨1⟩
    exact Nat.card_pos
  have hHdvd : Nat.card H ∣ Nat.card Oq := Subgroup.card_dvd_of_le hH
  have hHle : Nat.card H ≤ Nat.card Oq := Nat.le_of_dvd hposO hHdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hp
  have hk6 : 2 ^ k ≤ 6 := by
    calc 2 ^ k = Nat.card H := hk.symm
      _ ≤ Nat.card Oq := hHle
      _ ≤ 6 := card_Oq_le
  have hk2 : k ≤ 2 := by
    by_contra h
    push Not at h
    have h8dvd : 2 ^ 3 ∣ 2 ^ k := pow_dvd_pow 2 h
    have h8le : 2 ^ 3 ≤ 2 ^ k := Nat.le_of_dvd (Nat.pow_pos (by norm_num)) h8dvd
    norm_num at h8le
    omega
  interval_cases k
  · rw [hk]; norm_num
  · rw [hk]; norm_num
  · exfalso
    have hH4 : Nat.card H = 4 := by rw [hk]; norm_num
    have h4 : 4 ∣ Nat.card Oq := hH4 ▸ hHdvd
    obtain ⟨m, hm⟩ := h4
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h
      · subst h0; rw [mul_zero] at hm; omega
      · exact h
    have hmle : m ≤ 1 := by
      have h6 := card_Oq_le
      rw [hm] at h6
      omega
    have hm_eq : m = 1 := le_antisymm hmle hm1
    have hN4 : Nat.card Oq = 4 := by rw [hm, hm_eq, mul_one]
    have h3 : 3 ∣ Nat.card Oq := three_dvd_card_Oq
    rw [hN4] at h3
    obtain ⟨j, hj⟩ := h3
    omega

theorem index_chainStab_comap_le_two {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (φ : P →* MulAut U4) (hfix : ∀ p : P, ∀ z ∈ center U4, φ p z = z) :
    ((chainStab U4).comap φ).index ≤ 2 := by
  let ψ : P →* Equiv.Perm V4 := phi.comp φ
  have hker : (chainStab U4).comap φ = ψ.ker := by
    rw [← ker_phi]
    exact MonoidHom.comap_ker phi φ
  have hrange : ψ.range ≤ Oq := by
    rintro x ⟨p, rfl⟩
    exact ⟨phi_add (φ p), sqF_phi_of_fix (φ p) (hfix p)⟩
  have hpgroup : IsPGroup 2 ψ.range :=
    hP.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  rw [hker, Subgroup.index_ker ψ]
  exact card_le_two_of_pgroup ψ.range hrange hpgroup

end CFSG.OddStandard.SmallF3.HarrisU33.Outside
