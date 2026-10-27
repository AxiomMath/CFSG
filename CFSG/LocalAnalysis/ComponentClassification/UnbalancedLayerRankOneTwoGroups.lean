module

import CFSG.LocalAnalysis.SectionRank.GroupRankTransport
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Semidihedral.StructureTransport
public import CFSG.Foundations.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.UnbalancedLayer

open CFSG Subgroup

theorem pRank_eq_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y] {p : ℕ}
    (_hp : 1 < p) (e : X ≃* Y) : pRank p X = pRank p Y := CFSG.pRank_congr_of_mulEquiv e p

theorem not_isMulCommutative_of_quaternion {T : Type*} [Group T] {r : ℕ} (hr : 3 ≤ r)
    (e : T ≃* QuaternionGroup (2 ^ (r - 2))) : ¬ IsMulCommutative T := by
  intro hT
  have hm2 : 2 ≤ 2 ^ (r - 2) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (r - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h := congrArg e (hT.is_comm.comm (e.symm (QuaternionGroup.a 1))
    (e.symm (QuaternionGroup.xa 0)))
  simp only [map_mul, MulEquiv.apply_symm_apply, QuaternionGroup.a_mul_xa,
    QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq] at h
  have h2 : ((2 : ℕ) : ZMod (2 * 2 ^ (r - 2))) = 0 := by
    have : (0 : ZMod (2 * 2 ^ (r - 2))) - 1 - (0 + 1) = 0 := by rw [h, sub_self]
    have h' : -((2 : ℕ) : ZMod (2 * 2 ^ (r - 2))) = 0 := by
      rw [← this]
      push_cast
      ring
    exact neg_eq_zero.mp h'
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem sylow_quaternion_of_mulEquiv {X Y : Type*} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : ∀ T : Sylow 2 X, ∃ r : ℕ, 3 ≤ r ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (r - 2)))) :
    ∀ T : Sylow 2 Y, ∃ r : ℕ, 3 ≤ r ∧ Nonempty (T ≃* QuaternionGroup (2 ^ (r - 2))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y := Finite.of_equiv X e.toEquiv
  intro T
  obtain ⟨r, hr, ⟨eT⟩⟩ := h (T.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  refine ⟨r, hr, ⟨?_⟩⟩
  have e1 : (T : Subgroup Y) ≃* (T : Subgroup Y).map e.symm.toMonoidHom :=
    (T : Subgroup Y).equivMapOfInjective _ e.symm.injective
  exact e1.trans eT

theorem false_of_dihedral_of_unique_central_involution {P : Type*} [Group P] {m : ℕ}
    (hm : 3 ≤ m) (φ : P ≃* DihedralGroup m) {D : Subgroup P} (hD : ¬ IsMulCommutative D)
    {a : P} (haZ : a ∈ center P) (huniq : ∀ x ∈ D, orderOf x = 2 → x = a) : False := by
  obtain ⟨x, hxD, i, hxi⟩ : ∃ x ∈ D, ∃ i, φ x = DihedralGroup.sr i := by
    by_contra hnone
    push Not at hnone
    have hrot : ∀ y : D, ∃ i, φ y = DihedralGroup.r i := by
      intro y
      cases h : φ y with
      | r i => exact ⟨i, rfl⟩
      | sr i => exact absurd h (hnone y y.2 i)
    apply hD
    refine isMulCommutative_iff.mpr fun x y => Subtype.ext (φ.injective ?_)
    obtain ⟨i, hi⟩ := hrot x
    obtain ⟨j, hj⟩ := hrot y
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul, hi, hj, DihedralGroup.r_mul_r,
      DihedralGroup.r_mul_r, add_comm]
  have hx2 : orderOf x = 2 := by rw [← MulEquiv.orderOf_eq φ, hxi, DihedralGroup.orderOf_sr]
  have hxa := huniq x hxD hx2
  have hc := congrArg φ (mem_center_iff.mp haZ (φ.symm (DihedralGroup.r 1)))
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hxa, hxi, DihedralGroup.r_mul_sr,
    DihedralGroup.sr_mul_r, DihedralGroup.sr.injEq] at hc
  have h2 : ((2 : ℕ) : ZMod m) = 0 := by
    have : i - 1 - (i + 1) = (0 : ZMod m) := by rw [hc, sub_self]
    have h' : -((2 : ℕ) : ZMod m) = 0 := by
      rw [← this]
      push_cast
      ring
    exact neg_eq_zero.mp h'
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem index_eq_two_of_semidihedral {P : Type*} [Group P] [Finite P] {n : ℕ} (hn : 4 ≤ n)
    (f : Open.SemidihedralGroup n ≃* P) {D : Subgroup P} (hDn : D.Normal)
    (hD : ¬ IsMulCommutative D) {a : P} (haZ : a ∈ center P) (ha2 : orderOf a = 2)
    (huniq : ∀ x ∈ D, orderOf x = 2 → x = a) : D.index = 2 := by
  obtain ⟨hcen, -, -, hidx, -, -, -, -, -, -, -, -, -, hz2, -, hsq, -⟩ :=
    CFSG.Semidihedral.supplied_index_two_and_element_structure n hn f
  set r : P := f (CFSG.Semidihedral.r n) with hrdef
  set s : P := f (CFSG.Semidihedral.s n) with hsdef
  have hnf := CFSG.Semidihedral.normal_form n hn
  have hr : orderOf r = 2 ^ (n - 1) := by rw [hrdef, MulEquiv.orderOf_eq, hnf.2.2.1]
  have hs2 : orderOf s = 2 := by rw [hsdef, MulEquiv.orderOf_eq, hnf.2.2.2.1]
  have hsr : s * r * s⁻¹ = r ^ (2 ^ (n - 2) - 1) := by
    have h := congrArg f (CFSG.Semidihedral.s_conj_r n)
    simpa only [map_mul, map_inv, map_pow] using h
  have hform : ∀ g : P, ∃ i j : ℕ, j < 2 ∧ g = r ^ i * s ^ j := by
    intro g
    obtain ⟨c, hc, -⟩ := hnf.1 (f.symm g)
    refine ⟨c.1.val, c.2.val, c.2.isLt, ?_⟩
    rw [← f.apply_symm_apply g, hc, map_mul, map_pow, map_pow]
  set z : P := r ^ (2 ^ (n - 1) / 2) with hzdef
  have hzr : z ∈ zpowers r := pow_mem (mem_zpowers r) _
  have haz : a = z := by
    rw [hcen] at haZ
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp haZ
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · exfalso
      rw [← hk, ← zpow_mod_orderOf, hz2] at ha2
      norm_num [h] at ha2
    · rw [← hk, ← zpow_mod_orderOf, hz2]
      norm_num [h]
  obtain ⟨x, hxD, hxr⟩ : ∃ x ∈ D, x ∉ zpowers r := by
    by_contra hall
    push Not at hall
    apply hD
    refine isMulCommutative_iff.mpr fun x y => Subtype.ext ?_
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hall x x.2)
    obtain ⟨l, hl⟩ := mem_zpowers_iff.mp (hall y y.2)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
  obtain ⟨i, j, hj, hxij⟩ := hform x
  have hj1 : j = 1 := by
    rcases (by omega : j = 0 ∨ j = 1) with h | h
    · exfalso
      apply hxr
      rw [hxij, h, pow_zero, mul_one]
      exact pow_mem (mem_zpowers r) i
    · exact h
  rw [hj1, pow_one] at hxij
  have hsr' : s ∉ zpowers r := fun h => hxr (hxij ▸ mul_mem (pow_mem (mem_zpowers r) i) h)
  have hodd : Odd i := by
    by_contra heven
    rw [Nat.not_odd_iff_even] at heven
    obtain ⟨k, hk⟩ := heven
    have hx2 : x ^ 2 = 1 := by
      have h := hsq (i : ℤ)
      rw [zpow_natCast, zpow_natCast, ← hxij, hk, ← two_mul, pow_mul,
        (show z ^ 2 = 1 by rw [← hz2, pow_orderOf_eq_one]), one_pow] at h
      exact h
    have hx1 : x ≠ 1 := fun h => hxr (h ▸ one_mem _)
    have hxo : orderOf x = 2 := orderOf_eq_prime hx2 hx1
    exact hxr ((huniq x hxD hxo).trans haz ▸ hzr)
  have hrx : r * x⁻¹ * r⁻¹ ∈ D := hDn.conj_mem _ (inv_mem hxD) r
  have hcomm : x * (r * x⁻¹ * r⁻¹) = r ^ (2 ^ (n - 2) - 2) := by
    have h1 : x * r * x⁻¹ = r ^ (2 ^ (n - 2) - 1) := by
      rw [hxij]
      calc r ^ i * s * r * (r ^ i * s)⁻¹ = r ^ i * (s * r * s⁻¹) * (r ^ i)⁻¹ := by group
        _ = r ^ i * r ^ (2 ^ (n - 2) - 1) * (r ^ i)⁻¹ := by rw [hsr]
        _ = r ^ (2 ^ (n - 2) - 1) := by group
    have h2 : 2 ^ (n - 2) - 1 = (2 ^ (n - 2) - 2) + 1 := by
      have : 4 ≤ 2 ^ (n - 2) := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc x * (r * x⁻¹ * r⁻¹) = (x * r * x⁻¹) * r⁻¹ := by group
      _ = r ^ (2 ^ (n - 2) - 2) := by rw [h1, h2, pow_succ, mul_inv_cancel_right]
  have hr2c : (r ^ 2) ^ (2 ^ (n - 3) - 1) ∈ D := by
    rw [← pow_mul, show 2 * (2 ^ (n - 3) - 1) = 2 ^ (n - 2) - 2 by
      rw [Nat.mul_sub, mul_one, ← pow_succ']
      congr 2
      omega, ← hcomm]
    exact mul_mem hxD hrx
  have hr2 : r ^ 2 ∈ D := by
    have hcop : Nat.Coprime (2 ^ (n - 3) - 1) (orderOf (r ^ 2)) := by
      have hodd' : Odd (2 ^ (n - 3) - 1) := by
        have : 2 ≤ 2 ^ (n - 3) := by
          calc 2 = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (n - 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
        obtain ⟨k, hk⟩ : Even (2 ^ (n - 3)) :=
          (Nat.even_pow.mpr ⟨even_two, by omega⟩)
        exact ⟨k - 1, by omega⟩
      have h1 : Nat.Coprime (2 ^ (n - 3) - 1) (2 ^ (n - 1)) :=
        (Nat.coprime_pow_right_iff (by omega) _ _).mpr hodd'.coprime_two_right
      exact h1.coprime_dvd_right (hr ▸ orderOf_pow_dvd 2)
    obtain ⟨d, hd⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hd]
    exact pow_mem hr2c d
  have hrs : r * s ∈ D := by
    obtain ⟨k, hk⟩ := hodd
    have h : r * s = ((r ^ 2) ^ k)⁻¹ * x := by
      rw [hxij, hk, ← pow_mul]
      group
    rw [h]
    exact mul_mem (inv_mem (pow_mem hr2 k)) hxD
  have hQD : closure {r ^ 2, r * s} ≤ D := by
    rw [closure_le]
    rintro y (rfl | rfl)
    · exact hr2
    · exact hrs
  have hQidx : (closure {r ^ 2, r * s}).index = 2 :=
    (hidx (closure {r ^ 2, r * s})).mpr (Or.inr (Or.inr rfl))
  have hDtop : D ≠ ⊤ := by
    intro htop
    have hsD : s ∈ D := htop ▸ mem_top s
    exact hsr' ((huniq s hsD hs2).trans haz ▸ hzr)
  have hdvd : D.index ∣ 2 := hQidx ▸ index_dvd_of_le hQD
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd (index_eq_one.mp h) hDtop
  · exact h

end CFSG.ComponentClassification.UnbalancedLayer
