module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePQuatMod
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreYAltFour

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u : G} {M : ℕ}

theorem map_centralElt_right [NeZero M] (hc : PartC T Q P₁ e u) (φ : P₁ ≃* QuaternionGroup M) :
    φ ⟨e, hc.mem_right⟩ = a M := by
  have hw : orderOf (φ.symm (a M) : P₁) = 2 := by
    rw [MulEquiv.orderOf_eq, quaternionGroup_orderOf_a_self (Nat.one_le_iff_ne_zero.mpr
      (NeZero.ne M))]
  have he : ((φ.symm (a M) : P₁) : G) = e :=
    hc.unique _ (φ.symm (a M)).2 (by rw [Subgroup.orderOf_coe]; exact hw)
  rw [show (⟨e, hc.mem_right⟩ : P₁) = φ.symm (a M) from Subtype.ext he.symm,
    MulEquiv.apply_symm_apply]

theorem mem_zpowers_self (hc : PartC T Q P₁ e u) {x : G} (hx : x ∈ Subgroup.zpowers u) :
    x = 1 ∨ x = u ∨ x = e ∨ x = u * e := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h4 : orderOf u = 4 := by
    have h4 : orderOf u = 2 ^ (1 + 1) := by
      refine orderOf_eq_prime_pow ?_ ?_
      · rw [pow_one, pow_two, hc.sq]
        exact hc.centralElt_ne_one
      · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, hc.sq,
          hc.centralElt_mul_self]
    rw [h4]
    norm_num
  rw [← zpow_mod_orderOf, h4]
  have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h1 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos _ (by norm_num)
  obtain h | h | h | h : k % ((4 : ℕ) : ℤ) = 0 ∨ k % ((4 : ℕ) : ℤ) = 1 ∨
      k % ((4 : ℕ) : ℤ) = 2 ∨ k % ((4 : ℕ) : ℤ) = 3 := by omega
  · left
    rw [h, zpow_zero]
  · right; left
    rw [h, zpow_one]
  · right; right; left
    rw [h, show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hc.sq]
  · right; right; right
    rw [h, show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ, pow_two, hc.sq]
    exact (hc.commute_centralElt u).symm

theorem mul_self_mem_zpowers [NeZero M] (hc : PartC T Q P₁ e u) (hT : T ≤ Q ⊔ P₁) (hM : 4 ∣ M)
    (φ : P₁ ≃* QuaternionGroup M) {t : G} (ht : t ∈ T) :
    t * t ∈ Subgroup.zpowers ((φ.symm (a 2) : P₁) : G) := by
  have hEven : Even M := even_iff_two_dvd.mpr ((dvd_mul_left 2 2).trans hM)
  have himg : ∀ y ∈ Subgroup.zpowers (a 2 : QuaternionGroup M),
      ((φ.symm y : P₁) : G) ∈ Subgroup.zpowers ((φ.symm (a 2) : P₁) : G) := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [map_zpow, Subgroup.coe_zpow]
    exact Subgroup.zpow_mem_zpowers _ _
  have hp : ∀ p ∈ P₁, p * p ∈ Subgroup.zpowers ((φ.symm (a 2) : P₁) : G) := by
    intro p hp
    have h := himg _ (quaternionGroup_mul_self_mem_zpowers hEven (φ ⟨p, hp⟩))
    rwa [← map_mul, MulEquiv.symm_apply_apply] at h
  have he : e ∈ Subgroup.zpowers ((φ.symm (a 2) : P₁) : G) := by
    have h := himg _ (quaternionGroup_a_self_mem_zpowers hEven)
    rwa [← hc.map_centralElt_right φ, MulEquiv.symm_apply_apply] at h
  obtain ⟨q, hq, p, hp', rfl⟩ := hc.mem_sup_iff.mp (hT ht)
  have hqp : q * p * (q * p) = q * q * (p * p) := by
    rw [show q * p * (q * p) = q * (p * q) * p by group, ← hc.commute q hq p hp']
    group
  rw [hqp]
  refine Subgroup.mul_mem _ ?_ (hp p hp')
  rcases quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hq with h | h
  · rw [h]
    exact Subgroup.one_mem _
  · rw [h]
    exact he

theorem exists_mul_self_eq_self [NeZero M] (hc : PartC T Q P₁ e u) (hM : 4 ∣ M)
    (φ : P₁ ≃* QuaternionGroup M)
    (hnorm : P₁ ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    ∃ w ∈ P₁, w * w = u := by
  have hM4 : 4 ≤ M := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) hM
  set U : P₁ := ⟨u, hc.self_mem⟩ with hU
  set E : P₁ := ⟨e, hc.mem_right⟩ with hE
  have hφE : φ E = a M := hc.map_centralElt_right φ
  have hUU : φ U * φ U = a M := by
    rw [← map_mul, ← hφE]
    exact congrArg φ (Subtype.ext hc.sq)
  rcases hφU : φ U with i | i
  · rw [hφU] at hUU
    obtain ⟨j, hj⟩ := quaternionGroup_isSquare hM hUU
    refine ⟨(φ.symm (a j) : P₁), (φ.symm (a j)).2, ?_⟩
    rw [← Subgroup.coe_mul, ← map_mul, hj, ← hφU, MulEquiv.symm_apply_apply]
  · exfalso
    set c : P₁ := φ.symm (a 1) with hcdef
    have hcu : (c : G) * u * (c : G)⁻¹ ∈ Subgroup.zpowers u :=
      (Subgroup.mem_normalizer_iff.mp (hnorm c.2) u).mp (Subgroup.mem_zpowers u)
    have hφc : φ (c * U * c⁻¹) = xa (i - 2) := by
      rw [map_mul, map_mul, map_inv, hcdef, MulEquiv.apply_symm_apply, hφU,
        quaternionGroup_conj_xa]
    have hcases := hc.mem_zpowers_self hcu
    have hsub : ∀ w : P₁, ((c * U * c⁻¹ : P₁) : G) = (w : G) → xa (i - 2) = φ w := by
      intro w hw
      rw [← hφc, Subtype.ext hw]
    have hM2 : ((2 : ℕ) : ZMod (2 * M)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have hMM : ((M + 2 : ℕ) : ZMod (2 * M)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    rcases hcases with h | h | h | h
    · have h' := hsub 1 h
      rw [map_one, one_def] at h'
      cases h'
    · have h' := hsub U h
      rw [hφU, xa.injEq] at h'
      exact hM2 (by push_cast; linear_combination -h')
    · have h' := hsub E h
      rw [hφE] at h'
      cases h'
    · have h' := hsub (U * E) h
      rw [map_mul, hφU, hφE, xa_mul_a, xa.injEq] at h'
      exact hMM (by push_cast; linear_combination -h')

theorem normalizer_le_normalizer_zpowers [Finite G] [NeZero M] (hc : PartC T Q P₁ e u)
    (hT : T ≤ Q ⊔ P₁) (hM : 4 ∣ M) (φ : P₁ ≃* QuaternionGroup M)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G) := by
  intro g hg
  set S := Subgroup.closure {x : G | ∃ t ∈ T, t * t = x} with hS
  have hSC : S ≤ Subgroup.zpowers ((φ.symm (a 2) : P₁) : G) := by
    rw [Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact hc.mul_self_mem_zpowers hT hM φ ht
  have : IsCyclic S := Subgroup.isCyclic_of_le hSC
  obtain ⟨w, hwP, hww⟩ := hc.exists_mul_self_eq_self hM φ (hc.right_le.trans hnorm)
  have hwT := hc.right_le hwP
  have huS : u ∈ S := Subgroup.subset_closure ⟨w, hwT, hww⟩
  have hgw : g * w * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hg w).mp hwT
  have hgu : g * u * g⁻¹ = (g * w * g⁻¹) * (g * w * g⁻¹) := by rw [← hww]; group
  have hguS : g * u * g⁻¹ ∈ S := Subgroup.subset_closure ⟨_, hgw, hgu.symm⟩
  have hord : orderOf (g * u * g⁻¹) = orderOf u := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have heq : Subgroup.zpowers (⟨u, huS⟩ : S) = Subgroup.zpowers ⟨g * u * g⁻¹, hguS⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hord]
  have hmem : (⟨g * u * g⁻¹, hguS⟩ : S) ∈ Subgroup.zpowers (⟨u, huS⟩ : S) :=
    heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hgu' : g * u * g⁻¹ ∈ Subgroup.zpowers u :=
    ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine mem_normalizer_of_conj_mem fun x hx => ?_
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← conj_zpow]
  exact Subgroup.zpow_mem _ hgu' j

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
