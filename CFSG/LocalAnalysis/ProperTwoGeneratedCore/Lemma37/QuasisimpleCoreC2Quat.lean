module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Basic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePQuatMod

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G} {N : ℕ}

noncomputable abbrev quatGen (φ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup N) :
    G :=
  ((φ.symm (a 1) : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) : G)

variable (φ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup N)

theorem quatGen_mem : quatGen φ ∈ P₁ ⊔ Subgroup.zpowers y := (φ.symm (a 1)).2

theorem map_centralElt_sup [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) : φ ⟨e, Subgroup.mem_sup_left hc.mem_right⟩ = a N := by
  have hw : orderOf (φ.symm (a N) : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) = 2 := by
    rw [MulEquiv.orderOf_eq, quaternionGroup_orderOf_a_self (Nat.one_le_iff_ne_zero.mpr
      (NeZero.ne N))]
  have he : ((φ.symm (a N) : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) : G) = e :=
    hc.eq_of_mem_sup_zpowers hyT hy hyy (φ.symm (a N)).2 (by rw [Subgroup.orderOf_coe]; exact hw)
  rw [show (⟨e, Subgroup.mem_sup_left hc.mem_right⟩ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) =
    φ.symm (a N) from Subtype.ext he.symm, MulEquiv.apply_symm_apply]

theorem quatGen_pow_eq (k : ℕ) :
    quatGen φ ^ k = ((φ.symm (a k) : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) : G) := by
  rw [← a_one_pow, map_pow, Subgroup.coe_pow]

theorem quatGen_pow [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) : quatGen φ ^ N = e := by
  rw [quatGen_pow_eq, ← hc.map_centralElt_sup φ hyT hy hyy, MulEquiv.symm_apply_apply]

include φ in
theorem card_sup_zpowers_eq [NeZero N] :
    Nat.card (P₁ ⊔ Subgroup.zpowers y : Subgroup G) = 4 * N := by
  rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem quatGen_not_mem [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) : quatGen φ ∉ P₁ := by
  intro hcP
  apply hP₁
  have hle : Subgroup.zpowers (quatGen φ) ≤ P₁ := Subgroup.zpowers_le.mpr hcP
  have hcard : Nat.card P₁ ≤ Nat.card (Subgroup.zpowers (quatGen φ)) := by
    rw [Nat.card_zpowers, quatGen, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_a_one]
    have h1 := hc.card_sup_zpowers hyT hy hyy
    rw [card_sup_zpowers_eq φ] at h1
    omega
  rw [← Subgroup.eq_of_le_of_card_ge hle hcard]
  infer_instance

theorem quatGen_pow_mem_iff [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (k : ℕ) :
    quatGen φ ^ k ∈ P₁ ↔ Even k := by
  have hc2 : quatGen φ * quatGen φ ∈ P₁ := hc.mul_self_mem_right hyT hyy (quatGen_mem φ)
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · refine ⟨fun _ => even_two_mul j, fun _ => ?_⟩
    rw [pow_mul, pow_two]
    exact P₁.pow_mem hc2 j
  · refine ⟨fun h => absurd ?_ (hc.quatGen_not_mem φ hyT hy hyy hP₁), fun h => ?_⟩
    · rw [pow_succ, pow_mul, pow_two] at h
      simpa using P₁.mul_mem (P₁.inv_mem (P₁.pow_mem hc2 j)) h
    · exact absurd h (Nat.not_even_iff_odd.mpr ⟨j, rfl⟩)

theorem orderOf_eq_four_of_mul_self (hc : PartC T Q P₁ e u) {w : G} (hw : w * w = e) :
    orderOf w = 4 := by
  have h4 : orderOf w = 2 ^ (1 + 1) := by
    refine orderOf_eq_prime_pow ?_ ?_
    · rw [pow_one, pow_two, hw]
      exact hc.centralElt_ne_one
    · rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, hw, hc.centralElt_mul_self]
  rw [h4]
  norm_num

theorem eq_quatGen_pow_of_map_eq [NeZero N] {w : G} (hw : w ∈ P₁ ⊔ Subgroup.zpowers y)
    {k : ZMod (2 * N)} (hk : φ ⟨w, hw⟩ = a k) : w = quatGen φ ^ k.val := by
  rw [quatGen_pow_eq, ZMod.natCast_zmod_val, ← hk, MulEquiv.symm_apply_apply]

theorem xa_facts [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁)
    (hyy : y * y ∈ P₁) {w : G} (hw : w ∈ P₁ ⊔ Subgroup.zpowers y) {i : ZMod (2 * N)}
    (hi : φ ⟨w, hw⟩ = xa i) : w * w = e ∧ w * quatGen φ * w⁻¹ = (quatGen φ)⁻¹ := by
  constructor
  · have h : (⟨w, hw⟩ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) * ⟨w, hw⟩ =
        ⟨e, Subgroup.mem_sup_left hc.mem_right⟩ := by
      apply φ.injective
      rw [map_mul, hi, xa_mul_xa, hc.map_centralElt_sup φ hyT hy hyy, add_sub_cancel_right]
    exact congrArg Subtype.val h
  · have h : (⟨w, hw⟩ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) * φ.symm (a 1) =
        (φ.symm (a 1))⁻¹ * ⟨w, hw⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, map_inv, hi, MulEquiv.apply_symm_apply, xa_mul_a]
      change xa (i + 1) = a (-1) * xa i
      rw [a_mul_xa, sub_neg_eq_add]
    have h' : w * quatGen φ = (quatGen φ)⁻¹ * w := congrArg Subtype.val h
    rw [h', mul_inv_cancel_right]

theorem mem_sup_zpowers_cases [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) {w : G} (hw : w ∈ P₁ ⊔ Subgroup.zpowers y) :
    (∃ k : ℕ, w = quatGen φ ^ k) ∨ (w * w = e ∧ w * quatGen φ * w⁻¹ = (quatGen φ)⁻¹) := by
  rcases hφw : φ ⟨w, hw⟩ with k | i
  · exact Or.inl ⟨k.val, eq_quatGen_pow_of_map_eq φ hw hφw⟩
  · exact Or.inr (hc.xa_facts φ hyT hy hyy hw hφw)

theorem exists_map_self_eq_a [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 3 ≤ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    ∃ k : ZMod (2 * N), φ ⟨u, Subgroup.mem_sup_left hc.self_mem⟩ = a k := by
  set U : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) :=
    ⟨u, Subgroup.mem_sup_left hc.self_mem⟩ with hU
  set E : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) :=
    ⟨e, Subgroup.mem_sup_left hc.mem_right⟩ with hE
  have hφE : φ E = a N := hc.map_centralElt_sup φ hyT hy hyy
  rcases hφU : φ U with k | i
  · exact ⟨k, rfl⟩
  · exfalso
    set C : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) := φ.symm (a 1) with hCdef
    have hCT : (C : G) ∈ T := hc.sup_zpowers_le hyT C.2
    have hcu : (C : G) * u * (C : G)⁻¹ ∈ Subgroup.zpowers u :=
      (Subgroup.mem_normalizer_iff.mp (hnorm hCT) u).mp (Subgroup.mem_zpowers u)
    have hφc : φ (C * U * C⁻¹) = xa (i - 2) := by
      rw [map_mul, map_mul, map_inv, hCdef, MulEquiv.apply_symm_apply, hφU,
        quaternionGroup_conj_xa]
    have hsub : ∀ w : (P₁ ⊔ Subgroup.zpowers y : Subgroup G),
        ((C * U * C⁻¹ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G)) : G) = (w : G) →
          xa (i - 2) = φ w := by
      intro w hw
      rw [← hφc, Subtype.ext hw]
    have hN2 : ((2 : ℕ) : ZMod (2 * N)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have hNN : ((N + 2 : ℕ) : ZMod (2 * N)) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd (by omega) h
      omega
    rcases hc.mem_zpowers_of_mul_self hc.sq hcu with h | h | h | h
    · have h' := hsub 1 h
      rw [map_one, one_def] at h'
      cases h'
    · have h' := hsub U h
      rw [hφU, xa.injEq] at h'
      exact hN2 (by push_cast; linear_combination -h')
    · have h' := hsub E h
      rw [hφE] at h'
      cases h'
    · have h' := hsub (U * E) h
      rw [map_mul, hφU, hφE, xa_mul_a, xa.injEq] at h'
      exact hNN (by push_cast; linear_combination -h')

theorem self_mem_zpowers_quatGen [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 3 ≤ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    u ∈ Subgroup.zpowers (quatGen φ) := by
  obtain ⟨k, hk⟩ := hc.exists_map_self_eq_a φ hyT hy hyy hN hnorm
  rw [eq_quatGen_pow_of_map_eq φ _ hk]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _

theorem eq_of_mem_zpowers_quatGen [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 3 ≤ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) {x : G}
    (hx : x ∈ Subgroup.zpowers (quatGen φ)) (hxx : x * x = e) : x = u ∨ x = u * e := by
  have hu := hc.self_mem_zpowers_quatGen φ hyT hy hyy hN hnorm
  have heq : Subgroup.zpowers (⟨x, hx⟩ : Subgroup.zpowers (quatGen φ)) =
      Subgroup.zpowers ⟨u, hu⟩ := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers,
      Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc.orderOf_eq_four_of_mul_self hxx,
      hc.orderOf_eq_four_of_mul_self hc.sq]
  have hmem : (⟨x, hx⟩ : Subgroup.zpowers (quatGen φ)) ∈ Subgroup.zpowers ⟨u, hu⟩ :=
    heq ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hxu : x ∈ Subgroup.zpowers u := ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact hc.eq_of_mem_zpowers_of_mul_self hc.sq hxu hxx

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
