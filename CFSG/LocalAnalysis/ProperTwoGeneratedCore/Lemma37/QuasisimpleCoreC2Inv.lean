module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Orders
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCorePCases

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

theorem exists_conj_mem_sylow_of_le {G : Type} [Group G] [Finite G] (S : Sylow 2 G)
    {X D : Subgroup G} (hSX : (S : Subgroup G) ≤ X) (hDX : D ≤ X) (hD : IsPGroup 2 D) :
    ∃ k ∈ X, ∀ d ∈ D, k * d * k⁻¹ ∈ (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (D.subgroupOf X) := hD.of_equiv (Subgroup.subgroupOfEquivOfLe hDX).symm
  obtain ⟨R, hR⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq X R (S.subtype hSX)
  refine ⟨k, k.2, fun d hd => ?_⟩
  have h1 : (⟨d, hDX hd⟩ : X) ∈ (R : Subgroup X) := hR (Subgroup.mem_subgroupOf.mpr hd)
  have h2 : (k : X) * ⟨d, hDX hd⟩ * k⁻¹ ∈ ((S.subtype hSX : Sylow 2 X) : Subgroup X) := by
    rw [← hk, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ h1
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h2
  simpa using h2

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G} {N : ℕ}
  (φ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup N)

theorem conj_mul_self_eq (hc : PartC T Q P₁ e u) {q p : G} (hq : q ∈ Q) (hp : p ∈ P₁) :
    q * p * u * (q * p)⁻¹ = p * u * p⁻¹ := by
  have h := hc.commute q hq _ (hc.normal_right p (hc.right_le hp) u hc.self_mem)
  calc q * p * u * (q * p)⁻¹ = q * (p * u * p⁻¹) * q⁻¹ := by group
    _ = p * u * p⁻¹ := by rw [h, mul_inv_cancel_right]

theorem mul_mul_self_of_mem (hc : PartC T Q P₁ e u) {q p : G} (hq : q ∈ Q) (hp : p ∈ P₁) :
    q * p * (q * p) = q * q * (p * p) := by
  have h := hc.commute q hq p hp
  calc q * p * (q * p) = q * (p * q) * p := by group
    _ = q * q * (p * p) := by rw [← h]; group

theorem mem_right_of_conj_eq (hc : PartC T Q P₁ e u) {t : G} (ht : t ∈ Q ⊔ P₁)
    (htt : t * t = e) (htu : t * u * t⁻¹ = u * e) : t ∈ P₁ := by
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp ht
  rw [hc.conj_mul_self_eq hq hp] at htu
  rw [hc.mul_mul_self_of_mem hq hp] at htt
  rcases quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hq with h | h
  · rcases quaternion_eq_of_mul_self hc.quaternion.some hc.mem_left hc.order hq h with rfl | rfl
    · rw [one_mul]
      exact hp
    · exact P₁.mul_mem hc.mem_right hp
  · exfalso
    rw [h] at htt
    have hpp : p * p = 1 := by
      calc p * p = e⁻¹ * (e * (p * p)) := by group
        _ = 1 := by rw [htt, inv_mul_cancel]
    rcases hc.eq_of_mem_right_of_mul_self hp hpp with rfl | rfl
    · rw [one_mul, inv_one, mul_one] at htu
      exact hc.centralElt_ne_one (mul_eq_left.mp htu.symm)
    · rw [← hc.commute_centralElt u, mul_inv_cancel_right] at htu
      exact hc.centralElt_ne_one (mul_eq_left.mp htu.symm)

include φ in
theorem eq_of_mem_right_of_commute [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 3 ≤ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) {p : G} (hp : p ∈ P₁)
    (hpu : p * u = u * p) (hpp : p * p = e) : p = u ∨ p = u * e := by
  rcases hc.mem_sup_zpowers_cases φ hyT hy hyy (Subgroup.mem_sup_left hp) with
    ⟨k, rfl⟩ | ⟨-, hpc⟩
  · exact hc.eq_of_mem_zpowers_quatGen φ hyT hy hyy hN hnorm
      (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _) hpp
  · exfalso
    obtain ⟨j, hj⟩ :=
      Subgroup.mem_zpowers_iff.mp (hc.self_mem_zpowers_quatGen φ hyT hy hyy hN hnorm)
    have hinv : p * u * p⁻¹ = u⁻¹ := by
      rw [← hj, ← conj_zpow, hpc, inv_zpow]
    have hu : u⁻¹ = u := by rw [← hinv, hpu, mul_inv_cancel_right]
    have huu : u * u = 1 := by
      rw [show u * u = u * u⁻¹ by rw [hu]]
      exact mul_inv_cancel u
    rw [hc.sq] at huu
    exact hc.centralElt_ne_one huu

include φ in
theorem eq_mul_of_commute [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hN : 3 ≤ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) {v : G} (hvQ : v ∈ Q)
    (hvv : v * v = e) {r : G} (hr : r ∈ Q ⊔ P₁) (hrr : r * r = 1) (hr1 : r ≠ 1) (hre : r ≠ e)
    (hru : r * u = u * r) (hrv : r * v = v * r) : r = u * v ∨ r = u * v * e := by
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp hr
  have hpu : p * u = u * p := by
    have h1 : q * p * u * (q * p)⁻¹ = u := by rw [hru, mul_inv_cancel_right]
    rw [hc.conj_mul_self_eq hq hp] at h1
    calc p * u = p * u * p⁻¹ * p := by group
      _ = u * p := by rw [h1]
  have hqv : q * v = v * q := by
    have hpv := hc.commute v hvQ p hp
    have h2 : q * v * p = v * q * p := by
      calc q * v * p = q * (v * p) := by group
        _ = q * (p * v) := by rw [hpv]
        _ = q * p * v := by group
        _ = v * (q * p) := hrv
        _ = v * q * p := by group
    exact mul_right_cancel h2
  rw [hc.mul_mul_self_of_mem hq hp] at hrr
  rcases quaternion_mul_self hc.quaternion.some hc.mem_left hc.order hq with hqq | hqq
  · exfalso
    rw [hqq, one_mul] at hrr
    have hq1 := quaternion_eq_of_mul_self hc.quaternion.some hc.mem_left hc.order hq hqq
    have hp1 := hc.eq_of_mem_right_of_mul_self hp hrr
    rcases hq1 with h1 | h1 <;> rcases hp1 with h2 | h2 <;> rw [h1, h2] at hr1 hre
    · exact hr1 (mul_one 1)
    · exact hre (one_mul e)
    · exact hre (mul_one e)
    · exact hr1 hc.centralElt_mul_self
  · rw [hqq] at hrr
    have hpp : p * p = e := by
      calc p * p = e⁻¹ * (e * (p * p)) := by group
        _ = e := by rw [hrr, mul_one, hc.centralElt_inv]
    have hq' : q = v ∨ q = v * e := by
      by_contra hne
      push Not at hne
      have h := hc.anticomm hq hvQ hqq hvv (Ne.symm hne.1)
        (fun h => hne.2 (by rw [h, hc.mul_centralElt_mul_centralElt]))
      rw [hqv] at h
      exact hc.centralElt_ne_one (mul_eq_left.mp h.symm)
    have hvu : v * u = u * v := hc.commute v hvQ u hc.self_mem
    have he := hc.commute_centralElt
    rcases hq' with h1 | h1 <;>
      rcases hc.eq_of_mem_right_of_commute φ hyT hy hyy hN hnorm hp hpu hpp with h2 | h2 <;>
      rw [h1, h2]
    · exact Or.inl hvu
    · exact Or.inr (by rw [← mul_assoc, hvu])
    · right
      rw [mul_assoc, ← he u, ← mul_assoc, hvu]
    · left
      calc v * e * (u * e) = v * (e * u) * e := by group
        _ = v * (u * e) * e := by rw [← he u]
        _ = v * u * (e * e) := by group
        _ = u * v := by rw [hc.centralElt_mul_self, mul_one, hvu]

theorem mul_pow_eq_of_pow_eq (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hyy : y * y ∈ P₁)
    (hN : 8 ∣ N) {q w : G} (hq : q ∈ Q) (hw : w ∈ P₁ ⊔ Subgroup.zpowers y) (hwN : w ^ N = e) :
    (q * w) ^ N = e := by
  have hwT := hc.sup_zpowers_le hyT hw
  have hsQ : q * (w * q * w⁻¹) ∈ Q := Q.mul_mem hq (hc.normal_left w hwT q hq)
  have hcomm : Commute (q * (w * q * w⁻¹)) (w * w) :=
    hc.commute _ hsQ _ (hc.mul_self_mem_right hyT hyy hw)
  obtain ⟨M, rfl⟩ := hN
  rw [show 8 * M = 2 * (4 * M) by ring, pow_mul, pow_two, mul_mul_self_eq, hcomm.mul_pow,
    pow_mul, hc.pow_four_eq_one_left hsQ, one_pow, one_mul, ← pow_two, ← pow_mul,
    show 2 * (4 * M) = 8 * M by ring, hwN]

include φ in
theorem exists_mul_eq_of_mul_self [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N) {x : G}
    (hxT : x ∈ T) (hx : x ∉ Q ⊔ P₁) (hxx : x * x = e) :
    ∃ q ∈ Q, ∃ w ∈ P₁ ⊔ Subgroup.zpowers y, q * w = x ∧
      w * quatGen φ * w⁻¹ = (quatGen φ)⁻¹ := by
  have hxN : x ^ N = 1 := by
    obtain ⟨M, hM⟩ := hN
    rw [hM, show 8 * M = 2 * (2 * (2 * M)) by ring, pow_mul, pow_two, hxx, pow_mul, pow_two,
      hc.centralElt_mul_self, one_pow]
  obtain ⟨q, hq, w, hw, rfl⟩ := hc.exists_mul_eq_of_mem hyT hy hxT
  have hw₁ : w ∉ P₁ := fun h => hx (mul_mem_sup hq h)
  refine ⟨q, hq, w, hw, rfl, ?_⟩
  rcases hc.mem_sup_zpowers_cases φ hyT hy hyy hw with ⟨k, rfl⟩ | ⟨-, hwc⟩
  · exfalso
    have hk : ¬ Even k := fun h => hw₁ ((hc.quatGen_pow_mem_iff φ hyT hy hyy hP₁ k).mpr h)
    obtain ⟨j, rfl⟩ := Nat.not_even_iff_odd.mp hk
    have hwN : (quatGen φ ^ (2 * j + 1)) ^ N = e := by
      rw [← pow_mul, show (2 * j + 1) * N = N * (2 * j + 1) by ring, pow_mul,
        hc.quatGen_pow φ hyT hy hyy, pow_succ, pow_mul, pow_two, hc.centralElt_mul_self, one_pow,
        one_mul]
    have h1 := hc.mul_pow_eq_of_pow_eq hyT hyy hN hq hw hwN
    rw [hxN] at h1
    exact hc.centralElt_ne_one h1.symm
  · exact hwc

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
