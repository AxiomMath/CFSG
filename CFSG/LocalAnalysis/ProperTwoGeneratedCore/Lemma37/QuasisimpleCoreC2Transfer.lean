module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Rigid
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Fusion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G} {N : ℕ}
  (φ : (P₁ ⊔ Subgroup.zpowers y : Subgroup G) ≃* QuaternionGroup N)

theorem conj_mem_sup (hc : PartC T Q P₁ e u) {t k : G} (ht : t ∈ T) (hk : k ∈ Q ⊔ P₁) :
    t * k * t⁻¹ ∈ Q ⊔ P₁ := by
  obtain ⟨q, hq, p, hp, rfl⟩ := hc.mem_sup_iff.mp hk
  rw [show t * (q * p) * t⁻¹ = (t * q * t⁻¹) * (t * p * t⁻¹) by group]
  exact mul_mem_sup (hc.normal_left t ht q hq) (hc.normal_right t ht p hp)

theorem commutator_le_sup (hc : PartC T Q P₁ e u) : ⁅T, T⁆ ≤ Q ⊔ P₁ := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  by_cases haK : a ∈ Q ⊔ P₁
  · rw [show a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) by group]
    exact (Q ⊔ P₁).mul_mem haK (hc.conj_mem_sup hb ((Q ⊔ P₁).inv_mem haK))
  · by_cases hbK : b ∈ Q ⊔ P₁
    · exact (Q ⊔ P₁).mul_mem (hc.conj_mem_sup ha hbK) ((Q ⊔ P₁).inv_mem hbK)
    · have hk := hc.inv_mul_mem a ha b hb haK hbK
      rw [show a * b * a⁻¹ * b⁻¹ = a * ((a * (a⁻¹ * b) * a⁻¹) * (a⁻¹ * b)⁻¹) * a⁻¹ by group]
      exact hc.conj_mem_sup ha ((Q ⊔ P₁).mul_mem (hc.conj_mem_sup ha hk) ((Q ⊔ P₁).inv_mem hk))

theorem index_subgroupOf_eq_two [Finite G] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) : ((Q ⊔ P₁).subgroupOf T).index = 2 := by
  have h1 := hc.index_le_two
  have h2 : ((Q ⊔ P₁).subgroupOf T).index ≠ 1 := by
    rw [Ne, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top]
    exact fun h => hy (h hyT)
  have h3 : ((Q ⊔ P₁).subgroupOf T).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

include φ in
theorem transfer_condition [Finite G] [NeZero N] (hc : PartC T Q P₁ e u) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁) (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) {v : G}
    (hfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) (hvv : v * v = e)
    (hfus : ∀ g : G, g * u * g⁻¹ ∉ Subgroup.zpowers v)
    (hrig : ∀ x ∈ T, x ∉ Q ⊔ P₁ → x * x = e → ∀ g : G, g * x * g⁻¹ ≠ u)
    (m : ℤ) (a : G) (ha : a⁻¹ * quatGen φ ^ m * a ∈ T) :
    (quatGen φ ^ m)⁻¹ * (a⁻¹ * quatGen φ ^ m * a) ∈ Q ⊔ P₁ := by
  have hN3 : 3 ≤ N := by
    obtain ⟨M, hM⟩ := hN
    have := NeZero.ne N
    omega
  have hcN : quatGen φ ^ N = e := hc.quatGen_pow φ hyT hy hyy
  have hcT : quatGen φ ∈ T := hc.sup_zpowers_le hyT (quatGen_mem φ)
  have hc2 : quatGen φ * quatGen φ ∈ P₁ := hc.mul_self_mem_right hyT hyy (quatGen_mem φ)
  set c := quatGen φ with hcdef
  have hc2N : c ^ (2 * N) = 1 := by
    rw [show 2 * N = N * 2 by ring, pow_mul, hcN, pow_two, hc.centralElt_mul_self]
  have hpowN : ∀ b : G, (a⁻¹ * b * a) ^ N = a⁻¹ * b ^ N * a := fun b => by
    simpa using conj_pow (a := a⁻¹) (b := b) (i := N)
  have hzpow : ∀ k : ℤ, (c ^ k) ^ N = c ^ (k * N) := fun k => by
    rw [← zpow_natCast, ← zpow_mul]
  have he := hc.commute_centralElt
  set t := a⁻¹ * c ^ m * a with ht
  obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' m
  · have hcm : c ^ (2 * j) ∈ Q ⊔ P₁ := by
      rw [zpow_mul, zpow_two]
      exact Subgroup.mem_sup_right (P₁.zpow_mem hc2 j)
    refine (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem hcm) ?_
    by_contra htK
    have htN1 : t ^ N = 1 := by
      rw [ht, hpowN, hzpow, show 2 * j * (N : ℤ) = ((2 * N : ℕ) : ℤ) * j by push_cast; ring,
        zpow_mul, zpow_natCast, hc2N, one_zpow, mul_one, inv_mul_cancel]
    have htt : t * t = a⁻¹ * (c ^ (2 * j) * c ^ (2 * j)) * a := by rw [ht]; group
    have hzc : c ^ (2 * j) * c ^ (2 * j) ∈ Subgroup.zpowers c :=
      Subgroup.mul_mem _ (Subgroup.zpow_mem_zpowers c _) (Subgroup.zpow_mem_zpowers c _)
    have hconj : c ^ (2 * j) * c ^ (2 * j) = a * (t * t) * a⁻¹ := by rw [htt]; group
    rcases hc.pow_or_mul_self_of_not_mem φ hyT hy hyy hP₁ hN hfix ha htK with h | h | h | h
    · rw [htN1] at h
      exact hc.centralElt_ne_one h.symm
    · have hsq : c ^ (2 * j) * c ^ (2 * j) = e := by rw [hconj, h, hc.conj_centralElt]
      rcases hc.eq_of_mem_zpowers_quatGen φ hyT hy hyy hN3 hnorm
          (Subgroup.zpow_mem_zpowers c _) hsq with h' | h'
      · exact hrig t ha htK h a (by rw [ht, h']; group)
      · refine hrig (t * e) (T.mul_mem ha (hc.right_le hc.mem_right)) (fun h1 => htK ?_) ?_ a ?_
        · have h2 := (Q ⊔ P₁).mul_mem h1 (Subgroup.mem_sup_right hc.mem_right)
          rwa [hc.mul_centralElt_mul_centralElt] at h2
        · rw [show t * e * (t * e) = t * (e * t) * e by group, ← he t,
            show t * (t * e) * e = t * t * (e * e) by group, h, hc.centralElt_mul_self, mul_one]
        · rw [ht, h']
          calc a * (a⁻¹ * (u * e) * a * e) * a⁻¹ = u * e * (a * e * a⁻¹) := by group
            _ = u := by rw [hc.conj_centralElt, hc.mul_centralElt_mul_centralElt]
    all_goals
      have htv : t * t ∈ Subgroup.zpowers v := by
        rw [h]
        first
          | exact Subgroup.mem_zpowers v
          | exact mul_centralElt_mem_zpowers hvv
      have httt : t * t * (t * t) = e := by
        rw [h]
        first
          | exact hvv
          | rw [show v * e * (v * e) = v * (e * v) * e by group, ← he v,
              show v * (v * e) * e = v * v * (e * e) by group, hvv, hc.centralElt_mul_self,
              mul_one]
      have hzz : (c ^ (2 * j) * c ^ (2 * j)) * (c ^ (2 * j) * c ^ (2 * j)) = e := by
        rw [hconj, show a * (t * t) * a⁻¹ * (a * (t * t) * a⁻¹) = a * (t * t * (t * t)) * a⁻¹ by
          group, httt, hc.conj_centralElt]
      have hvz : a⁻¹ * (c ^ (2 * j) * c ^ (2 * j)) * a ∈ Subgroup.zpowers v := by
        rw [← htt]
        exact htv
      apply hfus a⁻¹
      rw [inv_inv]
      rcases hc.eq_of_mem_zpowers_quatGen φ hyT hy hyy hN3 hnorm hzc hzz with h' | h' <;>
        rw [h'] at hvz
      · exact hvz
      · have he' : e ∈ Subgroup.zpowers v := by
          rw [← hvv]
          exact Subgroup.mul_mem _ (Subgroup.mem_zpowers v) (Subgroup.mem_zpowers v)
        have h3 : a⁻¹ * (u * e) * a = a⁻¹ * u * a * e := by
          calc a⁻¹ * (u * e) * a = a⁻¹ * u * (e * a) := by group
            _ = a⁻¹ * u * (a * e) := by rw [← he a]
            _ = a⁻¹ * u * a * e := by group
        have h2 := Subgroup.mul_mem _ hvz he'
        rwa [h3, hc.mul_centralElt_mul_centralElt] at h2
  · have hcm : c ^ (2 * j + 1) ∉ Q ⊔ P₁ := by
      intro h
      have h1 := (Q ⊔ P₁).mul_mem
        ((Q ⊔ P₁).inv_mem (Subgroup.mem_sup_right (P₁.zpow_mem hc2 j))) h
      rw [zpow_add_one, zpow_mul, zpow_two, inv_mul_cancel_left] at h1
      exact hc.quatGen_not_mem φ hyT hy hyy hP₁
        (hc.mem_right_of_mem_sup hyT hy hyy (quatGen_mem φ) h1)
    have htK : t ∉ Q ⊔ P₁ := by
      intro h
      have h1 := hc.pow_eq_one_of_mem_sup φ hyT hy hyy hP₁ hN h
      rw [ht, hpowN, hzpow, show (2 * j + 1) * (N : ℤ) = ((2 * N : ℕ) : ℤ) * j + (N : ℕ) by
        push_cast; ring, zpow_add, zpow_mul, zpow_natCast, zpow_natCast, hc2N, one_zpow,
        one_mul, hcN, he a⁻¹, inv_mul_cancel_right] at h1
      exact hc.centralElt_ne_one h1
    exact hc.inv_mul_mem _ (T.zpow_mem hcT _) t ha hcm htK

include φ in
theorem false_of_labelled [Finite G] [NeZero N] (hperf : Group.IsPerfect G)
    (hc : PartC T Q P₁ e u) (hyT : y ∈ T) (hy : y ∉ Q ⊔ P₁) (hyy : y * y ∈ P₁)
    (hP₁ : ¬ IsCyclic P₁) (hN : 8 ∣ N) (S : Sylow 2 G) (hST : (S : Subgroup G) = T)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G))
    (hNT : Subgroup.normalizer (T : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hvQ, hvv, hyv, hfix⟩ := hc.exists_inv_conj hyT hy hyy
  have hTv := hc.le_normalizer_zpowers_of_inv hyT hy hvQ hvv hyv
  have hfus := hc.conj_not_mem_zpowers S hST hnorm hNT hvQ hvv hTv
  have hrig : ∀ x ∈ T, x ∉ Q ⊔ P₁ → x * x = e → ∀ g : G, g * x * g⁻¹ ≠ u :=
    fun x hxT hx hxx g => hc.conj_ne_self φ hyT hy hyy hP₁ hN S hST hnorm hvQ hvv hTv hfus hxT
      hx hxx g
  have hcT : quatGen φ ∈ T := hc.sup_zpowers_le hyT (quatGen_mem φ)
  have hcK : quatGen φ ∉ Q ⊔ P₁ := fun h => hc.quatGen_not_mem φ hyT hy hyy hP₁
    (hc.mem_right_of_mem_sup hyT hy hyy (quatGen_mem φ) h)
  have hindex : Nat.Coprime 2 T.index := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two, ← hST]
    exact S.not_dvd_index
  have hnormal : ((Q ⊔ P₁).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two (hc.index_subgroupOf_eq_two hyT hy)
  obtain ⟨k, hk⟩ := hc.isPGroup ⟨quatGen φ, hcT⟩
  have hgp : ∃ n : ℕ, quatGen φ ^ 2 ^ n = 1 := ⟨k, by simpa using congrArg Subtype.val hk⟩
  exact CFSG.Quasithin.generalized_thompson_transfer_one hindex ⟨hc.sup_le, hnormal⟩
    hc.commutator_le_sup hcT hcK hgp
    (hc.transfer_condition φ hyT hy hyy hP₁ hN hnorm hfix hvv hfus hrig)
    (by rw [hperf.commutator_eq_top]; exact Subgroup.mem_top _)

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
