module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup

section Klein

variable {G : Type*} [Group G]

private theorem mem_closure_pair_iff {z u : G} (hz : z * z = 1) (hu : u * u = 1) (hzu : z * u = u * z)
    (x : G) : x ∈ closure ({z, u} : Set G) ↔ x = 1 ∨ x = z ∨ x = u ∨ x = z * u := by
  have e1 : z * (z * u) = u := by rw [← mul_assoc, hz, one_mul]
  have e2 : z * u * z = u := by rw [hzu, mul_assoc, hz, mul_one]
  have e3 : u * (z * u) = z := by rw [hzu, ← mul_assoc, hu, one_mul]
  have e4 : z * u * u = z := by rw [mul_assoc, hu, mul_one]
  have e5 : z * u * (z * u) = 1 := by rw [mul_assoc, e3, hz]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have hzui : (z * u)⁻¹ = z * u := by rw [mul_inv_rev, hzi, hui, hzu]
  constructor
  · intro hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    | one => exact Or.inl rfl
    | mul x y _ _ hx hy =>
      rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h'] <;>
        simp [hz, hu, e1, e2, e3, e4, e5, hzu.symm]
    | inv x _ hx =>
      rcases hx with h | h | h | h <;> rw [h] <;> simp [hzi, hui, hzui]
  · rintro (h | h | h | h) <;> rw [h]
    · exact one_mem _
    · exact subset_closure (Set.mem_insert _ _)
    · exact subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    · exact mul_mem (subset_closure (Set.mem_insert _ _))
        (subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))

private theorem mul_self_eq_one_of_orderOf_eq_two' {z : G} (hz : orderOf z = 2) : z * z = 1 := by
  rw [← pow_two, ← hz]
  exact pow_orderOf_eq_one z

private theorem ne_one_of_orderOf_eq_two' {z : G} (hz : orderOf z = 2) : z ≠ 1 := by
  rintro rfl
  simp at hz

end Klein

theorem normalizer_fixes_z {G : Type*} [Group G] [Finite G] {z t : G} (hz : orderOf z = 2)
    (ht : orderOf t = 2) (hzt : z * t = t * z) (hne : z ≠ t) (A : Subgroup G) (hzA : z ∈ A)
    (htA : t ∈ A)
    (h3 : ∀ n ∈ A, (∀ x ∈ Subgroup.closure ({z, t} : Set G),
      n * x * n⁻¹ ∈ Subgroup.closure ({z, t} : Set G)) → orderOf n ≠ 3)
    (n₀ : G) (hn₀A : n₀ ∈ A) (hn₀z : n₀ * z * n₀⁻¹ = z) (hn₀t : n₀ * t * n₀⁻¹ = z * t) :
    ∀ n ∈ A, (∀ x ∈ Subgroup.closure ({z, t} : Set G),
      n * x * n⁻¹ ∈ Subgroup.closure ({z, t} : Set G)) → n * z * n⁻¹ = z := by
  have hz2 : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two' hz
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two' ht
  have hz1 : z ≠ 1 := ne_one_of_orderOf_eq_two' hz
  have ht1 : t ≠ 1 := ne_one_of_orderOf_eq_two' ht
  have hmem := mem_closure_pair_iff hz2 ht2 hzt
  set T : Subgroup G := Subgroup.closure ({z, t} : Set G) with hT
  have hzT : z ∈ T := (hmem z).2 (Or.inr (Or.inl rfl))
  have htT : t ∈ T := (hmem t).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hztT : z * t ∈ T := T.mul_mem hzT htT
  obtain ⟨N, hN⟩ : ∃ N : Subgroup G, ∀ g, g ∈ N ↔ g ∈ A ∧ g ∈ Subgroup.normalizer (T : Set G) :=
    ⟨A ⊓ Subgroup.normalizer (T : Set G), fun g => Subgroup.mem_inf⟩
  have hNconj : ∀ c : N, ∀ x ∈ T, (c : G) * x * (c : G)⁻¹ ∈ T := fun c x hx =>
    (Subgroup.mem_normalizer_iff.mp ((hN c).1 c.2).2 x).mp hx
  have hzN : z ∈ N := (hN z).2 ⟨hzA, Subgroup.le_normalizer hzT⟩
  have htN : t ∈ N := (hN t).2 ⟨htA, Subgroup.le_normalizer htT⟩
  have hztN : z * t ∈ N := N.mul_mem hzN htN
  have hn₀T : ∀ x ∈ T, n₀ * x * n₀⁻¹ ∈ T := by
    intro x hx
    rcases (hmem x).1 hx with h | h | h | h <;> rw [h]
    · simp
    · rw [hn₀z]; exact hzT
    · rw [hn₀t]; exact hztT
    · have : n₀ * (z * t) * n₀⁻¹ = t := by
        calc n₀ * (z * t) * n₀⁻¹ = (n₀ * z * n₀⁻¹) * (n₀ * t * n₀⁻¹) := by group
          _ = t := by rw [hn₀z, hn₀t, ← mul_assoc, hz2, one_mul]
      rw [this]; exact htT
  have hn₀N : n₀ ∈ N := (hN n₀).2 ⟨hn₀A, Subgroup.mem_normalizer_fintype hn₀T⟩
  intro n hnA hn
  by_contra hmove
  have hnN : n ∈ N := (hN n).2 ⟨hnA, Subgroup.mem_normalizer_fintype hn⟩
  let z' : N := ⟨z, hzN⟩
  let t' : N := ⟨t, htN⟩
  let w' : N := ⟨z * t, hztN⟩
  let n' : N := ⟨n, hnN⟩
  let n₀' : N := ⟨n₀, hn₀N⟩
  have hzt' : z' ≠ t' := fun h => hne (congrArg Subtype.val h)
  have hzw' : z' ≠ w' := fun h => ht1 (mul_eq_left.mp (congrArg Subtype.val h).symm)
  have htw' : t' ≠ w' := fun h => hz1 (mul_eq_right.mp (congrArg Subtype.val h).symm)
  have hn₀tw : IsConj t' w' := isConj_iff.mpr ⟨n₀', Subtype.ext (by simpa [n₀', t', w'] using hn₀t)⟩
  have hn₀wt : IsConj w' t' := by
    refine isConj_iff.mpr ⟨n₀', Subtype.ext ?_⟩
    show n₀ * (z * t) * n₀⁻¹ = t
    calc n₀ * (z * t) * n₀⁻¹ = (n₀ * z * n₀⁻¹) * (n₀ * t * n₀⁻¹) := by group
      _ = t := by rw [hn₀z, hn₀t, ← mul_assoc, hz2, one_mul]
  have hmT : n * z * n⁻¹ ∈ T := hn z hzT
  have hm1 : n * z * n⁻¹ ≠ 1 := by
    intro h
    apply hz1
    simpa using h
  have hcl : (conjugatesOf z').ncard = 3 := by
    have hset : conjugatesOf z' = {z', t', w'} := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hx
        obtain ⟨c, hc⟩ := isConj_iff.mp hx
        have hxG : (x : G) = c * z * (c : G)⁻¹ := by rw [← hc]; rfl
        have hxT : (x : G) ∈ T := by rw [hxG]; exact hNconj c z hzT
        have hx1 : (x : G) ≠ 1 := by
          rw [hxG]
          intro h
          apply hz1
          simpa using h
        rcases (hmem x).1 hxT with h | h | h | h
        · exact absurd h hx1
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Or.inl (Subtype.ext h))
        · exact Or.inr (Or.inr (Subtype.ext h))
      · have hzz : IsConj z' z' := IsConj.refl _
        rintro (h | h | h)
        · rw [h]; exact hzz
        · rw [h]
          rcases (hmem _).1 hmT with h1 | h1 | h1 | h1
          · exact absurd h1 hm1
          · exact absurd h1 hmove
          · exact isConj_iff.mpr ⟨n', Subtype.ext (by simpa [n', z', t'] using h1)⟩
          · exact (isConj_iff.mpr ⟨n', Subtype.ext (by simpa [n', z', w'] using h1)⟩ : IsConj z' w').trans hn₀wt
        · rw [h]
          rcases (hmem _).1 hmT with h1 | h1 | h1 | h1
          · exact absurd h1 hm1
          · exact absurd h1 hmove
          · exact (isConj_iff.mpr ⟨n', Subtype.ext (by simpa [n', z', t'] using h1)⟩ : IsConj z' t').trans hn₀tw
          · exact isConj_iff.mpr ⟨n', Subtype.ext (by simpa [n', z', w'] using h1)⟩
    exact Set.ncard_eq_three.mpr ⟨z', t', w', hzt', hzw', htw', hset⟩
  have hindex : (Subgroup.centralizer ({z'} : Set N)).index = 3 := by
    rw [Subgroup.index_centralizer_eq_ncard, hcl]
  have h3dvd : 3 ∣ Nat.card N := by
    rw [← Subgroup.card_mul_index (Subgroup.centralizer ({z'} : Set N)), hindex]
    exact dvd_mul_left 3 _
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
  exact h3 (x : G) ((hN x).1 x.2).1 (fun y hy => hNconj x y hy) (by rw [Subgroup.orderOf_coe]; exact hx)

theorem sylow_of_centralizer_two {G : Type*} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    (A S : Subgroup G) (_hzA : z ∈ A) (hSA : S ≤ A) (hS2 : IsPGroup 2 S) (hzS : z ∈ S)
    (hzZ : ∀ s ∈ S, s * z = z * s)
    (hZ : ∀ s ∈ S, (∀ w ∈ S, s * w = w * s) → s = 1 ∨ s = z)
    (hSyl : ¬ 2 ∣ S.relIndex (A ⊓ Subgroup.centralizer ({z} : Set G))) :
    ¬ 2 ∣ S.relIndex A := by
  intro h2
  obtain ⟨n, hn⟩ := hS2.exists_card_eq
  have hA : S.relIndex A * Nat.card S = Nat.card A := by
    simpa [inf_of_le_left hSA] using S.relIndex_mul_card A
  have hdvd : 2 ^ (n + 1) ∣ Nat.card A := by
    rw [← hA, hn, pow_succ, mul_comm (2 ^ n) 2]
    exact mul_dvd_mul_right h2 _
  obtain ⟨K, hK, hSK, hKA⟩ := Sylow.exists_subgroup_card_pow_prime_le_le Nat.prime_two
    (n := n + 1) (H := S) (L := A) (by rw [hn]; exact pow_dvd_pow 2 (Nat.le_succ n)) hdvd hSA
  have hSK2 : S.relIndex K = 2 := by
    have h := S.relIndex_mul_card K
    rw [inf_of_le_left hSK, hn, hK, pow_succ] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos n) (h.trans (mul_comm _ _))
  have hnorm : (S.subgroupOf K).Normal := Subgroup.normal_of_index_eq_two hSK2
  have hconj : ∀ k ∈ K, ∀ s ∈ S, k * s * k⁻¹ ∈ S := fun k hk s hs =>
    mem_subgroupOf.mp (hnorm.conj_mem ⟨s, hSK hs⟩ (mem_subgroupOf.mpr hs) ⟨k, hk⟩)
  have hKC : K ≤ A ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro k hk
    refine Subgroup.mem_inf.mpr ⟨hKA hk, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hu : k * z * k⁻¹ ∈ S := hconj k hk z hzS
    have hu' : ∀ w ∈ S, (k * z * k⁻¹) * w = w * (k * z * k⁻¹) := by
      intro w hw
      have hw' : k⁻¹ * w * k⁻¹⁻¹ ∈ S := hconj k⁻¹ (inv_mem hk) w hw
      have hc := hzZ _ hw'
      rw [inv_inv] at hc
      calc k * z * k⁻¹ * w = k * (z * (k⁻¹ * w * k)) * k⁻¹ := by group
        _ = k * ((k⁻¹ * w * k) * z) * k⁻¹ := by rw [hc]
        _ = w * (k * z * k⁻¹) := by group
    rcases hZ _ hu hu' with h1 | h1
    · exfalso
      have : z = 1 := by simpa using h1
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
    · calc k * z = (k * z * k⁻¹) * k := by group
        _ = z * k := by rw [h1]
  apply hSyl
  rw [← Subgroup.relIndex_mul_relIndex S K _ hSK hKC, hSK2]
  exact dvd_mul_right 2 _

end CFSG.GH74.GLS.Stage4.Q9
