module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.GH74.GLS.SP.Local

theorem mem_of_pow_mem_of_coprime {G : Type} [Group G] (N : Subgroup G) {g : G} {a b : ℕ}
    (hab : Nat.Coprime a b) (ha : g ^ a ∈ N) (hb : g ^ b = 1) : g ∈ N := by
  have huv : (1 : ℤ) = a * Nat.gcdA a b + b * Nat.gcdB a b := by
    have h := Nat.gcd_eq_gcd_ab a b
    rwa [hab.gcd_eq_one, Nat.cast_one] at h
  have h1 : g = (g ^ a) ^ (Nat.gcdA a b) * (g ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← huv, zpow_one]
  rw [h1, hb, one_zpow, mul_one]
  exact N.zpow_mem ha _

theorem pow_mul_mem_of_normalizes {G : Type} [Group G] (N : Subgroup G) {n y : G} (hn : n ∈ N)
    (hy : ∀ x ∈ N, y * x * y⁻¹ ∈ N) (k : ℕ) : ∃ n' ∈ N, (n * y) ^ k = n' * y ^ k := by
  have hconj : ∀ k : ℕ, ∀ x ∈ N, y ^ k * x * (y ^ k)⁻¹ ∈ N := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih =>
      intro x hx
      have e : y ^ (k + 1) * x * (y ^ (k + 1))⁻¹ = y * (y ^ k * x * (y ^ k)⁻¹) * y⁻¹ := by
        rw [pow_succ', mul_inv_rev]
        group
      rw [e]
      exact hy _ (ih x hx)
  induction k with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨n', hn', hk⟩ := ih
    refine ⟨n' * (y ^ k * n * (y ^ k)⁻¹), N.mul_mem hn' (hconj k n hn), ?_⟩
    rw [pow_succ, hk, pow_succ]
    group

theorem mem_of_mul_of_coprime_orders {G : Type} [Group G] (N : Subgroup G) {n y g : G}
    (hn : n ∈ N) (hy : ∀ x ∈ N, y * x * y⁻¹ ∈ N) (hg : g = n * y) {a b : ℕ} (hya : y ^ a = 1)
    (hgb : g ^ b = 1) (hab : Nat.Coprime a b) : g ∈ N := by
  obtain ⟨n', hn', hpow⟩ := pow_mul_mem_of_normalizes N hn hy a
  refine mem_of_pow_mem_of_coprime N hab ?_ hgb
  rw [hg, hpow, hya, mul_one]
  exact hn'

theorem exists_normal_two_complement_of_order_two {G : Type} [Group G] [Finite G]
    (C₁ : Subgroup G) (z : G) (hz : z ∈ C₁) (hz2 : orderOf z = 2)
    (hsyl : ∀ S : Subgroup G, S ≤ C₁ → IsPGroup 2 ↥S → Subgroup.zpowers z ≤ S →
      S = Subgroup.zpowers z) :
    ∃ V : Subgroup G, V ≤ C₁ ∧ (∀ g ∈ C₁, ∀ v ∈ V, g * v * g⁻¹ ∈ V) ∧ Odd (Nat.card ↥V) ∧
      (∀ g ∈ C₁, Odd (orderOf g) → g ∈ V) ∧ Nat.card ↥C₁ = 2 * Nat.card ↥V := by
  let z' : C₁ := ⟨z, hz⟩
  have hz'2 : orderOf z' = 2 := (Subgroup.orderOf_mk z hz).trans hz2
  let P₀ : Subgroup C₁ := Subgroup.zpowers z'
  have hP₀card : Nat.card P₀ = 2 := by rw [Nat.card_zpowers, hz'2]
  have hP₀p : IsPGroup 2 P₀ := IsPGroup.of_card (n := 1) (by rw [hP₀card, pow_one])
  have hmax : ∀ Q : Subgroup C₁, IsPGroup 2 Q → P₀ ≤ Q → Q = P₀ := by
    intro Q hQ hle
    have hS : Subgroup.zpowers z ≤ Q.map C₁.subtype := by
      rw [Subgroup.zpowers_le]
      exact ⟨z', hle (Subgroup.mem_zpowers z'), rfl⟩
    have h := hsyl (Q.map C₁.subtype) (Subgroup.map_subtype_le Q) (hQ.map C₁.subtype) hS
    have h2 : P₀.map C₁.subtype = Subgroup.zpowers z := by
      rw [MonoidHom.map_zpowers]; rfl
    exact Subgroup.map_injective C₁.subtype_injective (h.trans h2.symm)
  obtain ⟨P, hP⟩ := hP₀p.exists_le_sylow
  have hPeq : (P : Subgroup C₁) = P₀ := hmax P P.isPGroup' hP
  have hPcard : Nat.card (P : Subgroup C₁) = 2 := by rw [hPeq]; exact hP₀card
  have hcyc : IsCyclic (P : Subgroup C₁) := by rw [hPeq]; infer_instance
  have hdvd : 2 ∣ Nat.card C₁ := hz'2 ▸ orderOf_dvd_natCard z'
  have hp : (Nat.card C₁).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr hdvd
  have hcompl := IsCyclic.isComplement' hp hcyc
  have hnd := MonoidHom.not_dvd_card_ker_transferSylow P (hcyc.normalizer_le_centralizer hp)
  set φ := MonoidHom.transferSylow P (hcyc.normalizer_le_centralizer hp)
  have hVcard : Nat.card (φ.ker.map C₁.subtype) = Nat.card φ.ker :=
    (Nat.card_congr (φ.ker.equivMapOfInjective C₁.subtype C₁.subtype_injective).toEquiv).symm
  refine ⟨φ.ker.map C₁.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · rintro g hg _ ⟨v, hv, rfl⟩
    have hnorm : φ.ker.Normal := MonoidHom.normal_ker φ
    have hc : (⟨g, hg⟩ : C₁) * v * (⟨g, hg⟩ : C₁)⁻¹ ∈ φ.ker := hnorm.conj_mem v hv ⟨g, hg⟩
    exact ⟨_, hc, rfl⟩
  · rw [hVcard]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hnd)
  · intro g hg hodd
    have h1 : orderOf (φ ⟨g, hg⟩) ∣ orderOf g :=
      (Subgroup.orderOf_mk g hg) ▸ orderOf_map_dvd φ ⟨g, hg⟩
    have h2 : orderOf (φ ⟨g, hg⟩) ∣ 2 := by
      have h := orderOf_dvd_natCard (φ ⟨g, hg⟩)
      rwa [hPcard] at h
    have h3 : orderOf (φ ⟨g, hg⟩) = 1 := Nat.eq_one_of_dvd_coprimes hodd.coprime_two_right h1 h2
    exact ⟨⟨g, hg⟩, orderOf_eq_one_iff.mp h3, rfl⟩
  · rw [hVcard, ← hcompl.card_mul_card, hPcard, mul_comm]

theorem mem_K_or_mul_of_index_two {G : Type} [Group G] [Finite G] (S K : Subgroup G) (t : G)
    (htS : t ∈ S) (htK : t ∉ K) (hindex : Nat.card ↥S = 2 * Nat.card ↥(S ⊓ K)) :
    ∀ s ∈ S, s ∈ K ∨ s * t ∈ K := by
  set H : Subgroup S := (S ⊓ K).subgroupOf S with hH
  have hcard : Nat.card H = Nat.card ↥(S ⊓ K) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hpos : 0 < Nat.card ↥(S ⊓ K) := Nat.card_pos
  have hidx : H.index = 2 := by
    have h := H.card_mul_index
    rw [hcard, hindex] at h
    have : Nat.card ↥(S ⊓ K) * H.index = Nat.card ↥(S ⊓ K) * 2 := by
      rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos this
  intro s hs
  have htH : (⟨t, htS⟩ : S) ∉ H := by
    rw [hH, Subgroup.mem_subgroupOf]
    exact fun h => htK h.2
  have key := Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨s, hs⟩ : S)) (b := ⟨t, htS⟩)
  by_cases hsH : (⟨s, hs⟩ : S) ∈ H
  · left
    rw [hH, Subgroup.mem_subgroupOf] at hsH
    exact hsH.2
  · right
    have h2 : (⟨s, hs⟩ : S) * ⟨t, htS⟩ ∈ H := key.mpr (by tauto)
    rw [hH, Subgroup.mem_subgroupOf] at h2
    exact h2.2

end CFSG.GH74.GLS.SP.Local
