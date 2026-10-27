module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient

theorem sq_mem_centralizer_of_mem_normalizer {M : Type*} [Group M] {c n : M}
    (hc : orderOf c = 3) (hn : n ∈ Subgroup.normalizer (Subgroup.zpowers c)) :
    n ^ 2 ∈ Subgroup.centralizer {c} := by
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hmem : n * c * n⁻¹ ∈ Subgroup.zpowers c := (Subgroup.mem_normalizer_iff.1 hn c).1
    (Subgroup.mem_zpowers c)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hc1 : c ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hc
    omega
  have hmod : c ^ a = c ^ (a % 3) := by
    have h := zpow_mod_orderOf c a
    rw [hc] at h
    exact_mod_cast h.symm
  have h3 : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have key : ∀ r : ℕ, n * c * n⁻¹ = c ^ r → r = 1 ∨ r = 2 → n ^ 2 * c = c * n ^ 2 := by
    intro r hr hr12
    have e1 : n * c = c ^ r * n := by
      rw [← hr]; group
    rcases hr12 with rfl | rfl
    · rw [pow_one] at e1
      rw [pow_two, mul_assoc, e1, ← mul_assoc, e1, mul_assoc]
    · have e2 : n * c = c ^ 2 * n := e1
      have c4 : c ^ 4 = c := by
        rw [show 4 = 3 + 1 from rfl, pow_succ, hc3, one_mul]
      have e3 : n * c ^ 2 = c * n := by
        calc n * c ^ 2 = (n * c) * c := by rw [pow_two, mul_assoc]
          _ = (c ^ 2 * n) * c := by rw [e2]
          _ = c ^ 2 * (n * c) := by rw [mul_assoc]
          _ = c ^ 2 * (c ^ 2 * n) := by rw [e2]
          _ = c ^ 4 * n := by rw [← mul_assoc, ← pow_add]
          _ = c * n := by rw [c4]
      calc n ^ 2 * c = n * (n * c) := by rw [pow_two, mul_assoc]
        _ = n * (c ^ 2 * n) := by rw [e2]
        _ = (n * c ^ 2) * n := by rw [mul_assoc]
        _ = c * n * n := by rw [e3]
        _ = c * n ^ 2 := by rw [mul_assoc, ← pow_two]
  rw [Subgroup.mem_centralizer_singleton_iff]
  symm
  rcases h3 with h | h | h
  · exfalso
    apply hc1
    have : n * c * n⁻¹ = 1 := by rw [← ha, hmod, h]; simp
    have h' := congrArg (fun x => n⁻¹ * x * n) this
    simpa [mul_assoc] using h'
  · have : n * c * n⁻¹ = c ^ (1 : ℕ) := by rw [← ha, hmod, h]; simp
    exact (key 1 this (Or.inl rfl)).symm
  · have : n * c * n⁻¹ = c ^ (2 : ℕ) := by rw [← ha, hmod, h]; simp
    exact (key 2 this (Or.inr rfl)).symm

theorem mem_map_centralizer_of_odd {M G : Type*} [Group M] [Group G] [Finite M] (φ : M →* G)
    {c : M} {m : ℕ} (hc : φ c = 1) (hord : orderOf c = 3) (hcard : Nat.card φ.ker = 3 * m)
    (hm : ¬ 3 ∣ m) (g : M) (hg : Odd (orderOf (φ g))) :
    φ g ∈ (Subgroup.centralizer {c}).map φ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcK : c ∈ φ.ker := hc
  let c' : φ.ker := ⟨c, hcK⟩
  have hc'ord : orderOf c' = 3 := by rw [← hord]; exact (Subgroup.orderOf_coe c').symm
  have hfac : (Nat.card φ.ker).factorization 3 = 1 := by
    rw [hcard, Nat.factorization_mul (by omega) (by rintro rfl; simp at hm),
      Finsupp.add_apply, Nat.Prime.factorization_self Nat.prime_three,
      Nat.factorization_eq_zero_of_not_dvd hm]
  have hH : Nat.card (Subgroup.zpowers c') = 3 ^ (Nat.card φ.ker).factorization 3 := by
    rw [Nat.card_zpowers, hc'ord, hfac]
    norm_num
  let P : Sylow 3 φ.ker := Sylow.ofCard (Subgroup.zpowers c') hH
  have hF := Sylow.normalizer_sup_eq_top P
  have hmap : (P.map φ.ker.subtype : Subgroup M) = Subgroup.zpowers c := by
    show (Subgroup.zpowers c').map φ.ker.subtype = _
    rw [MonoidHom.map_zpowers]
    rfl
  rw [hmap] at hF
  have hgtop : g ∈ Subgroup.normalizer (Subgroup.zpowers c) ⊔ φ.ker := by
    rw [hF]; exact Subgroup.mem_top g
  obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_right.1 hgtop
  have hφg : φ g = φ n := by
    rw [← hnk, map_mul, (MonoidHom.mem_ker.1 hk), mul_one]
  obtain ⟨s, hs⟩ := hg
  have hpow : (φ g) ^ orderOf (φ g) = 1 := pow_orderOf_eq_one _
  refine ⟨n ^ (orderOf (φ g) + 1), ?_, ?_⟩
  · have : n ^ (orderOf (φ g) + 1) = (n ^ 2) ^ (s + 1) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [this]
    exact Subgroup.pow_mem _ (sq_mem_centralizer_of_mem_normalizer hord hn) _
  · rw [map_pow, ← hφg, pow_succ, hpow, one_mul]

end CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient
