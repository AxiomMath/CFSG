module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingData

public section

namespace CFSG.ComponentClassification.Asc76X

open Subgroup

section OddKernel

variable {H Q : Type*} [Group H] [Group Q] [Finite H] (f : H →* Q)

omit [Finite H] in
theorem card_map_mul_card_inf_ker (A : Subgroup H) :
    Nat.card (A.map f) * Nat.card (f.ker ⊓ A : Subgroup H) = Nat.card A := by
  rw [← relIndex_ker, relIndex, mul_comm]
  have h := index_mul_card (f.ker.subgroupOf A)
  have h2 : Nat.card (f.ker.subgroupOf A) = Nat.card (f.ker ⊓ A : Subgroup H) := by
    rw [← card_map_of_injective A.subtype_injective, subgroupOf_map_subtype]
  rw [← h2, mul_comm]
  exact h

omit [Finite H] in
theorem eq_one_of_two_element_of_ker (hk : Odd (Nat.card f.ker)) {x : H} {k : ℕ}
    (hx : x ^ (2 ^ k) = 1) (hfx : f x = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hx
  have h2 : orderOf x ∣ Nat.card f.ker := orderOf_dvd_natCard f.ker hfx
  have hcop : Nat.Coprime (2 ^ k) (Nat.card f.ker) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hk)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_two_element_preimage {A : Subgroup H} {y : Q} (hy : y ∈ A.map f) {k : ℕ}
    (hyk : y ^ (2 ^ k) = 1) : ∃ x ∈ A, (∃ i : ℕ, x ^ (2 ^ i) = 1) ∧ f x = y := by
  obtain ⟨a, haA, rfl⟩ := hy
  obtain ⟨i, m, hm, hn⟩ : ∃ i m : ℕ, Odd m ∧ orderOf a = 2 ^ i * m :=
    Nat.exists_eq_two_pow_mul_odd (orderOf_pos a).ne'
  have hcop : Nat.Coprime m (2 ^ k) := Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hm)
  rcases Nat.lt_or_ge 1 (2 ^ k) with hk | hk
  · obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hk
    refine ⟨a ^ (m * m'), pow_mem haA _, ⟨i, ?_⟩, ?_⟩
    · rw [← pow_mul, show m * m' * 2 ^ i = (2 ^ i * m) * m' by ring, pow_mul, ← hn,
        pow_orderOf_eq_one, one_pow]
    · rw [map_pow]
      by_cases h1 : orderOf (f a) = 1
      · rw [orderOf_eq_one_iff.mp h1, one_pow]
      · rw [← pow_mod_orderOf]
        have hord : orderOf (f a) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hyk
        rw [← Nat.mod_mod_of_dvd _ hord, hm', Nat.one_mod_eq_one.mpr h1, pow_one]
  · have h1 : 2 ^ k = 1 := le_antisymm hk Nat.one_le_two_pow
    rw [h1, pow_one] at hyk
    exact ⟨1, one_mem _, ⟨0, by simp⟩, by rw [map_one, hyk]⟩

end OddKernel

end CFSG.ComponentClassification.Asc76X

namespace CFSG.ComponentClassification.RankTwoBender

open Subgroup CFSG.ComponentClassification.AschbacherTightEmbedding

variable {H Q : Type*} [Group H] [Group Q] [Finite H] (f : H →* Q)

theorem inf_eq_bot_of_isPGroup_of_odd {P K : Subgroup H} (hP : IsPGroup 2 P)
    (hK : Odd (Nat.card K)) : P ⊓ K = ⊥ :=
  two_subgroup_of_odd_eq_bot (P ⊓ K) K hP.to_inf_left hK inf_le_right

theorem card_map_of_isPGroup (hk : Odd (Nat.card f.ker)) {P : Subgroup H} (hP : IsPGroup 2 P) :
    Nat.card (P.map f) = Nat.card P := by
  have h := Asc76X.card_map_mul_card_inf_ker f P
  have hbot : f.ker ⊓ P = ⊥ := by
    rw [inf_comm]
    exact inf_eq_bot_of_isPGroup_of_odd hP hk
  rw [hbot, card_bot, mul_one] at h
  exact h

theorem exists_involution_preimage (hk : Odd (Nat.card f.ker)) {A : Subgroup H} {y : Q}
    (hy : y ∈ A.map f) (hy2 : y * y = 1) : ∃ x ∈ A, x * x = 1 ∧ f x = y := by
  obtain ⟨x, hxA, ⟨i, hxi⟩, hfx⟩ := Asc76X.exists_two_element_preimage f hy (k := 1)
    (by rw [pow_one, sq, hy2])
  refine ⟨x, hxA, ?_, hfx⟩
  have h1 : f (x * x) = 1 := by rw [map_mul, hfx, hy2]
  apply Asc76X.eq_one_of_two_element_of_ker f hk (k := i) _ h1
  rw [← sq, ← pow_mul, ← pow_succ', pow_succ, pow_mul, hxi, one_pow]

theorem tightlyEmbedded_map_of_odd_ker (hf : Function.Surjective f)
    (hk : Odd (Nat.card f.ker)) {X : Subgroup H} (hX : TightlyEmbedded X) :
    TightlyEmbedded (X.map f) := by
  classical
  have : Finite Q := Finite.of_surjective f hf
  refine ⟨?_, fun q hq => ?_⟩
  ·
    have h := Asc76X.card_map_mul_card_inf_ker f X
    have hodd : Odd (Nat.card (f.ker ⊓ X : Subgroup H)) :=
      hk.of_dvd_nat (card_dvd_of_le inf_le_left)
    have heven := hX.1
    rw [← h] at heven
    exact (Nat.even_mul.mp heven).resolve_right (Nat.not_even_iff_odd.mpr hodd)
  · by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨⟨yb, hyb⟩, hybord⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    have hyb2 : yb * yb = 1 := by
      have := pow_orderOf_eq_one (⟨yb, hyb⟩ : (X.map f ⊓ rightConjugate (X.map f) q : Subgroup Q))
      rw [hybord, sq] at this
      exact congrArg Subtype.val this
    have hyb1 : yb ≠ 1 := by
      intro h
      have h' : (⟨yb, hyb⟩ : (X.map f ⊓ rightConjugate (X.map f) q : Subgroup Q)) = 1 :=
        Subtype.ext h
      rw [h', orderOf_one] at hybord
      exact absurd hybord (by norm_num)
    obtain ⟨g, rfl⟩ := hf q
    obtain ⟨x, hxX, hx2, hfx⟩ := exists_involution_preimage f hk hyb.1 hyb2
    have hqyb : f g * yb * (f g)⁻¹ ∈ X.map f := (mem_rightConjugate_iff _ _ _).mp hyb.2
    obtain ⟨z, hzX, hz2, hfz⟩ := exists_involution_preimage f hk hqyb
      (by rw [show f g * yb * (f g)⁻¹ * (f g * yb * (f g)⁻¹) = f g * (yb * yb) * (f g)⁻¹ by group,
        hyb2, mul_one, mul_inv_cancel])
    set x' := g⁻¹ * z * g with hx'
    have hfx' : f x' = yb := by
      rw [hx', map_mul, map_mul, map_inv, hfz]
      group
    have hx'2 : x' * x' = 1 := by
      rw [hx', show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group, hz2, mul_one,
        inv_mul_cancel]
    set n := x * x' with hn
    have hnk : n ∈ f.ker := by
      rw [MonoidHom.mem_ker, hn, map_mul, hfx, hfx', hyb2]
    have hxnx : x * n * x = n⁻¹ := by
      rw [hn, mul_inv_rev, inv_eq_of_mul_eq_one_right hx2, inv_eq_of_mul_eq_one_right hx'2,
        show x * (x * x') * x = (x * x) * x' * x by group, hx2, one_mul]
    have hnodd : Odd (orderOf n) := by
      have := orderOf_dvd_natCard (⟨n, hnk⟩ : f.ker)
      rw [Subgroup.orderOf_mk] at this
      exact hk.of_dvd_nat this
    obtain ⟨m, hm⟩ := hnodd
    set h := n ^ (m + 1) with hh
    have hconj : ∀ k : ℕ, x * n ^ k * x = (n ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => rw [pow_zero, mul_one, hx2, inv_one]
      | succ k ih =>
        have e1 : x * n ^ (k + 1) * x = (x * n ^ k * x) * (x * n * x) := by
          rw [pow_succ]
          calc x * (n ^ k * n) * x = x * n ^ k * (x * x) * n * x := by rw [hx2]; group
            _ = (x * n ^ k * x) * (x * n * x) := by group
        rw [e1, ih, hxnx, ← mul_inv_rev, ← pow_succ']
    have hx'h : x' = h⁻¹ * x * h := by
      have h2 : n ^ (2 * (m + 1)) = n := by
        rw [show 2 * (m + 1) = orderOf n + 1 by omega, pow_succ, pow_orderOf_eq_one, one_mul]
      have hxh : x * h = h⁻¹ * x := by
        have := hconj (m + 1)
        rw [← hh] at this
        calc x * h = (x * h * x) * x := by rw [mul_assoc _ x x, hx2, mul_one]
          _ = h⁻¹ * x := by rw [this]
      calc x' = x * n := by rw [hn, ← mul_assoc, hx2, one_mul]
        _ = x * (h * h) := by rw [hh, ← pow_add, show m + 1 + (m + 1) = 2 * (m + 1) by ring, h2]
        _ = (x * h) * h := by group
        _ = h⁻¹ * x * h := by rw [hxh]
    have hhk : h ∈ f.ker := pow_mem hnk _
    have hxmem : x ∈ X ⊓ rightConjugate X (g * h⁻¹) := by
      refine ⟨hxX, (mem_rightConjugate_iff _ _ _).mpr ?_⟩
      have : g * h⁻¹ * x * (g * h⁻¹)⁻¹ = g * x' * g⁻¹ := by rw [hx'h]; group
      rw [this, hx']
      convert hzX using 1
      group
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hyb1 (by rw [← hfx, map_one])
    have hN : g * h⁻¹ ∈ normalizer (X : Set H) := by
      by_contra hN
      have hodd := hX.2 _ hN
      have := orderOf_dvd_natCard (⟨x, hxmem⟩ : (X ⊓ rightConjugate X (g * h⁻¹) : Subgroup H))
      have hord : orderOf (⟨x, hxmem⟩ : (X ⊓ rightConjugate X (g * h⁻¹) : Subgroup H)) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [sq, hx2]) hx1
      rw [hord] at this
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr this)
    apply hq
    have hfg : f (g * h⁻¹) = f g := by rw [map_mul, map_inv, MonoidHom.mem_ker.mp hhk, inv_one,
      mul_one]
    rw [← hfg]
    rw [mem_normalizer_iff]
    intro w
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨g * h⁻¹ * v * (g * h⁻¹)⁻¹, (mem_normalizer_iff.mp hN v).mp hv, by simp⟩
    · rintro ⟨v, hv, hvw⟩
      refine ⟨(g * h⁻¹)⁻¹ * v * (g * h⁻¹), ?_, ?_⟩
      · have := (mem_normalizer_iff.mp hN ((g * h⁻¹)⁻¹ * v * (g * h⁻¹))).mpr
        apply this
        rwa [show g * h⁻¹ * ((g * h⁻¹)⁻¹ * v * (g * h⁻¹)) * (g * h⁻¹)⁻¹ = v by group]
      · rw [map_mul, map_mul, map_inv, hvw]
        group

end CFSG.ComponentClassification.RankTwoBender
