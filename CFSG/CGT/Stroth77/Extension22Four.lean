module

public import CFSG.CGT.Stroth77.Extension22Cocycle

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C : Subgroup S} {m : ℕ}

theorem index_four_of_relIndex (hBC : B ≤ C) (hrel : Nat.card C = 4 * Nat.card B) :
    (B.subgroupOf C).index = 4 := by
  have hcard : Nat.card (B.subgroupOf C) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  have hmul : Nat.card (B.subgroupOf C) * (B.subgroupOf C).index = Nat.card C :=
    Subgroup.card_mul_index (B.subgroupOf C)
  rw [hcard, hrel, mul_comm 4 (Nat.card B)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

theorem zsmul_gen_eq_zero {k : Fin 3 → ℕ} (j : Fin 3) (n : ℤ) :
    n • gen k j = 0 ↔ (n : ZMod (2 ^ k j)) = 0 := by
  constructor
  · intro h
    have := congrFun h j
    simpa [gen, Pi.single_eq_same, zsmul_eq_mul] using this
  · intro h
    funext i
    by_cases hi : i = j
    · subst hi
      simpa [gen, Pi.single_eq_same, zsmul_eq_mul] using h
    · simp [gen, Pi.single_eq_of_ne hi]

theorem t100_fixed_rho_t (m : ℕ) (y : Torus (Type100.k m))
    (hρ : (Type100.action m).φρ y = y)
    (ht : (Type100.action m).φt y = y) : y = 0 := by
  obtain ⟨i, j, l, hy⟩ := torus_eq_zsmul_gens (Type100.k m) y
  have hρ0 : (Type100.action m).φρ (gen (Type100.k m) 0) = gen (Type100.k m) 0 := by
    simpa [Torus.c] using Type100.rho_c m
  have hρ1 : (Type100.action m).φρ (gen (Type100.k m) 1) = gen (Type100.k m) 2 := by
    simpa [Torus.a, Torus.b] using Type100.rho_a m
  have hρ2 : (Type100.action m).φρ (gen (Type100.k m) 2) =
      (-2 : ℤ) • gen (Type100.k m) 0 + (-1 : ℤ) • gen (Type100.k m) 1 +
        (-1 : ℤ) • gen (Type100.k m) 2 := by
    simpa [Torus.a, Torus.b, Torus.c] using Type100.rho_b m
  have hρ' : (Type100.action m).φρ
      (i • gen (Type100.k m) 0 + j • gen (Type100.k m) 1 + l • gen (Type100.k m) 2) =
      i • gen (Type100.k m) 0 + j • gen (Type100.k m) 1 +
        l • gen (Type100.k m) 2 := by
    rw [← hy]
    exact hρ
  rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hρ0, hρ1, hρ2] at hρ'
  have hρ'' : (i - 2 * l) • gen (Type100.k m) 0 + (-l) • gen (Type100.k m) 1 +
      (j - l) • gen (Type100.k m) 2 =
      i • gen (Type100.k m) 0 + j • gen (Type100.k m) 1 +
        l • gen (Type100.k m) 2 := by
    have h := hρ'
    rw [zsmul_gens] at h
    linear_combination h
  have hjal : (j : ZMod (2 ^ (m + 1))) = -(l : ZMod (2 ^ (m + 1))) := by
    have h' := gens_coord_one hρ''
    rw [k100_one] at h'
    rw [Int.cast_neg] at h'
    exact h'.symm
  have hj2l : (j : ZMod (2 ^ (m + 1))) = 2 * (l : ZMod (2 ^ (m + 1))) := by
    have h' := gens_coord_two hρ''
    rw [k100_two] at h'
    rw [Int.cast_sub] at h'
    linear_combination h'
  have h3l : (3 : ZMod (2 ^ (m + 1))) * (l : ZMod (2 ^ (m + 1))) = 0 := by
    have h : (2 : ZMod (2 ^ (m + 1))) * (l : ZMod (2 ^ (m + 1))) -
        (-(l : ZMod (2 ^ (m + 1)))) = 0 := by
      rw [← hj2l, ← hjal, sub_self]
    convert h using 1 <;> ring
  have hcop : Nat.Coprime 3 (2 ^ (m + 1)) := by
    rw [Nat.coprime_comm]
    exact (Nat.coprime_pow_left_iff (by omega : 0 < m + 1) 2 3).2 (by decide)
  have h3unit : IsUnit (3 : ZMod (2 ^ (m + 1))) :=
    (ZMod.isUnit_iff_coprime 3 (2 ^ (m + 1))).2 hcop
  have hl : (l : ZMod (2 ^ (m + 1))) = 0 := by
    have h3l' : (l : ZMod (2 ^ (m + 1))) * (3 : ZMod (2 ^ (m + 1))) = 0 := by
      rw [mul_comm]; exact h3l
    exact (h3unit.mul_left_eq_zero).mp h3l'
  have hj : (j : ZMod (2 ^ (m + 1))) = 0 := by
    rw [hjal, hl, neg_zero]
  have ht' : (Type100.action m).φt (i • gen (Type100.k m) 0) =
      i • gen (Type100.k m) 0 := by
    have h' := ht
    rw [hy] at h'
    have hj0 : j • gen (Type100.k m) 1 = 0 := (zsmul_gen_eq_zero 1 j).2 hj
    have hl0 : l • gen (Type100.k m) 2 = 0 := (zsmul_gen_eq_zero 2 l).2 hl
    rw [hj0, hl0, add_zero] at h'
    simpa using h'
  have ht0 : (Type100.action m).φt (gen (Type100.k m) 0) =
      gen (Type100.k m) 0 + (2 : ℤ) • gen (Type100.k m) 1 := by
    simpa [Torus.c, Torus.a] using Type100.t_c m
  rw [map_zsmul, ht0, smul_add, smul_smul, mul_comm i 2] at ht'
  have h2i : (2 * i : ℤ) • gen (Type100.k m) 1 = 0 := by
    have h' : i • gen (Type100.k m) 0 + (2 * i : ℤ) • gen (Type100.k m) 1 =
        i • gen (Type100.k m) 0 + 0 := by
      simpa using ht'
    exact add_left_cancel h'
  have h2i' : ((2 * i : ℤ) : ZMod (2 ^ (m + 1))) = 0 := (zsmul_gen_eq_zero 1 (2 * i)).1 h2i
  have hdiv : (2 : ℤ) ^ (m + 1) ∣ 2 * i := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * i) (2 ^ (m + 1))).mp h2i'
    simpa [Nat.cast_pow] using h
  have hdvd : (2 : ℤ) ^ m ∣ i := dvd_of_dvd_two_mul hdiv
  have hi : (i : ZMod (2 ^ m)) = 0 := by
    have h := (ZMod.intCast_zmod_eq_zero_iff_dvd i (2 ^ m)).mpr hdvd
    simpa [Nat.cast_pow] using h
  have hi0 : i • gen (Type100.k m) 0 = 0 := (zsmul_gen_eq_zero 0 i).2 hi
  have hj0 : j • gen (Type100.k m) 1 = 0 := (zsmul_gen_eq_zero 1 j).2 hj
  have hl0 : l • gen (Type100.k m) 2 = 0 := (zsmul_gen_eq_zero 2 l).2 hl
  rw [hy, hi0, hj0, hl0, add_zero, add_zero]

theorem natCard_torus_t200 (m : ℕ) :
    Nat.card (Torus (Type200.k m)) = 4 * Nat.card (Torus (Type100.k m)) := by
  rw [natCard_torus, natCard_torus]
  simp [Type200.k, Type100.k]
  rw [show m + (m + 2) + (m + 2) = 3 * m + 4 by ring,
    show m + (m + 1) + (m + 1) = 3 * m + 2 by ring, pow_succ]
  ring

theorem t100_fixed_rho_t_of_mem {m : ℕ} {B : Subgroup S}
    (D : StrothTypeData B (StrothTypeIndex.t100 m)) {x : B}
    (hρ : conjBy D.ρ_mem x = x) (ht : conjBy D.t_mem x = x) : x = 1 := by
  have hxρ : (StrothTypeIndex.t100 m).action.φρ (D.e (Additive.ofMul x)) =
      D.e (Additive.ofMul x) := by
    rw [← D.ρ_conj x, hρ]
  have hxt : (StrothTypeIndex.t100 m).action.φt (D.e (Additive.ofMul x)) =
      D.e (Additive.ofMul x) := by
    rw [← D.t_conj x, ht]
  have h0 : D.e (Additive.ofMul x) = 0 := by
    apply t100_fixed_rho_t m
    · exact hxρ
    · exact hxt
  apply Additive.ofMul.injective
  simpa using h0

end CFSG.CGT.Stroth77
