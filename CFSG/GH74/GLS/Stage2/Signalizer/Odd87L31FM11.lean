module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Kind
import CFSG.GH74.GLS.Stage2.Local.P27.QIdArith

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Blueprint

section M11Perm

private abbrev l31fA : Equiv.Perm (Fin 11) :=
  List.formPerm [1, 9] * List.formPerm [3, 10] * List.formPerm [4, 6] * List.formPerm [7, 8]

private abbrev l31fB : Equiv.Perm (Fin 11) :=
  List.formPerm [0, 3, 2, 7] * List.formPerm [1, 4, 5, 8]

private theorem l31fA_mem : l31fA ∈ NativeSporadic.M11 :=
  Subgroup.subset_closure (Set.mem_insert _ _)

private theorem l31fB_mem : l31fB ∈ NativeSporadic.M11 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

private theorem orderOf_l31fAB : orderOf (l31fA * l31fB) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  refine orderOf_eq_prime ?_ ?_
  · ext i
    revert i
    decide +kernel
  · intro h
    have := congrArg (fun f : Equiv.Perm (Fin 11) => f 0) h
    revert this
    decide +kernel

private theorem orderOf_l31fW :
    orderOf (l31fA * l31fB * l31fA * l31fB * l31fB * l31fA * l31fB * l31fB) = 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := orderOf_eq_prime_pow (p := 2) (n := 2)
    (x := l31fA * l31fB * l31fA * l31fB * l31fB * l31fA * l31fB * l31fB)
    (by
      intro h
      have := congrArg (fun f : Equiv.Perm (Fin 11) => f 0) h
      revert this
      decide +kernel)
    (by
      ext i
      revert i
      decide +kernel)
  simpa using h

private theorem l31fAB_transitive : ∀ j : Fin 11, ∃ i : ℕ, ((l31fA * l31fB) ^ i) 0 = j := by
  have h : ∀ j : Fin 11, ∃ i : Fin 11, ((l31fA * l31fB) ^ (i : ℕ)) 0 = j := by decide +kernel
  intro j
  obtain ⟨i, hi⟩ := h j
  exact ⟨i, hi⟩

private theorem l31fAB_pow_comm_B : ∀ j : Fin 11,
    (l31fA * l31fB) ^ (j : ℕ) * l31fB = l31fB * (l31fA * l31fB) ^ (j : ℕ) → j = 0 := by
  decide +kernel

private theorem l31f_exists_pow_of_commute {α : Type} {σ τ : Equiv.Perm α} {a : α}
    (htrans : ∀ j, ∃ i : ℕ, (σ ^ i) a = j) (hc : τ * σ = σ * τ) : ∃ k : ℕ, τ = σ ^ k := by
  obtain ⟨k, hk⟩ := htrans (τ a)
  refine ⟨k, ?_⟩
  ext j
  obtain ⟨i, rfl⟩ := htrans j
  have h1 : τ ((σ ^ i) a) = (σ ^ i) (τ a) := by
    have := congrArg (fun f : Equiv.Perm α => f a)
      (Commute.pow_right (show Commute τ σ from hc) i).eq
    simpa [Equiv.Perm.mul_apply] using this
  calc τ ((σ ^ i) a) = (σ ^ i) (τ a) := h1
    _ = (σ ^ i) ((σ ^ k) a) := by rw [hk]
    _ = (σ ^ k) ((σ ^ i) a) := by
      rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add, add_comm]

theorem l31f_center_m11_eq_bot : center ↥NativeSporadic.M11 = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hx : (c : Equiv.Perm (Fin 11)) * (l31fA * l31fB) = (l31fA * l31fB) * c := by
    have := Subgroup.mem_center_iff.mp hc ⟨l31fA * l31fB, mul_mem l31fA_mem l31fB_mem⟩
    exact (congrArg Subtype.val this).symm
  have hb : (c : Equiv.Perm (Fin 11)) * l31fB = l31fB * c := by
    have := Subgroup.mem_center_iff.mp hc ⟨l31fB, l31fB_mem⟩
    exact (congrArg Subtype.val this).symm
  obtain ⟨k, hk⟩ := l31f_exists_pow_of_commute l31fAB_transitive hx
  have hk' : (c : Equiv.Perm (Fin 11)) = (l31fA * l31fB) ^ (k % 11) := by
    rw [hk, ← pow_mod_orderOf, orderOf_l31fAB]
  have hcomm : (l31fA * l31fB) ^ (k % 11) * l31fB = l31fB * (l31fA * l31fB) ^ (k % 11) := by
    rw [← hk']
    exact hb
  have h0 := l31fAB_pow_comm_B ⟨k % 11, Nat.mod_lt _ (by norm_num)⟩ hcomm
  have hk0 : k % 11 = 0 := congrArg Fin.val h0
  apply Subtype.ext
  rw [hk', hk0]
  rfl

theorem l31f_eleven_dvd_card_m11 : 11 ∣ Nat.card ↥NativeSporadic.M11 := by
  have h := orderOf_dvd_natCard
    (⟨l31fA * l31fB, mul_mem l31fA_mem l31fB_mem⟩ : ↥NativeSporadic.M11)
  rwa [Subgroup.orderOf_mk, orderOf_l31fAB] at h

theorem l31f_eight_dvd_card_m11 : 8 ∣ Nat.card ↥NativeSporadic.M11 := by
  have hm : l31fA * l31fB * l31fA * l31fB * l31fB * l31fA * l31fB * l31fB ∈ NativeSporadic.M11 := by
    have h1 := mul_mem l31fA_mem l31fB_mem
    have h2 := mul_mem (mul_mem (mul_mem h1 l31fA_mem) l31fB_mem) l31fB_mem
    exact mul_mem (mul_mem (mul_mem h2 l31fA_mem) l31fB_mem) l31fB_mem
  have h := orderOf_dvd_natCard
    (⟨l31fA * l31fB * l31fA * l31fB * l31fB * l31fA * l31fB * l31fB, hm⟩ : ↥NativeSporadic.M11)
  rwa [Subgroup.orderOf_mk, orderOf_l31fW] at h

theorem l31f_card_m11_dvd_factorial : Nat.card ↥NativeSporadic.M11 ∣ Nat.factorial 11 := by
  have h := Subgroup.card_subgroup_dvd_card NativeSporadic.M11
  rwa [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin 11)), Fintype.card_perm,
    Fintype.card_fin] at h

end M11Perm

section Arith

theorem l31f_false_of_l2_card {r p n : ℕ} (hp : p.Prime) (hn : 1 ≤ n) (hr : r = p ^ n)
    (hr5 : 5 ≤ r) (hd : r * (r ^ 2 - 1) / 2 ∣ Nat.factorial 11)
    (h11 : 11 ∣ r * (r ^ 2 - 1) / 2) (h8 : 8 ∣ r * (r ^ 2 - 1) / 2) : False := by
  have hf : Nat.factorial 11 = 39916800 := by decide
  rw [hf] at hd
  have hle : r * (r ^ 2 - 1) / 2 ≤ 39916800 := Nat.le_of_dvd (by norm_num) hd
  have hr500 : r ≤ 500 := by
    by_contra h
    push Not at h
    have h1 : 501 * (501 ^ 2 - 1) / 2 ≤ r * (r ^ 2 - 1) / 2 := by
      apply Nat.div_le_div_right
      apply Nat.mul_le_mul h
      have : 501 ^ 2 ≤ r ^ 2 := Nat.pow_le_pow_left h 2
      omega
    omega
  have h55 : r = 55 := by
    interval_cases r <;> omega
  subst h55
  have hpd : p ∣ 5 * 11 := by
    rw [show 5 * 11 = p ^ n from hr]
    exact dvd_pow_self p (by omega)
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h5 | h11'
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
    have hn3 : n ≤ 3 := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 5 by norm_num) (show 4 ≤ n by omega)
      omega
    interval_cases n <;> omega
  · obtain rfl := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h11'
    have hn2 : n ≤ 2 := by
      by_contra h
      have := Nat.pow_le_pow_right (show 0 < 11 by norm_num) (show 3 ≤ n by omega)
      omega
    interval_cases n <;> omega

end Arith

section Kinds

private theorem l31f_not_eleven_dvd_factorial {n : ℕ} (hn : n ≤ 10) : ¬ 11 ∣ Nat.factorial n := by
  intro h
  have := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 11)).mp h
  omega

theorem l31f_not_kindFactorAll_m11 {k : Kind} (hk : k ≠ Kind.ly) {Y : Type} [Group Y]
    (hd : Nat.card Y ∣ Nat.factorial 11) (h11 : 11 ∣ Nat.card Y) (h8 : 8 ∣ Nat.card Y) :
    ¬ KindFactorAll k Y := by
  have hL2 : ¬ IVK.IsL2 Y (fun r => Odd r ∧ 5 ≤ r) := by
    rintro ⟨F, _, _, ⟨hodd, h5⟩, ⟨e⟩⟩
    have h1 : IVK.IsL2 Y (fun r => r = Nat.card F) := ⟨F, inferInstance, inferInstance, rfl, ⟨e⟩⟩
    have hcard := Local.P27.QId.card_isL2 hodd h1
    obtain ⟨p, n, hp, -, hn, hpn⟩ := IVK.isOddPrimePower_of_L2Field (F := F) ⟨hodd, by omega⟩
    rw [hcard] at hd h11 h8
    exact l31f_false_of_l2_card hp hn hpn h5 hd h11 h8
  have hAlt : ∀ n : ℕ, 7 ≤ n → n ≤ 10 → ¬ IsSection Y (alternatingGroup (Fin n)) := by
    intro n hn7 hn hs
    exact l31f_not_eleven_dvd_factorial hn
      (h11.trans (hs.card_dvd.trans (card_alt_dvd_factorial n (by omega))))
  intro h
  cases k with
  | ly => exact hk rfl
  | g2 => exact hL2 h
  | psp4 => exact hL2 h
  | m12 => exact hL2 h
  | l4 ε =>
    rcases h with h | h
    · exact hL2 h
    · exact hAlt 7 le_rfl (by norm_num) h
  | mcl =>
    obtain ⟨n, hn8, hn, hs⟩ := h
    exact hAlt n (by omega) (by omega) hs

end Kinds

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
