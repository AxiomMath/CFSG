module

public import CFSG.CGT.Stroth77.L4Sylow.Embed

public section

namespace CFSG.CGT.Stroth77.L4Sylow

open Equiv Matrix CFSG.Open

variable {K : Type} [Field K] {n q : ℕ}

namespace L4Data

variable (D : L4Data K n)

theorem zeta_pow_add_one (hq : 2 ^ n ∣ q + 1) : (D.ζ : K) ^ (q + 1) = 1 := by
  rw [← Units.val_pow_eq_pow_val, (orderOf_dvd_iff_pow_eq_one).mp (D.orderOf_ζ ▸ hq),
    Units.val_one]

theorem embed_map_pow_transpose_mul (hq0 : q ≠ 0) (hq : 2 ^ n ∣ q + 1) (a : L4Hat n) :
    (((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).map (· ^ q))ᵀ *
      ((D.embed a : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
  have hy : ∀ v : ℕ, ((D.ζ : K) ^ v) ^ q * (D.ζ : K) ^ v = 1 := fun v => by
    rw [← pow_mul, ← pow_add, show v * q + v = (q + 1) * v by ring, pow_mul,
      D.zeta_pow_add_one hq, one_pow]
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply, Matrix.map_apply, embed_apply_apply, ite_pow,
    zero_pow hq0, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [(a.right : Perm (Fin 4)).injective.eq_iff]
  split_ifs with h
  · exact hy _
  · exact mul_zero _

theorem embed_mem_statedSU (hn : 1 ≤ n) (hq : 2 ^ n ∣ q + 1) {a : L4Hat n} (ha : a ∈ L4P n) :
    D.embed a ∈ StatedSU 4 q K := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h2 : 2 ∣ 0 + 1 := (dvd_pow_self 2 (by omega : n ≠ 0)).trans hq
    omega
  exact Subgroup.subset_closure ⟨StatedAPI.mem_statedSL_iff.mp (D.embed_mem_statedSL hn ha),
    D.embed_map_pow_transpose_mul hq0 hq a⟩

@[expose] def toSU (hn : 1 ≤ n) (hq : 2 ^ n ∣ q + 1) : L4P n →* StatedSU 4 q K :=
  (D.embed.comp (L4P n).subtype).codRestrict (StatedSU 4 q K) fun a =>
    D.embed_mem_statedSU hn hq a.2

theorem coe_toSU (hn : 1 ≤ n) (hq : 2 ^ n ∣ q + 1) (a : L4P n) :
    ((D.toSU hn hq a : StatedSU 4 q K) : GL (Fin 4) K) = D.embed a := rfl

theorem toSU_injective (hn : 1 ≤ n) (hq : 2 ^ n ∣ q + 1) : Function.Injective (D.toSU hn hq) := by
  intro a b h
  apply Subtype.ext
  apply D.embed_injective
  rw [← coe_toSU D hn hq, ← coe_toSU D hn hq, h]

end L4Data

theorem exists_l4Data_of_card_eq_sq [Finite K] (hK : Nat.card K = q ^ 2) (h : 2 ^ n ∣ q + 1) :
    Nonempty (L4Data K n) := by
  have hsq := Nat.pow_two_sub_pow_two q 1
  rw [one_pow] at hsq
  exact exists_l4Data_of_dvd (h.trans ⟨q - 1, by rw [hK, hsq]⟩)

end CFSG.CGT.Stroth77.L4Sylow
