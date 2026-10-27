module

public import CFSG.GH74.Uniqueness.SU.KInputs2
public import CFSG.GH74.Uniqueness.SU.SU4Quot2

public section

namespace CFSG.GH74.Uniqueness.SU.K.KI8

open Subgroup CFSG.GH74.Uniqueness.SU.SU4

variable {H : Type} [Group H] [Finite H]

omit [Finite H] in
theorem T_le_cen {T : Sylow 2 H} {z : H} (hzc : ∀ t ∈ (T : Subgroup H), t * z = z * t) :
    (T : Subgroup H) ≤ centralizer ({z} : Set H) := by
  intro t ht
  exact mem_centralizer_singleton_iff.mpr (hzc t ht)

theorem isSylowIn_cen {T : Sylow 2 H} {z : H} (hzc : ∀ t ∈ (T : Subgroup H), t * z = z * t) :
    IsSylowIn (centralizer ({z} : Set H)) (T : Subgroup H) :=
  (sylow_isSylowIn_top T).of_le (T_le_cen hzc) le_top

theorem eq_of_two_pow_mul_odd {k k' m m' : ℕ} (hm : Odd m) (hm' : Odd m')
    (h : 2 ^ k * m = 2 ^ k' * m') : k = k' := by
  have h1 : padicValNat 2 (2 ^ k * m) = k := by
    rw [padicValNat.mul (by positivity) hm.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by simpa [Nat.odd_iff] using hm)]
    simp
  have h2 : padicValNat 2 (2 ^ k' * m') = k' := by
    rw [padicValNat.mul (by positivity) hm'.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by simpa [Nat.odd_iff] using hm')]
    simp
  rw [← h1, h, h2]

theorem card_T_of_card_cbar {T : Sylow 2 H} {z : H}
    (hzc : ∀ t ∈ (T : Subgroup H), t * z = z * t) {k m : ℕ} (hm : Odd m)
    (hcard : Nat.card (CBar H z) = 2 ^ k * m) : Nat.card (T : Subgroup H) = 2 ^ k := by
  obtain ⟨Tb, hTb⟩ := exists_sylow_barImage (centralizer ({z} : Set H)) (isSylowIn_cen hzc)
  obtain ⟨-, k', m', hk', hm', hX⟩ := (isSylowIn_iff_card).mp (sylow_isSylowIn_top Tb)
  rw [Subgroup.card_top] at hX
  have hk : k = k' := eq_of_two_pow_mul_odd hm hm' (hcard.symm.trans hX)
  have hcardT : Nat.card (T : Subgroup H) = Nat.card (Tb : Subgroup (CBar H z)) := by
    rw [hTb]
    exact Nat.card_congr (mulEquivBarImage (centralizer ({z} : Set H)) T.isPGroup'
      (T_le_cen hzc)).toEquiv
  rw [hcardT, hk', hk]

omit [Finite H] in
theorem le_of_isPGroup_of_odd_index {N : Subgroup H} [N.Normal] (hN : Odd N.index)
    {P : Subgroup H} (hP : IsPGroup 2 P) : P ≤ N := by
  intro x hx
  obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
  have h1 : (QuotientGroup.mk' N x) ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [this, map_one]
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    have := orderOf_dvd_natCard (QuotientGroup.mk' N x)
    rwa [← Subgroup.index] at this
  have h4 : Nat.Coprime (orderOf (QuotientGroup.mk' N x)) (2 ^ k) := by
    have : Nat.Coprime (orderOf (QuotientGroup.mk' N x)) 2 :=
      Nat.Coprime.coprime_dvd_left h3 (Nat.coprime_two_right.mpr hN)
    exact Nat.Coprime.pow_right k this
  have h5 : orderOf (QuotientGroup.mk' N x) = 1 := Nat.Coprime.eq_one_of_dvd h4 h2
  have h6 : QuotientGroup.mk' N x = 1 := orderOf_eq_one_iff.mp h5
  exact (QuotientGroup.eq_one_iff x).mp h6

theorem eq_top_of_aut_card {L : Subgroup H} [L.Normal] (hodd : Odd L.index)
    (hC : centralizer (L : Set H) = ⊥) (hA : Nat.card (MulAut L) ∣ 2 * Nat.card L) : L = ⊤ := by
  have hinj : Function.Injective (MulAut.conjNormal : H →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro h hh
    rw [MonoidHom.mem_ker] at hh
    have hcent : h ∈ centralizer (L : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 : h * l * h⁻¹ = l := by
        have := congrArg (fun a : MulAut L => ((a ⟨l, hl⟩ : L) : H)) hh
        simpa [MulAut.conjNormal_apply] using this
      calc l * h = (h * l * h⁻¹) * h := by rw [h1]
        _ = h * l := by group
    rw [hC] at hcent
    exact hcent
  have : Finite (MulAut L) := Finite.of_injective (fun f : MulAut L => (f : L → L))
    (fun f g hfg => MulEquiv.ext (fun x => congrFun hfg x))
  have h1 : Nat.card H ∣ Nat.card (MulAut L) := Subgroup.card_dvd_of_injective _ hinj
  have h2 : Nat.card H ∣ 2 * Nat.card L := h1.trans hA
  have h3 : Nat.card L * L.index = Nat.card H := by
    rw [mul_comm]; exact (Subgroup.index_mul_card L)
  have h4 : L.index ∣ 2 := by
    have h2' : Nat.card L * L.index ∣ Nat.card L * 2 := by
      rw [h3, mul_comm (Nat.card L) 2]; exact h2
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h2'
  have h5 : L.index = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h | h
    · exact h
    · rw [h] at hodd; exact absurd hodd (by decide)
  exact Subgroup.index_eq_one.mp h5

end CFSG.GH74.Uniqueness.SU.K.KI8
