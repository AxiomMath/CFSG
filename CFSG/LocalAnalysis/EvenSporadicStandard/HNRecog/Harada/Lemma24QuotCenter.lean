module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup

private theorem odd_lcm {a b : ℕ} (ha : Odd a) (hb : Odd b) : Odd (Nat.lcm a b) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  have h2ab : 2 ∣ a * b := h2.trans (lcm_dvd_mul a b)
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2ab with h | h
  · exact Odd.not_two_dvd_nat ha h
  · exact Odd.not_two_dvd_nat hb h

theorem center_normal_eq_bot {Q : Type} [Group Q] [Finite Q]
    (hO : ∀ N : Subgroup Q, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hmax : ∀ R : Subgroup Q, IsPGroup 2 R → Nat.card R ≤ 64)
    {X F P : Subgroup Q} [X.Normal] (hFX : F ≤ X) (hPF : P ≤ F) (hP2 : IsPGroup 2 P)
    (hPcard : Nat.card P = 64) (hFz : ∀ f ∈ F, (∀ g ∈ F, f * g = g * f) → f = 1) :
    Subgroup.center ↥X = ⊥ := by
  let Z : Subgroup ↥X := Subgroup.center ↥X
  let Z' : Subgroup Q := Z.map X.subtype
  change Z = ⊥
  have hZchar : Z.Characteristic := Subgroup.centerCharacteristic
  have hZ'normal : Z'.Normal :=
    ConjAct.normal_of_characteristic_of_normal (H := X) (K := Z) (h := hZchar)
  have hZ'comm : ∀ a ∈ Z', ∀ b ∈ Z', a * b = b * a := by
    intro a ha b hb
    obtain ⟨xa, hxa, hax⟩ := Subgroup.mem_map.mp ha
    obtain ⟨xb, hxb, hbx⟩ := Subgroup.mem_map.mp hb
    have key : X.subtype (xa * xb) = X.subtype (xb * xa) :=
      congrArg X.subtype (Subgroup.mem_center_iff.mp hxa xb).symm
    rw [map_mul, map_mul] at key
    rw [← hax, ← hbx]
    exact key
  let Zodd : Subgroup Q :=
    { carrier := {z | z ∈ Z' ∧ Odd (orderOf z)}
      one_mem' := ⟨Z'.one_mem, by simp⟩
      mul_mem' := fun {a b} ha hb =>
        ⟨Z'.mul_mem ha.1 hb.1,
          Odd.of_dvd_nat (odd_lcm ha.2 hb.2)
            (Commute.orderOf_mul_dvd_lcm (show Commute a b from hZ'comm a ha.1 b hb.1))⟩
      inv_mem' := fun {a} ha => ⟨Z'.inv_mem ha.1, by simpa [orderOf_inv] using ha.2⟩ }
  have hZodd_normal : Zodd.Normal := by
    refine ⟨fun n hn g => ⟨hZ'normal.conj_mem n hn.1 g, ?_⟩⟩
    have hconj : orderOf (g * n * g⁻¹) = orderOf n := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hconj]
    exact hn.2
  have hZodd_odd : Odd (Nat.card Zodd) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have h2 : 2 ∣ Nat.card Zodd := even_iff_two_dvd.mp heven
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Zodd) 2 h2
    have hodd : Odd (orderOf (g : Q)) := g.2.2
    rw [Subgroup.orderOf_coe g, hg] at hodd
    exact absurd hodd (by decide)
  have hZodd_bot : Zodd = ⊥ := hO Zodd hZodd_normal hZodd_odd
  have hpow : ∀ z : Q, z ∈ Z' → ∃ k, orderOf z = 2 ^ k := by
    intro z hz
    obtain ⟨k, m, hm_odd, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos z).ne'
    have hmem : z ^ 2 ^ k ∈ Zodd := by
      refine ⟨Z'.pow_mem hz (2 ^ k), ?_⟩
      have hdvd : orderOf (z ^ 2 ^ k) ∣ m := by
        rw [orderOf_dvd_iff_pow_eq_one]
        calc (z ^ 2 ^ k) ^ m = z ^ (2 ^ k * m) := (pow_mul z (2 ^ k) m).symm
          _ = z ^ orderOf z := by rw [hkm]
          _ = 1 := pow_orderOf_eq_one z
      exact Odd.of_dvd_nat hm_odd hdvd
    have hzpow : z ^ 2 ^ k = 1 := by
      have : z ^ 2 ^ k ∈ (⊥ : Subgroup Q) := by rw [← hZodd_bot]; exact hmem
      simpa using this
    have hdvd : orderOf z ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hzpow
    have hm1 : m = 1 := by
      have hpos : 0 < 2 ^ k := pow_pos (by norm_num) k
      have hdvd' : 2 ^ k * m ∣ 2 ^ k := by rwa [hkm] at hdvd
      exact Nat.dvd_one.mp ((Nat.mul_dvd_mul_iff_left hpos).mp (by simpa using hdvd'))
    exact ⟨k, by rw [hkm, hm1, mul_one]⟩
  have hZ'2 : IsPGroup 2 Z' := by
    rw [isPGroup_iff_orderOf_dvd_pow]
    intro z
    obtain ⟨k, hk⟩ := hpow (z : Q) z.2
    exact ⟨k, by rw [← Subgroup.orderOf_coe z, hk]⟩
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  have hScard : Nat.card (S : Subgroup Q) ≤ 64 := hmax (S : Subgroup Q) S.isPGroup'
  have hSP : P = (S : Subgroup Q) := by
    refine Subgroup.eq_of_le_of_card_ge hPS ?_
    calc Nat.card (S : Subgroup Q) ≤ 64 := hScard
      _ = Nat.card P := hPcard.symm
  haveI : Z'.Normal := hZ'normal
  have hZ'leS : Z' ≤ (S : Subgroup Q) := IsPGroup.le_sylow_of_normal hZ'2 S
  have hZ'leF : Z' ≤ F := by
    have hZ'leP : Z' ≤ P := by rw [hSP]; exact hZ'leS
    exact hZ'leP.trans hPF
  have hZ'bot : Z' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp hz
    have hzF : z ∈ F := hZ'leF hz
    have hcomm : ∀ g ∈ F, z * g = g * z := by
      intro g hg
      have hxg := Subgroup.mem_center_iff.mp hx (⟨g, hFX hg⟩ : ↥X)
      rw [← hxz]
      simpa using (congrArg X.subtype hxg).symm
    simpa using hFz z hzF hcomm
  exact (Subgroup.map_eq_bot_iff_of_injective Z X.subtype_injective).mp hZ'bot

end CFSG.EvenSporadicStandard.HNRecog.Harada
