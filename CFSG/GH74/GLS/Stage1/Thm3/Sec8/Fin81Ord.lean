module

public import CFSG.GH74.GLS.Stage2.Final.ModelDisjoint
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ref

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81

open CFSG.GH74.GLS.Stage2.Final.ModelArith

theorem v2_two_pow_mul_odd {m r : ℕ} (hr : Odd r) : (2 ^ m * r).factorization 2 = m := by
  rw [Nat.factorization_mul (by positivity) hr.pos.ne', Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr h))]
  simp

theorem v2_ordA3 {q : ℕ} (hq : q % 8 = 5) : (CFSG.Open.ordA 3 q).factorization 2 = 7 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 5 := ⟨q / 8, by omega⟩
  have hg : Nat.gcd 4 (8 * k + 5 - 1) = 4 := Nat.gcd_eq_left ⟨2 * k + 1, by omega⟩
  have h := gcd_mul_ordA_three (q := 8 * k + 5)
  rw [hg] at h
  have e2 : (8 * k + 5) ^ 2 - 1 = 2 ^ 3 * (8 * k ^ 2 + 10 * k + 3) := by
    have : (8 * k + 5) ^ 2 = 2 ^ 3 * (8 * k ^ 2 + 10 * k + 3) + 1 := by ring
    omega
  have e3 : (8 * k + 5) ^ 3 - 1 = 2 ^ 2 * (128 * k ^ 3 + 240 * k ^ 2 + 150 * k + 31) := by
    have : (8 * k + 5) ^ 3 = 2 ^ 2 * (128 * k ^ 3 + 240 * k ^ 2 + 150 * k + 31) + 1 := by ring
    omega
  have e4 : (8 * k + 5) ^ 4 - 1 =
      2 ^ 4 * ((8 * k ^ 2 + 10 * k + 3) * (32 * k ^ 2 + 40 * k + 13)) := by
    have : (8 * k + 5) ^ 4 =
        2 ^ 4 * ((8 * k ^ 2 + 10 * k + 3) * (32 * k ^ 2 + 40 * k + 13)) + 1 := by ring
    omega
  have ha : Odd (8 * k ^ 2 + 10 * k + 3) := ⟨4 * k ^ 2 + 5 * k + 1, by ring⟩
  have hb : Odd (128 * k ^ 3 + 240 * k ^ 2 + 150 * k + 31) :=
    ⟨64 * k ^ 3 + 120 * k ^ 2 + 75 * k + 15, by ring⟩
  have hc : Odd (32 * k ^ 2 + 40 * k + 13) := ⟨16 * k ^ 2 + 20 * k + 6, by ring⟩
  have hq : Odd ((8 * k + 5) ^ 6) := Odd.pow ⟨4 * k + 2, by ring⟩
  have key : CFSG.Open.ordA 3 (8 * k + 5) = 2 ^ 7 *
      ((8 * k + 5) ^ 6 * (8 * k ^ 2 + 10 * k + 3) *
        (128 * k ^ 3 + 240 * k ^ 2 + 150 * k + 31) *
        ((8 * k ^ 2 + 10 * k + 3) * (32 * k ^ 2 + 40 * k + 13))) := by
    have h4 : 4 * CFSG.Open.ordA 3 (8 * k + 5) = 4 * (2 ^ 7 *
      ((8 * k + 5) ^ 6 * (8 * k ^ 2 + 10 * k + 3) *
        (128 * k ^ 3 + 240 * k ^ 2 + 150 * k + 31) *
        ((8 * k ^ 2 + 10 * k + 3) * (32 * k ^ 2 + 40 * k + 13)))) := by
      rw [h, e2, e3, e4]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
  rw [key]
  exact v2_two_pow_mul_odd (((hq.mul ha).mul hb).mul (ha.mul hc))

theorem v2_ordTwistedA3 {q : ℕ} (hq : q % 8 = 3) :
    (CFSG.Open.ordTwistedA 3 q).factorization 2 = 7 := by
  obtain ⟨k, rfl⟩ : ∃ k, q = 8 * k + 3 := ⟨q / 8, by omega⟩
  have hg : Nat.gcd 4 (8 * k + 3 + 1) = 4 := Nat.gcd_eq_left ⟨2 * k + 1, by omega⟩
  have h := gcd_mul_ordTwistedA_three (q := 8 * k + 3)
  rw [hg] at h
  have e2 : (8 * k + 3) ^ 2 - 1 = 2 ^ 3 * (8 * k ^ 2 + 6 * k + 1) := by
    have : (8 * k + 3) ^ 2 = 2 ^ 3 * (8 * k ^ 2 + 6 * k + 1) + 1 := by ring
    omega
  have e3 : (8 * k + 3) ^ 3 + 1 = 2 ^ 2 * (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7) := by
    ring
  have e4 : (8 * k + 3) ^ 4 - 1 =
      2 ^ 4 * ((8 * k ^ 2 + 6 * k + 1) * (32 * k ^ 2 + 24 * k + 5)) := by
    have : (8 * k + 3) ^ 4 =
        2 ^ 4 * ((8 * k ^ 2 + 6 * k + 1) * (32 * k ^ 2 + 24 * k + 5)) + 1 := by ring
    omega
  have ha : Odd (8 * k ^ 2 + 6 * k + 1) := ⟨4 * k ^ 2 + 3 * k, by ring⟩
  have hb : Odd (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7) :=
    ⟨64 * k ^ 3 + 72 * k ^ 2 + 27 * k + 3, by ring⟩
  have hc : Odd (32 * k ^ 2 + 24 * k + 5) := ⟨16 * k ^ 2 + 12 * k + 2, by ring⟩
  have hq : Odd ((8 * k + 3) ^ 6) := Odd.pow ⟨4 * k + 1, by ring⟩
  have key : CFSG.Open.ordTwistedA 3 (8 * k + 3) = 2 ^ 7 *
      ((8 * k + 3) ^ 6 * (8 * k ^ 2 + 6 * k + 1) *
        (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7) *
        ((8 * k ^ 2 + 6 * k + 1) * (32 * k ^ 2 + 24 * k + 5))) := by
    have h4 : 4 * CFSG.Open.ordTwistedA 3 (8 * k + 3) = 4 * (2 ^ 7 *
      ((8 * k + 3) ^ 6 * (8 * k ^ 2 + 6 * k + 1) *
        (128 * k ^ 3 + 144 * k ^ 2 + 54 * k + 7) *
        ((8 * k ^ 2 + 6 * k + 1) * (32 * k ^ 2 + 24 * k + 5)))) := by
      rw [h, e2, e3, e4]; ring
    exact Nat.eq_of_mul_eq_mul_left (by norm_num) h4
  rw [key]
  exact v2_two_pow_mul_odd (((hq.mul ha).mul hb).mul (ha.mul hc))

theorem v2_card_model_psl {Gs : Type} [Group Gs] {p f : ℕ} (_hp : p.Prime)
    (hq8 : p ^ f % 8 = 5) (hL : CFSG.Blueprint.LieModel Gs .PSL 4 p f) :
    (Nat.card Gs).factorization 2 = 7 := by
  obtain ⟨-, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psl_unpack hL
  rw [Nat.card_congr e.toEquiv, card_psl4, hF]
  exact v2_ordA3 hq8

theorem v2_card_model_psu {Gs : Type} [Group Gs] {p f : ℕ} (hp : p.Prime)
    (hq8 : p ^ f % 8 = 3) (hL : CFSG.Blueprint.LieModel Gs .PSU 4 p f) :
    (Nat.card Gs).factorization 2 = 7 := by
  obtain ⟨hf, F, iF, fF, hF, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psu_unpack hL
  rw [Nat.card_congr e.toEquiv, card_psu4 hp hf hF]
  exact v2_ordTwistedA3 hq8

theorem exists_sylow_M128_of_embedding {Gs : Type} [Group Gs] [Finite Gs] (Φ : M128 →* Gs)
    (hΦ : Function.Injective Φ) (hv : (Nat.card Gs).factorization 2 = 7) :
    ∃ S' : Sylow 2 Gs, Nonempty (M128 ≃* ↥(S' : Subgroup Gs)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card Φ.range = 2 ^ 7 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΦ).toEquiv, card_M128]; norm_num
  have hT : IsPGroup 2 Φ.range := IsPGroup.of_card hcard
  obtain ⟨P, hP⟩ := hT.exists_le_sylow
  have hPcard : Nat.card P = 2 ^ 7 := by rw [Sylow.card_eq_multiplicity, hv]
  have hEq : Φ.range = (P : Subgroup Gs) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, hcard])
  exact ⟨P, ⟨(MonoidHom.ofInjective hΦ).trans (MulEquiv.subgroupCongr hEq)⟩⟩

end CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81
