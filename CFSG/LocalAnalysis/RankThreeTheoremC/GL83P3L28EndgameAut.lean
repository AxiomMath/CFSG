module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Model

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup
open CFSG.Quasithin.F6.L28Res (G8)

private def noComm (g : G8) : Prop :=
  ∀ t : G8, t * t = 1 → t ≠ 1 → (g * t * g⁻¹) * t ≠ t * (g * t * g⁻¹)

private instance (g : G8) : Decidable (noComm g) := by
  unfold noComm
  infer_instance

private theorem l28_g8_noComm : ∀ g : G8, g ^ 3 = 1 → g ≠ 1 → noComm g := by
  decide +kernel

theorem l28_noComm {K : Type} [Group K] (hK : IsRankThreeL28 K) {g t : K} (hg3 : g ^ 3 = 1)
    (hg1 : g ≠ 1) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    (g * t * g⁻¹) * t ≠ t * (g * t * g⁻¹) := by
  obtain ⟨e⟩ := l28m_equiv hK
  have h := l28_g8_noComm (e g) (by rw [← map_pow, hg3, map_one])
    (fun h => hg1 (e.injective (by rw [h, map_one]))) (e t)
    (by rw [← map_mul, ht2, map_one]) (fun h => ht1 (e.injective (by rw [h, map_one])))
  intro hcomm
  exact h (by simpa only [map_mul, map_inv] using congrArg e hcomm)

theorem l28_no_invariant_two_group {Y : Type} [Group Y] [Finite Y] {K : Subgroup Y} [K.Normal]
    (hK : IsRankThreeL28 K) (hC : centralizer (K : Set Y) = ⊥) {g : Y} (hgK : g ∈ K)
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) {R : Subgroup Y} (hR : IsPGroup 2 R)
    (hgR : g ∈ normalizer (R : Set Y)) : R = ⊥ := by
  by_contra hne
  have hinj : Function.Injective (MulAut.conjNormal : Y →* MulAut K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    have : y ∈ centralizer (K : Set Y) := by
      rw [mem_centralizer_iff]
      intro h hh
      have := congrArg (fun φ : MulAut K => ((φ ⟨h, hh⟩ : K) : Y)) (MonoidHom.mem_ker.mp hy)
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at this
      calc h * y = (y * h * y⁻¹) * y := by rw [this]
        _ = y * h := by group
    rwa [hC, Subgroup.mem_bot] at this
  have hYd : Nat.card Y ∣ 1512 :=
    (Subgroup.card_dvd_of_injective _ hinj).trans (l28m_card_mulAut hK).dvd
  have hK504 : Nat.card K = 504 := l28m_card hK
  have hidx : K.index ∣ 3 := by
    have h1 := K.index_mul_card
    rw [hK504] at h1
    have : K.index * 504 ∣ 3 * 504 := by
      rw [h1]
      simpa using hYd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
  have hRK : R ≤ K := by
    intro r hr
    obtain ⟨m, hm⟩ := hR ⟨r, hr⟩
    have hrm : r ^ 2 ^ m = 1 := congrArg Subtype.val hm
    let q : Y ⧸ K := QuotientGroup.mk r
    have h1 : q ^ 2 ^ m = 1 := by
      change QuotientGroup.mk r ^ 2 ^ m = 1
      rw [← QuotientGroup.mk_pow, hrm, QuotientGroup.mk_one]
    have h2 : q ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Y ⧸ K) (x := q)
      rw [← Subgroup.index_eq_card] at h
      obtain ⟨c, hc⟩ := hidx
      rw [hc, pow_mul, h, one_pow]
    have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    have hcop : Nat.Coprime (2 ^ m) 3 := Nat.Coprime.pow_left m (by norm_num)
    rw [hcop, pow_one] at h3
    exact (QuotientGroup.eq_one_iff r).mp h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hne
  have hcen : Nontrivial (center R) := hR.center_nontrivial
  have hcR : IsPGroup 2 (center R) := hR.to_subgroup _
  obtain ⟨n, hn⟩ := hcR.exists_card_eq
  have h2dvd : 2 ∣ Nat.card (center R) := by
    have hn0 : n ≠ 0 := by
      rintro rfl
      have hbot : center R = ⊥ := by simpa using hn
      exact (Subgroup.nontrivial_iff_ne_bot (center R)).mp hcen hbot
    rw [hn]
    exact dvd_pow_self 2 hn0
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := center R) 2 h2dvd
  have hcord : orderOf ((c : R) : Y) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    exact hc
  set t : Y := ((c : R) : Y) with ht
  have htR : t ∈ R := (c : R).2
  have ht2 : t * t = 1 := by
    rw [← sq]
    exact hcord ▸ pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hcord
    omega
  have htc : ∀ r ∈ R, r * t = t * r := fun r hr =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp c.2 ⟨r, hr⟩)
  have hgt : g * t * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hgR t).mp htR
  have hcomm : (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := htc _ hgt
  have hg3' : (⟨g, hgK⟩ : K) ^ 3 = 1 := Subtype.ext (by simpa using hg3)
  have hg1' : (⟨g, hgK⟩ : K) ≠ 1 := fun h => hg1 (congrArg Subtype.val h)
  have ht2' : (⟨t, hRK htR⟩ : K) * ⟨t, hRK htR⟩ = 1 := Subtype.ext (by simpa using ht2)
  have ht1' : (⟨t, hRK htR⟩ : K) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  exact l28_noComm hK hg3' hg1' ht2' ht1' (Subtype.ext hcomm)

end CFSG.LocalAnalysis.RankThreeTheoremC
