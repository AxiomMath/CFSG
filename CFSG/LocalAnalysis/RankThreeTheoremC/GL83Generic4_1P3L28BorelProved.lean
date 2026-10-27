module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Aut
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28Model
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L28ThreeProved
public import CFSG.LocalAnalysis.AGLEmbedding.Signalizer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

theorem l28BorelCore_proved : KFactL28BorelCore := by
  intro X _ _ K hKn hC hKL T hTK hTsyl
  have : K.Normal := hKn
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hTsyl
  have hTcard : Nat.card T = 3 ^ 2 := by
    rw [← hQ, Subgroup.card_map_of_injective K.subtype_injective]
    exact l28m_card_sylow hKL Q
  set N : Subgroup X := normalizer (T : Set X) with hN
  set R : Subgroup X := rankThreePrimeCore 3 N with hR
  have hRN : R ≤ N := CFSG.AGLEmbedding.glbPrimeCore_le 3 N
  have hRcop : Nat.Coprime 3 (Nat.card R) := CFSG.AGLEmbedding.glbPrimeCore_coprime 3 N
  have hNR : N ≤ normalizer (R : Set X) := CFSG.AGLEmbedding.le_normalizer_glbPrimeCore 3 N
  have hTN : T ≤ N := Subgroup.le_normalizer
  have hTR : T ⊓ R = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hTcard]
    exact Nat.Coprime.pow_left 2 hRcop
  refine eq_bot_iff.mpr fun r hr => ?_
  have hrN : r ∈ N := hRN hr
  have hcomm : ∀ t ∈ T, r * t = t * r := by
    intro t ht
    have h1 : r * t * r⁻¹ * t⁻¹ ∈ T :=
      T.mul_mem ((mem_normalizer_iff.mp hrN t).mp ht) (T.inv_mem ht)
    have h2 : r * t * r⁻¹ * t⁻¹ ∈ R := by
      have h3 : t * r⁻¹ * t⁻¹ ∈ R := by
        have := (mem_normalizer_iff.mp (hNR (hTN ht)) r⁻¹).mp (R.inv_mem hr)
        simpa [mul_assoc] using this
      have := R.mul_mem hr h3
      simpa [mul_assoc] using this
    have h4 : r * t * r⁻¹ * t⁻¹ ∈ T ⊓ R := ⟨h1, h2⟩
    rw [hTR, Subgroup.mem_bot] at h4
    calc r * t = (r * t * r⁻¹ * t⁻¹) * (t * r) := by group
      _ = t * r := by rw [h4, one_mul]
  have hfix : ∀ u ∈ (Q : Subgroup K), (MulAut.conjNormal r : MulAut K) u = u := by
    intro u hu
    have huT : (u : X) ∈ T := hQ ▸ ⟨u, hu, rfl⟩
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    calc r * (u : X) * r⁻¹ = ((u : X) * r) * r⁻¹ := by rw [hcomm _ huT]
      _ = u := by group
  have hrpow : r ^ Nat.card R = 1 := by
    have h := pow_card_eq_one' (G := R) (x := ⟨r, hr⟩)
    exact congrArg Subtype.val h
  have hψpow : (MulAut.conjNormal r : MulAut K) ^ Nat.card R = 1 := by
    rw [← map_pow, hrpow, map_one]
  obtain ⟨k, hk⟩ := l28m_exists_conj_of_pow_eq_one (G := K)
    (fun x hx => l28m_eq_one_of_central hKL hx)
    (by rw [l28m_card_mulAut hKL, l28m_card hKL]) hψpow hRcop.symm
  have hkQ : k ∈ (Q : Subgroup K) := by
    refine l28m_centralizer_sylow hKL Q ?_
    rw [mem_centralizer_iff]
    intro u hu
    have h1 := hfix u hu
    rw [← hk, MulAut.conj_apply] at h1
    calc u * k = (k * u * k⁻¹) * k := by rw [h1]
      _ = k * u := by group
  have hk9 : k ^ 9 = 1 := by
    have h := pow_card_eq_one' (G := (Q : Subgroup K)) (x := ⟨k, hkQ⟩)
    have h' := congrArg Subtype.val h
    rw [l28m_card_sylow hKL Q] at h'
    simpa using h'
  have hψ9 : (MulAut.conjNormal r : MulAut K) ^ 9 = 1 := by
    rw [← hk, ← map_pow, hk9, map_one]
  have hψ1 : (MulAut.conjNormal r : MulAut K) = 1 := by
    have h1 : orderOf (MulAut.conjNormal r : MulAut K) ∣ Nat.card R :=
      orderOf_dvd_of_pow_eq_one hψpow
    have h2 : orderOf (MulAut.conjNormal r : MulAut K) ∣ 9 := orderOf_dvd_of_pow_eq_one hψ9
    have h3 : Nat.Coprime (Nat.card R) 9 := by
      have := (Nat.Coprime.pow_left 2 hRcop).symm
      simpa using this
    have h4 : orderOf (MulAut.conjNormal r : MulAut K) ∣ 1 := by
      simpa [Nat.Coprime.gcd_eq_one h3] using Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h4)
  have hrK : r ∈ centralizer (K : Set X) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut K => ((φ ⟨x, hx⟩ : K) : X)) hψ1
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc x * r = (r * x * r⁻¹) * r := by rw [h1]
      _ = r * x := by group
  rw [hC, Subgroup.mem_bot] at hrK
  exact Subgroup.mem_bot.mpr hrK

end CFSG.LocalAnalysis.RankThreeTheoremC
