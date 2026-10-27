module

public import CFSG.Timmesfeld.Orders.Bang
public import Mathlib.Data.Int.Star

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KFAE

open CFSG.Timmesfeld (IsPrimitivePrimeDivisor)

theorem exists_ppd_data {f₀ e : ℕ} (hf₀ : 1 ≤ f₀) (he : 2 ≤ e) (hexc : ¬ (f₀ = 1 ∧ e = 6)) :
    ∃ r m : ℕ, IsPrimitivePrimeDivisor r m ∧ 0 < m ∧ ∀ k : ℕ, m ∣ f₀ * k ↔ e ∣ k := by
  by_cases h6 : f₀ * e = 6
  · have hf3 : f₀ ≤ 3 := by nlinarith
    interval_cases f₀
    · exfalso
      exact hexc ⟨rfl, by omega⟩
    · have he3 : e = 3 := by omega
      subst he3
      refine ⟨7, 3, ⟨by norm_num, by norm_num, ?_⟩, by norm_num, fun k => by omega⟩
      intro j hj hj3
      interval_cases j <;> norm_num
    · have he2 : e = 2 := by omega
      subst he2
      refine ⟨3, 2, ⟨by norm_num, by norm_num, ?_⟩, by norm_num, fun k => by omega⟩
      intro j hj hj2
      interval_cases j
      norm_num
  · obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor
      (k := f₀ * e) (by nlinarith) h6
    exact ⟨r, f₀ * e, hr, by positivity, fun k => Nat.mul_dvd_mul_iff_left (by omega)⟩

theorem ppd_dvd_iff {r m f₀ e p : ℕ} (h : IsPrimitivePrimeDivisor r m) (hm : 0 < m)
    (hcorr : ∀ k : ℕ, m ∣ f₀ * k ↔ e ∣ k) (hp : p.Prime) (hpe : ¬ p ∣ e) (k : ℕ) :
    (r ∣ (2 ^ f₀) ^ k - 1 ↔ e ∣ k) ∧ (r ∣ (2 ^ (p * f₀)) ^ k - 1 ↔ e ∣ k) := by
  constructor
  · rw [← pow_mul, h.dvd_sub_one_iff hm, hcorr]
  · have e1 : (2 ^ (p * f₀)) ^ k = 2 ^ (f₀ * (p * k)) := by
      rw [← pow_mul]
      congr 1
      ring
    rw [e1, h.dvd_sub_one_iff hm, hcorr]
    have hcop : Nat.Coprime e p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpe).symm
    exact ⟨fun h' => hcop.dvd_of_dvd_mul_left h', fun h' => Dvd.dvd.mul_left h' p⟩

end KFAE

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
