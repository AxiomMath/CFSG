module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructNonab
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowXUnStructAb

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem abelian_exp_three_of_card [Finite K] (hK : Nat.card K = 4) [FiniteDimensional K V]
    {N : ℕ} (hN : Module.finrank K V = N) (hN9 : 9 ≤ N) {Q : Subgroup (V ≃ₗ[K] V)}
    (hQ : IsGoodIn (scalars K V) Q) (hcard : 3 ^ (N - 2) ≤ Nat.card Q) :
    (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) ∧ ∀ x ∈ Q, x ^ 3 = 1 := by
  classical
  haveI : Finite (V ≃ₗ[K] V) := finite_linearEquiv
  have hZ := scalarLike_scalars (V := V) hK
  by_cases hab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x
  · refine ⟨hab, ?_⟩
    by_contra hne
    push Not at hne
    obtain ⟨x, hx, hx3⟩ := hne
    have := finrank_le_six_of_abelian hK hQ hab hx hx3 (hN ▸ hcard)
    omega
  · exfalso
    obtain ⟨g, hg, h, hh, hg3, hgh⟩ := exists_pow_three_eq_one_noncomm hZ hQ hab
    obtain ⟨n, hn3, hcardn⟩ := card_le_of_nonab hK hQ hg hh hg3 hgh
    have h1 : 3 ^ (N - 2) ≤ 3 ^ (2 + (n + n / 2)) := hcard.trans hcardn
    have h2 : N - 2 ≤ 2 + (n + n / 2) := (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
    omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie.RowXUn.Struct

end
