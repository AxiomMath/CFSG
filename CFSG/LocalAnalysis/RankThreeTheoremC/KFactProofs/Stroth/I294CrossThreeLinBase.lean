module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeProj

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

namespace LinThree

open CFSG.Open

theorem pow_eq_one_of_mem_statedScalars_subgroupOf {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {H : Subgroup (GL ι K)} {N : ℕ}
    (hN : ∀ c : Kˣ, Matrix.GeneralLinearGroup.scalar ι c ∈ H → c ^ N = 1) :
    ∀ z ∈ (StatedScalars ι K).subgroupOf H, z ^ N = 1 := by
  intro z hz
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  have hcH : Matrix.GeneralLinearGroup.scalar ι c ∈ H := hc ▸ z.2
  apply Subtype.ext
  show ((z : GL ι K)) ^ N = 1
  rw [← hc, ← map_pow, hN c hcH, map_one]

theorem le_pRank_centralizer_statedProj_of_coprime {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] [Finite K] {H : Subgroup (GL ι K)} {A : Type*} [Group A] {k N : ℕ}
    (hN : Nat.Coprime 3 N) (hZ : ∀ z ∈ (StatedScalars ι K).subgroupOf H, z ^ N = 1)
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ 3 = 1) (hA : Nat.card A = 3 ^ k)
    (φ : A →* GL ι K) (hφ : Function.Injective φ) (hH : ∀ a, φ a ∈ H) (g : H)
    (hg : ∀ a, (g : GL ι K) * φ a = φ a * (g : GL ι K)) :
    k ≤ pRank 3 (Subgroup.centralizer
      ({(QuotientGroup.mk g : StatedProj H)} : Set (StatedProj H))) := by
  refine le_pRank_centralizer_statedProj hcomm hpow hA φ hφ hH ?_ g hg
  intro a ha
  have hz : (⟨φ a, hH a⟩ : H) ∈ (StatedScalars ι K).subgroupOf H := ha
  have h1 : (⟨φ a, hH a⟩ : H) ^ N = 1 := hZ _ hz
  have h2 : (⟨φ a, hH a⟩ : H) ^ 3 = 1 :=
    Subtype.ext (by
      show (φ a) ^ 3 = 1
      rw [← map_pow, hpow a, map_one])
  have h3 : (⟨φ a, hH a⟩ : H) = 1 := by
    have hd : orderOf (⟨φ a, hH a⟩ : H) ∣ 1 := by
      have := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h1)
      rwa [hN] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  exact hφ (by simpa using congrArg Subtype.val h3)

end LinThree

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
