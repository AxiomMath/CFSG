module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166TwA5Four7
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Cases

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.UnitaryPilot CFSG.SeitzReduction.LinearPilot
open CFSG.LocalAnalysis.GLTheoremA
open Matrix

theorem concl166S_twA5Four_of_transport
    (htr : ∀ {K R : Type} [Group K] [Finite K] [Group R] [Finite R], (K ≃* R) → ∀ {p : ℕ},
      (∃ (q : ℕ) (B' : Subgroup R) (x' : R) (J : Subgroup R), Concl166S R p q B' x' J) →
      ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J)
    {K : Type} [Group K] [Finite K] {lab : GLALabel} {p : ℕ}
    (hK : HasLabel K (fun l : GLALabel => l = lab))
    (hfam : i166FamTwA5 lab p (Subgroup.center K = ⊥))
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 4 ≤ evenRank K)
    (hr : GLATwoLocalRank p K + 1 = evenRank K)
    (hn : lab.n = 2) :
    ∃ (q : ℕ) (B' : Subgroup K) (x' : K) (J : Subgroup K), Concl166S K p q B' x' J := by
  have hz : Subgroup.center K = ⊥ := by
    have hlab : lab = ⟨.twA, 5, 2⟩ := by
      obtain ⟨t, r, n⟩ := lab
      obtain ⟨ht, hrk, -, -⟩ := hfam
      simp_all
    exact center_eq_bot_of_hasLabel_twA5_two hlab hK
  obtain ⟨htag, hrank, -, hpdvd⟩ := hfam
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := by
      have h3 : 2 ^ lab.n - 1 = 3 := by rw [hn]; norm_num
      rwa [h3] at hpdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd
  subst hp3
  have hlab : lab = ⟨.twA, 5, 2⟩ := by
    obtain ⟨t, r, n⟩ := lab
    simp_all
  subst hlab
  obtain ⟨F, hFld, hFin, hF, ⟨e⟩⟩ :=
    exists_mulEquiv_unitarySU_of_hasLabel_twA5_two rfl hK hz
  letI : Field F := hFld
  letI : Finite F := hFin
  exact htr e (twA5FourModelAt_holds F hF)

end CFSG.LocalAnalysis.GLTheoremA.Y10F
