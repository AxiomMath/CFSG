module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36Rows

public section

namespace CFSG.ComponentClassification.HarrisLit.N36

open CFSG Subgroup GrSLit.L34Facts
open scoped commutatorElement

theorem fusionZStar_eq_center {Q : Type*} [Group Q] (hO : pPrimeCore 2 Q = ⊥) :
    Open.fusionZStar Q = center Q := by
  ext l
  rw [GSThmB.OddQuot.mem_fusionZStar_iff, hO, mem_center_iff]
  constructor
  · intro h m
    have h1 := h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  · intro h m
    rw [mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (h m).symm

namespace Config

variable {G : Type} [Group G] [Finite G] {p m : ℕ} {τ : MulAut G} {K : Subgroup G}

noncomputable def zStarEquiv (h : Config G p m τ K) :
    G ⧸ Open.fusionZStar G ≃* G ⧸ center G :=
  QuotientGroup.quotientMulEquivOfEq (fusionZStar_eq_center h.oddCore)

theorem isMType (h : Config G p m τ K) {t : Assembly.LowTwoRank.StatedLieTag} {n k : ℕ}
    (hL : Blueprint.LieModel (G ⧸ center G) t n p k)
    (hc : ∀ n k : ℕ,
      (Blueprint.LieModel (G ⧸ center G) .PSL (2 * n) p k →
        (Nat.card ↥(center G)).factorization 2 = (Nat.gcd (2 * n) (p ^ k - 1)).factorization 2) ∧
      (Blueprint.LieModel (G ⧸ center G) .PSU (2 * n) p k →
        (Nat.card ↥(center G)).factorization 2 = (Nat.gcd (2 * n) (p ^ k + 1)).factorization 2)) :
    IsMType p G := by
  have hZ : Open.fusionZStar G = center G := fusionZStar_eq_center h.oddCore
  have hcard : Nat.card ↥(Open.fusionZStar G) = Nat.card ↥(center G) := by rw [hZ]
  refine ⟨⟨h.perfect, ?_⟩, ⟨t, n, k, GSThmB.OddQuot.lieModel_of_equiv h.zStarEquiv.symm hL⟩,
    ?_, fun n k => ⟨fun hn => ?_, fun hn => ?_⟩⟩
  · exact LocalCores.isQuasisimple_of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq h.oddCore).trans QuotientGroup.quotientBot).symm
      h.quasisimple
  · rw [hcard]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h.center_isPGroup
    have hj0 : j ≠ 0 := by
      rintro rfl
      apply h.center_ne_bot
      rw [pow_zero] at hj
      exact Subgroup.eq_bot_of_card_eq _ hj
    rw [hj]
    exact (Nat.even_pow' hj0).mpr even_two
  · rw [hcard]
    exact (hc n k).1 (GSThmB.OddQuot.lieModel_of_equiv h.zStarEquiv hn)
  · rw [hcard]
    exact (hc n k).2 (GSThmB.OddQuot.lieModel_of_equiv h.zStarEquiv hn)

theorem exists_even_model (h : Config G p m τ K) {t : Assembly.LowTwoRank.StatedLieTag}
    {n k : ℕ} (hL : Blueprint.LieModel (G ⧸ center G) t n p k) :
    ∃ n k : ℕ,
      (Blueprint.LieModel (G ⧸ center G) .PSL (2 * n) p k ∧
        (Nat.card ↥(center G)).factorization 2 ≠ (Nat.gcd (2 * n) (p ^ k - 1)).factorization 2) ∨
      (Blueprint.LieModel (G ⧸ center G) .PSU (2 * n) p k ∧
        (Nat.card ↥(center G)).factorization 2 ≠
          (Nat.gcd (2 * n) (p ^ k + 1)).factorization 2) := by
  by_contra hne
  push Not at hne
  exact h.not_mType (h.isMType hL fun n k => ⟨(hne n k).1, (hne n k).2⟩)

end Config

end CFSG.ComponentClassification.HarrisLit.N36
