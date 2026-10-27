module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Solvable
public import CFSG.FeitThompson.Definitions.RawNormalPrimeSetCore
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Local.PiCoreQuotientPiCore
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.PCoreSelfCentralizingNoNormalComplement

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open QuotientGroup Subgroup

variable {X : Type*} [Group X] [Finite X] {p : ℕ} {P K : Subgroup X}

omit [Finite X] in
theorem map_le_normalizer_map_of_le_normalizer {Y : Type*} [Group Y] (f : X →* Y)
    (hPK : P ≤ normalizer (K : Set X)) :
    P.map f ≤ normalizer ((K.map f : Subgroup Y) : Set Y) := by
  refine le_normalizer_iff_commutator_le_right.2 ?_
  rw [← Subgroup.map_commutator]
  exact Subgroup.map_mono (le_normalizer_iff_commutator_le_right.1 hPK)

theorem eq_bot_of_coprime_of_le_normalizer_of_pComplCore_eq_bot [Group.IsSolvable X]
    (hp : p.Prime) (hX : pComplCore p X = ⊥) (hK : p.Coprime (Nat.card K))
    (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hPK : P ≤ normalizer (K : Set X)) : K = ⊥ := by
  have := Fact.mk hp
  have hRnormal : (pCore p X).Normal := pCore_normal p X
  have hRp : IsPGroup p (pCore p X) := isPGroup_pCore hp X
  have hcent : centralizer ((pCore p X : Subgroup X) : Set X) ≤ pCore p X :=
    centralizer_pCore_le_pCore hp hX
  have hRP : pCore p X ≤ P := by
    have : pCore p X ≤ (Sylow.ofCard P hP : Subgroup X) := hRp.le_sylow_of_normal _
    simpa using this
  have hdisj : pCore p X ⊓ K = ⊥ := by
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    exact disjoint_iff.1
      (Subgroup.disjoint_of_coprime_natCard (by rw [hn]; exact hK.pow_left n))
  have hcommbot : ⁅K, pCore p X⁆ = ⊥ := by
    have h1 : ⁅pCore p X, K⁆ ≤ K :=
      (Subgroup.commutator_mono hRP le_rfl).trans (le_normalizer_iff_commutator_le_right.1 hPK)
    have h2 : ⁅pCore p X, K⁆ ≤ pCore p X := Subgroup.commutator_le_left _ K
    rw [commutator_comm, ← le_bot_iff, ← hdisj]
    exact le_inf h2 h1
  rw [← le_bot_iff, ← hdisj]
  exact le_inf ((commutator_eq_bot_iff_le_centralizer.1 hcommbot).trans hcent) le_rfl

theorem le_pComplCore_of_coprime_of_le_normalizer [Group.IsSolvable X] (hp : p.Prime)
    (hK : p.Coprime (Nat.card K)) (hP : Nat.card P = p ^ (Nat.card X).factorization p)
    (hPK : P ≤ normalizer (K : Set X)) : K ≤ pComplCore p X := by
  have hNcop : p.Coprime (Nat.card (pComplCore p X)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_natCard_pComplCore hp X)
  have hPbar : Nat.card (P.map (mk' (pComplCore p X)))
      = p ^ (Nat.card (X ⧸ pComplCore p X)).factorization p := by
    rw [← map_sup_mk'_eq_map_mk' P (pComplCore p X)]
    exact natCard_map_sup_mk'_eq_pow_factorization hp hNcop hP
  have hKbar : K.map (mk' (pComplCore p X)) = ⊥ :=
    eq_bot_of_coprime_of_le_normalizer_of_pComplCore_eq_bot hp
      (pComplCore_quotient_pComplCore p X)
      (Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd K _) hK) hPbar
      (map_le_normalizer_map_of_le_normalizer _ hPK)
  rwa [Subgroup.map_eq_bot_iff, ker_mk'] at hKbar

theorem le_pComplCore_sylow [Group.IsSolvable X] [Fact p.Prime] (P : Sylow p X)
    (hK : p.Coprime (Nat.card K)) (hPK : (P : Subgroup X) ≤ normalizer (K : Set X)) :
    K ≤ pComplCore p X :=
  le_pComplCore_of_coprime_of_le_normalizer Fact.out hK P.card_eq_multiplicity hPK

end

end CFSG.FeitThompson
