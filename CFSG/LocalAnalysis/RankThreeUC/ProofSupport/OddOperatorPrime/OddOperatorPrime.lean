module


public import CFSG.LocalAnalysis.RankThreeUC.FaithfulPrimeFieldKGroupModule
public import CFSG.GroupTheory.CoprimeActionSupport.FixedFreeOrderTwoSubgroupCentral

public section

namespace CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOperatorPrime

theorem ne_two {G : Type} [Group G] [Finite G] {p : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ρ : Representation (ZMod p) G V}
    (hS : CFSG.LocalAnalysis.RankThreeUC.FaithfulPrimeFieldKGroupModule G p V ρ) {q r : ℕ} (hq : q.Prime) (hr : r.Prime)
    (hqp : q ≠ p) (hrp : r ≠ p) (hqr : q ≠ r)
    (D : Subgroup G) (hD : Nat.card D = r)
    (hCV : (⨅ d ∈ D, LinearMap.ker (ρ d - LinearMap.id)) = (⊥ : Submodule (ZMod p) V))
    (Q : Subgroup G) (hQD : ⁅D, Q⁆ = Q) (hQ1 : Q ≠ ⊥) (hQq : IsPGroup q Q) :
    r ≠ 2 := by
  intro hr2
  subst hr2
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    exact hrp ((Nat.prime_dvd_prime_iff_eq hS.prime hr).mp h').symm
  have hfix : Representation.invariants (ρ.comp D.subtype) = ⊥ := by
    rw [← hCV]
    ext v
    simp [Representation.mem_invariants, Submodule.mem_iInf, sub_eq_zero]
  have hc := CFSG.GroupTheory.CoprimeActionSupport.FixedFreeOrderTwoSubgroupCentral.le_center h2 ρ hS.faithful
    D hD hfix
  have hbot : ⁅D, Q⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hc.trans (Subgroup.center_le_centralizer _)
  exact hQ1 (hQD ▸ hbot)

end CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOperatorPrime
