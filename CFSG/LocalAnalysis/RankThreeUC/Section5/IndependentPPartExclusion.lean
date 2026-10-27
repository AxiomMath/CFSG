module

public import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PPartAnnihilation.PPartAnnihilation
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CharacteristicPrimeSubgroup
public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.IndependentPPartExclusion

variable {G : Type} [Group G] [Finite G]

theorem p_part_impossible {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (h : ExtraspecialBinaryActionCounterexample G p P T B e ρ) (hp : p ∈ piOf B) : False := by
  obtain ⟨A, hAB, hcard, hchar⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.Section5.CharacteristicPrimeSubgroup.exists_characteristic h hp
  have hpp : p.Prime := hp.1
  have hA : A ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcard
    exact hpp.one_lt.ne hcard
  have h1 := (characteristic_actor_fixes_commutator_fixedSpace_and_centralizes_odd_invariants h.oddPrimeClassTwoAction h.faithfulBinaryIrreducibleAction A hAB hchar).2.2 hA
  exact h1 (CFSG.LocalAnalysis.RankThreeUC.ProofSupport.PPartAnnihilation.actual_pPart_annihilation h hAB hcard)

end CFSG.LocalAnalysis.RankThreeUC.Section5.IndependentPPartExclusion
