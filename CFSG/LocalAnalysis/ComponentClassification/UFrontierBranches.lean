module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueUFailureSimple
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSectionalFour
public import CFSG.LocalAnalysis.ComponentClassification.KProperRelativeBShell

public section

namespace CFSG.ComponentClassification.UFrontier

open CFSG.Assembly CFSG.Blueprint Subgroup
open CFSG.ComponentClassification.UnbalancedLayer (GSUnbalancingTriple)

@[expose] def TripleBranch : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    KProper Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    (∃ (a x : X) (J : Subgroup X), GSUnbalancingTriple a x J) → OutcomeLocal.UOutcome X

@[expose] def ProperCoreBranch : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    KProper Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    ∀ S : Sylow 2 X,
      (⨆ (Q : Subgroup X) (_ : Q ≤ (S : Subgroup X)) (_ : 2 ≤ CFSG.pRank 2 ↥Q),
        normalizer (Q : Set X)) < ⊤ →
      OutcomeLocal.UOutcome X

@[expose] def SectionalFourBranch : Prop :=
  ∀ (X : Type) [Group X] [Finite X] [IsSimpleGroup X], (∃ a b : X, a * b ≠ b * a) →
    KProper Catalog X →
    (∃ z : X, orderOf z = 2 ∧ CFSG.oddCore (centralizer ({z} : Set X)) ≠ ⊥) →
    (∀ P : Subgroup X, IsPGroup 2 P →
      ∃ Y : Finset X, Y.card ≤ 4 ∧ closure (Y : Set X) = P) →
    (∀ (H : Subgroup X) (R : Subgroup ↥H) [R.Normal],
      Open.IsElemAbelian 2 (⊤ : Subgroup (↥H ⧸ R)) → Nat.card (↥H ⧸ R) ≤ 16) →
    OutcomeLocal.UOutcome X

theorem commutator_eq_top_of_simple {X : Type} [Group X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) : commutator X = ⊤ := by
  obtain ⟨a, b, hab⟩ := hnonab
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X)).resolve_left fun h => hab ?_
  have hmem : a * b * a⁻¹ * b⁻¹ ∈ commutator X :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [h, Subgroup.mem_bot] at hmem
  calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
    _ = b * a := by rw [hmem, one_mul]

theorem pPrimeCore_two_eq_bot_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {z : X} (hz : orderOf z = 2) : CFSG.pPrimeCore 2 X = ⊥ := by
  refine CFSG.pPrimeCore_eq_bot_iff.mpr fun K hK hcop => ?_
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal K).resolve_right fun htop => ?_
  have hdvd : 2 ∣ Nat.card K := by
    rw [htop, Subgroup.card_top, ← hz]
    exact orderOf_dvd_natCard z
  exact absurd (Nat.Coprime.eq_one_of_dvd hcop hdvd) (by norm_num)

theorem oddCore_eq_pPrimeCore_two' (G : Type*) [Group G] :
    CFSG.oddCore G = CFSG.pPrimeCore 2 G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.oddCore_eq_piCore G).trans (CFSG.pPrimeCore_eq_piCore G 2).symm

theorem relativeU_of_branches (hCU : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome)
    (htriple : TripleBranch) (hcore : ProperCoreBranch) (hfour : SectionalFourBranch) :
    KProperRelativeB.RelativeU Catalog := by
  intro X _ _ hK hsimple hnonab hz
  by_contra hfail
  obtain ⟨-, hXs, hXnab⟩ :=
    CatalogueU.kProper_unbalanced_U_failure_is_simple_of_catalogU hCU hK hsimple hnonab hz hfail
  obtain ⟨z, hz2, hzc⟩ := hz
  have hperf : commutator X = ⊤ := commutator_eq_top_of_simple hXnab
  have hunb : ∃ t : X, orderOf t = 2 ∧
      ¬ (CFSG.pPrimeCore 2 (centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype ≤
        CFSG.pPrimeCore 2 X := by
    refine ⟨z, hz2, fun hle => hzc ?_⟩
    rw [pPrimeCore_two_eq_bot_of_simple hz2, le_bot_iff,
      map_eq_bot_iff_of_injective _ (centralizer ({z} : Set X)).subtype_injective] at hle
    rw [oddCore_eq_pPrimeCore_two', hle]
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 X))
  rcases UnbalancedCorr.perfect_unbalanced_triple_core_or_sectional_four hperf S hunb rfl with
    ⟨a, x, J, -, -, -, h⟩ | h | ⟨h4, h16⟩
  · exact hfail (htriple X hXnab hK ⟨z, hz2, hzc⟩ ⟨a, x, J, h⟩)
  · exact hfail (hcore X hXnab hK ⟨z, hz2, hzc⟩ S h)
  · exact hfail (hfour X hXnab hK ⟨z, hz2, hzc⟩ h4 h16)

end CFSG.ComponentClassification.UFrontier
