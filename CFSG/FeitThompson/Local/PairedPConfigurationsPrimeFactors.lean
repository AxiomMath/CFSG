module

public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.PConfigurationKappaFactors
import CFSG.FeitThompson.Representations.TypeVMaximalExclusion

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] [Finite G] {M E W₁ W₂ : Subgroup G}

theorem isTypeII_or_isTypeIII_or_isTypeIV_of_existsUnique_localTypes
    (huniq : ∃! i : Fin 5, CFSG.FeitThompson.localTypes M i)
    (hI : ¬ IsTypeI M) (hV : ¬ IsTypeV M) :
    IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M := by
  obtain ⟨i, hi, -⟩ := huniq
  fin_cases i
  · exact absurd hi hI
  · exact Or.inl hi
  · exact Or.inr (Or.inl hi)
  · exact Or.inr (Or.inr hi)
  · exact absurd hi hV

theorem prime_natCard_W₁_of_isTypeIIToIV (hsolv : Group.IsSolvable ↥M)
    (htype : IsTypeII M ∨ IsTypeIII M ∨ IsTypeIV M)
    (hc : IsWitnessedPConfiguration M E W₁ W₂) : (Nat.card W₁).Prime := by
  rcases htype with h | h | h
  · exact (h.clauses_of_isWitnessedPConfiguration hsolv hc).1.prime_natCard_W₁
  · exact (h.clauses_of_isWitnessedPConfiguration hsolv hc).1.prime_natCard_W₁
  · exact (h.clauses_of_isWitnessedPConfiguration hsolv hc).1.prime_natCard_W₁

theorem natCard_W₂_ne_natCard_W₁ (hc : IsWitnessedPConfiguration M E W₁ W₂)
    (hp : (Nat.card W₁).Prime) : Nat.card W₂ ≠ Nat.card W₁ := fun h =>
  hp.ne_one (Nat.Coprime.eq_one_of_dvd hc.coprime_natCard_W₁_natCard_commutator
    (h ▸ Subgroup.card_dvd_of_le (hc.le_hallCore_W₂.trans hc.hallCore_le_commutator)))

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

open CFSG.FeitThompson

universe u

theorem FNI_paired_p_configurations_prime_factors
    (h₁ : Statements.FBG_five_type_local_classification.{u})
    (h₂ : Statements.FNI_kappa_local_pair.{u})
    (h₃ : Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₄ : Statements.FPF_type_iii_v_extended_dade_support.{u})
    (h₅ : Statements.FPF_type_iii_v_induced_family_noncoherence.{u})
    (h₆ : Statements.FPF_type_iii_v_second_factor_prime.{u})
    (h₇ : Statements.FTS_type_I_core_kappa_identity.{u}) :
    Statements.FNI_paired_p_configurations_prime_factors.{u} := by
  intro G _ _ hG S T U V W₁ W₂ hS hT _hST hcS hcT
  have : Fintype G := Fintype.ofFinite G
  have hFBG : CFSG.FeitThompson.IsFBGAmbient G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG6 : Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hG9 : CFSG.FeitThompson.Prep09.IsMinimalSimpleOddOrder G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hnotV := FPF_type_v_exclusion h₄ h₅ h₆ G hG6
  have hκS := (FNI_p_configuration_kappa_factors h₂ h₃ G hG S U W₁ W₂ hS hcS).1
  have hκT := (FNI_p_configuration_kappa_factors h₂ h₃ G hG T V W₂ W₁ hT hcT).1
  have hnotI : ∀ M : Subgroup G, IsCoatom M → (kappaPrimes M).Nonempty → ¬ IsTypeI M :=
    fun M hM hκ hI => Set.nonempty_iff_ne_empty.1 hκ (h₇ G hG9 M hM hI).1
  have htS := isTypeII_or_isTypeIII_or_isTypeIV_of_existsUnique_localTypes ((h₁ G hFBG).1 S hS)
    (hnotI S hS hκS) (hnotV S hS)
  have htT := isTypeII_or_isTypeIII_or_isTypeIV_of_existsUnique_localTypes ((h₁ G hFBG).1 T hT)
    (hnotI T hT hκT) (hnotV T hT)
  have hq : (Nat.card W₁).Prime :=
    prime_natCard_W₁_of_isTypeIIToIV (hG.isSolvable_of_ne_top S hS.1) htS hcS
  have hp : (Nat.card W₂).Prime :=
    prime_natCard_W₁_of_isTypeIIToIV (hG.isSolvable_of_ne_top T hT.1) htT hcT
  exact ⟨hp, hq, odd_natCard_subgroup hG.odd_natCard W₂, odd_natCard_subgroup hG.odd_natCard W₁,
    natCard_W₂_ne_natCard_W₁ hcS hq⟩

end CFSG.FeitThompson.Proofs

end
