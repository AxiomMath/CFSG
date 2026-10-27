module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.KappaCandidateStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
import CFSG.FeitThompson.Local.MaximalTauTwoNonemptyTypeIOrII
import CFSG.FeitThompson.Local.SignalizerNilpotentSupportingCore
import CFSG.FeitThompson.Local.PConfigurationKappaFactors
import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup
import CFSG.FeitThompson.OddOrder.PConfigCoprimeFrobeniusAction

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson

universe u

variable {G : Type*} [Group G] [Finite G]

theorem notMem_tauTwoPrimes_of_dvd_natCard_W₁ [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {T E W₁ W₂ : Subgroup G} (hT : IsCoatom T) (hc : IsWitnessedPConfiguration T E W₁ W₂)
    {p : ℕ} (hp : p.Prime) (hpW : p ∣ Nat.card ↥W₁) : p ∉ tauTwoPrimes T :=
  fun hpτ => notMem_kappaPrimes_of_mem_tauTwoPrimes hpτ
    (mem_kappaPrimes_of_dvd_natCard_W₁ hna hodd hsolv hT hc hp hpW)

theorem mem_commutator_of_forall_mem_tauTwoPrimes [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {T : Subgroup G} (hT : IsCoatom T) (hII : IsTypeII T) {x : G} (hxT : x ∈ T)
    (hx : ∀ p : ℕ, p.Prime → p ∣ orderOf x → p ∈ tauTwoPrimes T) :
    x ∈ (⁅T, T⁆ : Subgroup G) := by
  obtain ⟨E, W₁, W₂, hcfg⟩ := hII.exists_isPConfiguration
  have hc := hcfg.isWitnessedPConfiguration
  have hcop : (orderOf x).Coprime (Nat.card ↥W₁) := by
    by_contra h
    obtain ⟨p, hp, hpx, hpW⟩ := Nat.Prime.not_coprime_iff_dvd.1 h
    exact notMem_tauTwoPrimes_of_dvd_natCard_W₁ hna hodd hsolv hT hc hp hpW (hx p hp hpx)
  have hnormal := normal_subgroupOf_commutator_self T
  have hidx : ((⁅T, T⁆ : Subgroup G).subgroupOf T).index = Nat.card ↥W₁ := by
    rw [hc.isComplement'_subgroupOf_commutator_W₁.symm.index_eq_card,
      natCard_subgroupOf hc.le_M_W₁]
  have hmem : (⟨x, hxT⟩ : ↥T) ∈ (⁅T, T⁆ : Subgroup G).subgroupOf T :=
    mem_of_coprime_orderOf_index (by rw [hidx, Subgroup.orderOf_mk]; exact hcop)
  exact Subgroup.mem_subgroupOf.1 hmem

theorem FTS_signalizer_supporting_type_exterior
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_five_type_local_classification.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_local_pair.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_kappa_semiprime_complement_existence.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FTS_kappa_residual_prime_overgroup_intersection.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_outside_sigma_plane_structure.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_signalizer_unique_supporting_maximum.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_signalizer_supporting_type_exterior.{u} := by
  intro G _ _ hG x hx hk T hT
  have := hG.isSimpleGroup
  obtain ⟨-, -, -, hx1⟩ := mem_sigmaSupport.1 hx
  have hxT : x ∈ T := hT.le (Subgroup.mem_centralizer_iff.2 (by simp))
  obtain ⟨-, hHS, -, -, hRx, hRne, hxnotH, -⟩ :=
    FTS_signalizer_nilpotent_supporting_core h₂ h₆ h₇ G hG x hx hk T hT
  obtain ⟨-, -, hprimes, -⟩ := (h₇ G hG x hx hk).2 T hT.isCoatom hT.le
  have hτ : (tauTwoPrimes T).Nonempty :=
    ⟨(orderOf x).minFac, hprimes _
      (Nat.minFac_prime fun h => hx1 (orderOf_eq_one_iff.1 h)) (Nat.minFac_dvd _)⟩
  have htype := FTS_tau_two_maximum_type_one_or_two h₁ h₃ h₄ h₅ G hG T hT.isCoatom hτ
  refine ⟨htype, hHS, hRx, hRne, fun _ => ⟨⟨hxT, hx1, hRne⟩, fun hmem => hxnotH hmem.1⟩,
    fun hII => ⟨⟨?_, hx1, hRne⟩, fun hmem => hxnotH hmem.1⟩⟩
  exact mem_commutator_of_forall_mem_tauTwoPrimes hG.not_isMulCommutative hG.odd_natCard
    hG.isSolvable_of_ne_top hT.isCoatom hII hxT hprimes

end

end CFSG.FeitThompson.Proofs
