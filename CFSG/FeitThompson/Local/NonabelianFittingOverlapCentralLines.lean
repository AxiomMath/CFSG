module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Local.Omega1CentralizerCommutatorBound
public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Local.CompetingMaximalFittingPrimeSupport
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.NonabelianFittingOverlapMaximalPlane
import CFSG.FeitThompson.Local.NonabelianFittingOverlapPrimary
import CFSG.FeitThompson.Local.FittingOverlapPrimeCentralizerSmall
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.NonuniqueLinesAlphaCoreTrivial
import CFSG.FeitThompson.Local.NoncentralInvariantSylowFixedPointFreePlane
import CFSG.FeitThompson.Local.OutsideSigmaKappaCoreFixerCyclic
import CFSG.FeitThompson.Local.UniquenessTransferCentralizerRankTwo
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.OddOrder.ControlledWitnessCentralTorsion
import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
public import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
public import CFSG.FeitThompson.Foundations.CharacteristicSubgroupInvariance
public import CFSG.FeitThompson.Foundations.HallImageQuotient
public import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
public import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
public import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
public import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
public import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
public import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
public import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
public import Mathlib
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {M X : Subgroup G} {g : G} {p q : ℕ}

theorem natCard_subgroupCenterTorsionBy_eq_of_isCyclic (hq : q.Prime) {Q : Subgroup G}
    (hQp : IsPGroup q ↥Q) (hQcyc : IsCyclic ↥Q) (hQne : Q ≠ ⊥) :
    Nat.card ↥(subgroupCenterTorsionBy Q q) = q := by
  have := Fact.mk hq
  have hZcyc : IsCyclic ↥(subgroupCenterTorsionBy Q q) :=
    isCyclic_of_le_of_isCyclic subgroupCenterTorsionBy_le hQcyc
  have hZne : subgroupCenterTorsionBy Q q ≠ ⊥ :=
    _root_.CFSG.FeitThompson.Proofs.subgroupCenterTorsionBy_ne_bot_of_isPGroup hq hQp hQne
  have hdvd : Nat.card ↥(subgroupCenterTorsionBy Q q) ∣ q := by
    have := hZcyc
    rw [← IsCyclic.exponent_eq_card]
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun z => ?_
    exact Subtype.ext (by simpa using (mem_subgroupCenterTorsionBy.1 z.2).2.2)
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h | h
  · exact absurd (Subgroup.card_eq_one.1 h) hZne
  · exact h

theorem pCoreIn_ne_bot_of_mem_primeFactors (hq : q.Prime) {H : Subgroup G}
    (hHnil : Group.IsNilpotent ↥H) (hqH : q ∈ (Nat.card ↥H).primeFactors) :
    pCoreIn q H ≠ ⊥ := by
  have hcard := natCard_pCoreIn_eq_pow_factorization hq H hHnil
  have h1 : 1 ≤ (Nat.card ↥H).factorization q :=
    Nat.Prime.factorization_pos_of_dvd hq Nat.card_pos.ne' (Nat.dvd_of_mem_primeFactors hqH)
  intro h
  rw [h, Subgroup.card_bot] at hcard
  have hle : q ^ 1 ≤ q ^ (Nat.card ↥H).factorization q := Nat.pow_le_pow_right hq.pos h1
  rw [← hcard, pow_one] at hle
  exact absurd hle hq.one_lt.not_ge

theorem pCoreIn_le_pComplCoreIn (hp : p.Prime) (hq : q.Prime) (hqp : q ≠ p) (H : Subgroup G) :
    pCoreIn q H ≤ pComplCoreIn p H := by
  have := Fact.mk hq
  refine le_pComplCoreIn (pCoreIn_le q H) (le_normalizer_pCoreIn q Subgroup.le_normalizer) ?_
  obtain ⟨n, hn⟩ := (isPGroup_pCoreIn hq H).exists_card_eq
  rw [hn]
  intro hdvd
  exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hdvd)).symm

theorem characteristic_subgroupOf_subgroupCenterTorsionBy_pCoreIn (hq : q.Prime) {H : Subgroup G}
    (hHnil : Group.IsNilpotent ↥H) :
    ((subgroupCenterTorsionBy (pCoreIn q H) q).subgroupOf H).Characteristic := by
  have := Fact.mk hq
  exact characteristic_subgroupOf_subgroupCenterTorsionBy hHnil (pCoreIn_le q H)
    (natCard_pCoreIn_eq_pow_factorization hq H hHnil)

theorem exists_prime_isElementaryAbelian_natCard_eq_sq_of_not_isCyclic (hodd : Odd (Nat.card G))
    {R : Subgroup G} (hRab : IsMulCommutative ↥R) (hRnc : ¬ IsCyclic ↥R) :
    ∃ r : ℕ, r.Prime ∧ ∃ B ≤ R, IsElementaryAbelian r B ∧ Nat.card ↥B = r ^ 2 := by
  have hz : ¬ IsZGroup ↥R := fun h =>
    hRnc (_root_.CFSG.FeitThompson.Proofs.isCyclic_of_isMulCommutative_of_isZGroup hRab h)
  rw [isZGroup_iff] at hz
  simp only [not_forall] at hz
  obtain ⟨r, hr, S, hScyc⟩ := hz
  set S' : Subgroup G := (S : Subgroup ↥R).map R.subtype with hS'
  have he : ↥(S : Subgroup ↥R) ≃* ↥S' := Subgroup.equivMapOfInjective _ _ R.subtype_injective
  have hS'p : IsPGroup r ↥S' := S.isPGroup'.of_equiv he
  have hS'nc : ¬ IsCyclic ↥S' := fun h => hScyc ((MulEquiv.isCyclic he).2 h)
  have hS'R : S' ≤ R := Subgroup.map_subtype_le _
  have hS'ne : S' ≠ ⊥ := by
    intro h
    rw [h] at hS'nc
    exact hS'nc inferInstance
  have := Fact.mk hr
  obtain ⟨n, hn⟩ := hS'p.exists_card_eq
  have hrdvd : r ∣ Nat.card ↥S' := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero] at hn
      exact absurd (Subgroup.card_eq_one.1 hn) hS'ne
    · rw [hn]; exact dvd_pow_self r hpos.ne'
  have hrodd : Odd r :=
    Odd.of_dvd_nat hodd (hrdvd.trans (Subgroup.card_subgroup_dvd_card S'))
  obtain ⟨B, hBS, hBea, hBcard⟩ :=
    _root_.CFSG.FeitThompson.Proofs.exists_le_isElementaryAbelian_natCard_eq_sq_of_not_isCyclic hr hrodd
      hS'p hS'nc
  exact ⟨r, hr, B, hBS.trans hS'R, hBea, hBcard⟩

theorem isCyclic_pComplCoreIn_of_isFittingOverlapSetup
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g)
    (hnab : ¬ IsMulCommutative ↥(hallCoreIn M)) (hp : p ∈ (Nat.card ↥X).primeFactors) :
    IsCyclic ↥(pComplCoreIn p (hallCoreIn M)) := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have := Fact.mk hpp
  have := hG.isSimpleGroup
  have hHnil : Group.IsNilpotent ↥(hallCoreIn M) := isNilpotent_hallCoreIn M
  obtain ⟨-, -, hXP, hPnab, hRab, hprod, -⟩ :=
    nonabelian_fitting_overlap_primary_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₆ h₇ h₈ hG hsetup
      hnab hp
  obtain ⟨L, hLX, hLcard⟩ := _root_.CFSG.FeitThompson.Proofs.exists_le_natCard_eq_of_prime_dvd hpp
    (Nat.dvd_of_mem_primeFactors hp)
  have hLP : L ≤ pCoreIn p (hallCoreIn M) := hLX.trans hXP
  obtain ⟨-, -, -, hnu, -⟩ :=
    centralizerWithin_hallCoreIn_properties_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₈ hG hsetup
      hpp hLX hLcard
  by_contra hRnc
  obtain ⟨r, hr, B, hBR, hBea, hBcard⟩ :=
    exists_prime_isElementaryAbelian_natCard_eq_sq_of_not_isCyclic hG.odd_natCard hRab hRnc
  have hPne : pCoreIn p (hallCoreIn M) ≠ ⊥ := by
    intro h
    rw [h] at hPnab
    exact hPnab inferInstance
  obtain ⟨a, ha⟩ := (isPGroup_pCoreIn hpp (hallCoreIn M)).exists_card_eq
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | hpos
    · rw [pow_zero] at ha
      exact absurd (Subgroup.card_eq_one.1 ha) hPne
    · exact hpos
  have hGm : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨N, ⟨hN, hPN⟩, huniq⟩ := h₄ G hGm p a _ hpp ha1 ha hPnab
  have hPuniq : IsUniqueMaximalOvergroup (pCoreIn p (hallCoreIn M)) N :=
    ⟨hN, hPN, fun N' hN' hPN' => huniq N' ⟨hN', hPN'⟩⟩
  have hRP : pComplCoreIn p (hallCoreIn M) ≤
      centralizer ((pCoreIn p (hallCoreIn M) : Subgroup G) : Set G) := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.1 ?_
    rw [Subgroup.commutator_comm]
    exact hprod.commutator_eq_bot
  have hBuniq : IsUniqueMaximalOvergroup B N :=
    isUniqueMaximalOvergroup_of_le_centralizer hr hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable (bot_lt_iff_ne_bot.2 hPne) hPuniq (hBR.trans hRP)
      (hBea.le_elementaryAbelianPRank hr hBcard le_rfl)
  have hBC : B ≤ centralizerWithin (hallCoreIn M) L :=
    hBR.trans (pComplCoreIn_le_centralizerWithin hpp (hallCoreIn M) hHnil hLP)
  have hCtop : centralizerWithin (hallCoreIn M) L ≠ ⊤ := fun h =>
    hsetup.isCoatom.1 (top_le_iff.1 (h ▸ (centralizerWithin_le _ _).trans (hallCoreIn_le M)))
  exact hnu ⟨N, hBuniq.mono hBC hCtop⟩

theorem nonabelian_fitting_overlap_central_lines_of_isFittingOverlapSetup
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g)
    (hnab : ¬ IsMulCommutative ↥(hallCoreIn M)) :
    (Nat.card ↥X).Prime ∧
      IsCyclic ↥(pComplCoreIn (Nat.card ↥X) (hallCoreIn M)) ∧
      ∀ q ∈ (Nat.card ↥(hallCoreIn M)).primeFactors, ∃ Z₀ : Subgroup G,
        (Z₀ : Set G) = pTorsionSet q (centreIn (pCoreIn q (hallCoreIn M))) ∧
          (Z₀.subgroupOf (hallCoreIn M)).Characteristic ∧ Nat.card ↥Z₀ = q := by
  have hHnil : Group.IsNilpotent ↥(hallCoreIn M) := isNilpotent_hallCoreIn M
  have hXne : Nat.card ↥X ≠ 1 := fun h => hsetup.ne_bot (Subgroup.card_eq_one.1 h)
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hXne
  have hpmem : p ∈ (Nat.card ↥X).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hpp, hpdvd, Nat.card_pos.ne'⟩
  obtain ⟨L, hLX, hLcard⟩ := _root_.CFSG.FeitThompson.Proofs.exists_le_natCard_eq_of_prime_dvd hpp hpdvd
  obtain ⟨-, -, ⟨Z, hZcoe, -, hZcard, -⟩, -, hXcard⟩ :=
    nonabelian_fitting_overlap_maximal_plane_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG
      hsetup hnab hpmem hLX hLcard
  have hZeq : Z = subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p := by
    refine SetLike.coe_injective ?_
    rw [hZcoe, coe_subgroupCenterTorsionBy_eq_pTorsionSet_centreIn]
  have hRcyc : IsCyclic ↥(pComplCoreIn p (hallCoreIn M)) :=
    isCyclic_pComplCoreIn_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₆ h₇ h₈ hG hsetup hnab hpmem
  refine ⟨by rw [hXcard]; exact hpp, by rw [hXcard]; exact hRcyc, fun r hr => ?_⟩
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  refine ⟨subgroupCenterTorsionBy (pCoreIn r (hallCoreIn M)) r,
    coe_subgroupCenterTorsionBy_eq_pTorsionSet_centreIn _ _,
    characteristic_subgroupOf_subgroupCenterTorsionBy_pCoreIn hrp hHnil, ?_⟩
  by_cases hrpe : r = p
  ·
    subst hrpe
    rw [← hZeq]
    exact hZcard
  ·
    refine natCard_subgroupCenterTorsionBy_eq_of_isCyclic hrp (isPGroup_pCoreIn hrp _) ?_
      (pCoreIn_ne_bot_of_mem_primeFactors hrp hHnil hr)
    exact isCyclic_of_le_of_isCyclic (pCoreIn_le_pComplCoreIn hpp hrp hrpe _) hRcyc

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson

universe u

theorem FBG_nonabelian_fitting_overlap_central_lines
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₅ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₆ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₇ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_nonabelian_fitting_overlap_central_lines.{u} :=
  fun _ _ _ hG _ _ _ hsetup hnab =>
    nonabelian_fitting_overlap_central_lines_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG
      hsetup hnab

end

end CFSG.FeitThompson.Proofs
