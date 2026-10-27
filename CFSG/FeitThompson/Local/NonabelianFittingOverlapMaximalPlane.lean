module

public import CFSG.FeitThompson.Statements.FittingOverlapKappaStatements
public import CFSG.FeitThompson.Statements.SigmaNormalizerTauStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Local.Omega1CentralizerCommutatorBound
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
import CFSG.FeitThompson.Local.NonabelianFittingOverlapPrimary
import CFSG.FeitThompson.Local.FittingOverlapPrimeCentralizerSmall
import CFSG.FeitThompson.Local.GlobalMaximalPlaneGeometry
import CFSG.FeitThompson.Local.NonuniqueLinesAlphaCoreTrivial
import CFSG.FeitThompson.Local.SigmaConjugateIntersectionCyclic
import CFSG.FeitThompson.Local.NonabelianAmbientPlaneCentralizer
import CFSG.FeitThompson.Local.NoncentralInvariantSylowFixedPointFreePlane
import CFSG.FeitThompson.Local.UniqueMaximalOvergroupCentralizerTauOneThree
import CFSG.FeitThompson.Local.ExceptionalInvariantSylowSeparation
import CFSG.FeitThompson.Local.AbelianAmbientCharacteristicChain
import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
import CFSG.FeitThompson.Local.MixedFittingCentralizerConstrained
import CFSG.FeitThompson.Local.HallCoreInSigmaCore
import CFSG.FeitThompson.Local.RankThreeNormalAbelianSelfCentralizing
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.CentralProductPlaneCentralizer
import CFSG.FeitThompson.Representations.PrimeCentralTorsionCharacteristic
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.OddOrder.SigmaElementFusionControlled
import CFSG.FeitThompson.OddOrder.ControlledWitnessCentralTorsion
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

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup Pointwise _root_.CFSG.FeitThompson

universe u

variable {G : Type u} [Group G] [Finite G] {M X L : Subgroup G} {g : G} {p : ℕ}

omit [Finite G] in
theorem coe_subgroupCenterTorsionBy_eq_pTorsionSet_centreIn (p : ℕ) (P : Subgroup G) :
    ((subgroupCenterTorsionBy P p : Subgroup G) : Set G) = pTorsionSet p (centreIn P) := by
  ext z
  rw [SetLike.mem_coe, mem_subgroupCenterTorsionBy, mem_pTorsionSet, centreIn_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨Subgroup.mem_inf.2 ⟨h1, Subgroup.mem_centralizer_iff.2 fun x hx => h2 x hx⟩, h3⟩
  · rintro ⟨h1, h3⟩
    obtain ⟨h1P, h1c⟩ := Subgroup.mem_inf.1 h1
    exact ⟨h1P, fun x hx => Subgroup.mem_centralizer_iff.1 h1c x hx, h3⟩

theorem characteristic_subgroupOf_subgroupCenterTorsionBy_self (hp : p.Prime) (P : Subgroup G)
    (hP : IsPGroup p ↥P) : ((subgroupCenterTorsionBy P p).subgroupOf P).Characteristic := by
  have := Fact.mk hp
  have hcard : Nat.card ↥P = p ^ (Nat.card ↥P).factorization p := by
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    rw [hn, Nat.Prime.factorization_pow hp]
    simp
  exact characteristic_subgroupOf_subgroupCenterTorsionBy hP.isNilpotent le_rfl hcard

theorem natCard_pCoreIn_eq_pow_factorization (hp : p.Prime) (H : Subgroup G)
    (hnil : Group.IsNilpotent ↥H) :
    Nat.card ↥(pCoreIn p H) = p ^ (Nat.card ↥H).factorization p := by
  have := Fact.mk hp
  have := hnil
  obtain ⟨S⟩ : Nonempty (Sylow p ↥H) := inferInstance
  have hQcard : Nat.card ↥((S : Subgroup ↥H).map H.subtype)
      = p ^ (Nat.card ↥H).factorization p := by
    rw [Subgroup.card_map_of_injective H.subtype_injective, S.card_eq_multiplicity]
  have hQP : (S : Subgroup ↥H).map H.subtype ≤ pCoreIn p H :=
    le_pCoreIn_of_isPGroup_of_isNilpotent hp (Subgroup.map_subtype_le _)
      (IsPGroup.of_card hQcard)
  obtain ⟨k, hk⟩ := (isPGroup_pCoreIn hp H).exists_card_eq
  have hdvd : p ^ k ∣ Nat.card ↥H := by
    rw [← hk]; exact Subgroup.card_dvd_of_le (pCoreIn_le p H)
  have hkle : k ≤ (Nat.card ↥H).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 hdvd
  refine le_antisymm ?_ ?_
  · rw [hk]; exact Nat.pow_le_pow_right hp.pos hkle
  · rw [← hQcard]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hQP)

theorem le_two_of_isElementaryAbelian_of_le (hp : p.Prime) (hG : IsFBGAmbient G)
    (hM : IsCoatom M) (hpσ : p ∈ sigmaPrimes M)
    (hPcard : Nat.card ↥(pCoreIn p (hallCoreIn M)) = p ^ (Nat.card G).factorization p)
    (hrank : maxElementaryAbelianPRank ↥(centralizerWithin (hallCoreIn M) L) ≤ 2)
    (hLP : L ≤ pCoreIn p (hallCoreIn M)) (hLcard : Nat.card ↥L = p)
    {E : Subgroup G} (hE : IsElementaryAbelian p E) (hLE : L ≤ E) {d : ℕ}
    (hEcard : Nat.card ↥E = p ^ d) : d ≤ 2 := by
  have := Fact.mk hp
  have := hG.isSimpleGroup
  have hLne : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hLcard
    exact hp.one_lt.ne' hLcard.symm
  obtain ⟨l, hl1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hLne
  have hxL : (l : G) ∈ L := l.2
  have hx1 : (l : G) ≠ 1 := fun h => hl1 (Subtype.ext h)
  have hLea : IsElementaryAbelian p L := IsElementaryAbelian.of_natCard_eq_prime hp hLcard
  have hxord : orderOf (l : G) = p := orderOf_eq_prime (hLea.pow_eq_one hxL) hx1
  have hLzp : Subgroup.zpowers (l : G) = L :=
    _root_.CFSG.FeitThompson.Proofs.zpowers_eq_of_natCard_prime hp hLcard hxL hx1
  obtain ⟨a, ha⟩ := exists_forall_inv_mul_mul_mem hPcard hE.isPGroup
  have hPM : pCoreIn p (hallCoreIn M) ≤ M := (pCoreIn_le p _).trans (hallCoreIn_le M)
  have hxM : (l : G) ∈ M := hPM (hLP hxL)
  have hxaM : a⁻¹ * (l : G) * a ∈ M := hPM (ha (l : G) (hLE hxL))
  obtain ⟨b, hbM, hab⟩ := exists_mem_conj_eq_of_mem_sigmaPrimes hG.not_isMulCommutative
    hG.odd_natCard hG.isSolvable hM hpσ hxM ⟨1, by rw [pow_one, hxord]⟩ hxaM
  have hMnorm : M ≤ normalizer ((hallCoreIn M : Subgroup G) : Set G) := by
    rw [CFSG.FeitThompson.hallCoreIn_eq]
    exact le_normalizer_map_subtype_hallCore M
  have hbP := le_normalizer_pCoreIn p hMnorm hbM
  have hxt : (a * b⁻¹)⁻¹ * (l : G) * (a * b⁻¹) = (l : G) := by
    simp only [mul_inv_rev, inv_inv]
    calc b * a⁻¹ * (l : G) * (a * b⁻¹) = b * (a⁻¹ * (l : G) * a) * b⁻¹ := by group
      _ = b * (b⁻¹ * (l : G) * b) * b⁻¹ := by rw [hab]
      _ = (l : G) := by group
  have hEtmem : ∀ y ∈ E.map (MulAut.conj (a * b⁻¹)⁻¹).toMonoidHom,
      ∃ e ∈ E, (a * b⁻¹)⁻¹ * e * (a * b⁻¹) = y := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hy
    exact ⟨e, he, by simp [MulAut.conj]⟩
  have hEtP : E.map (MulAut.conj (a * b⁻¹)⁻¹).toMonoidHom ≤ pCoreIn p (hallCoreIn M) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := hEtmem y hy
    have h1 : a⁻¹ * e * a ∈ pCoreIn p (hallCoreIn M) := ha e he
    have h2 : (a * b⁻¹)⁻¹ * e * (a * b⁻¹) = b * (a⁻¹ * e * a) * b⁻¹ := by group
    rw [h2]
    exact (Subgroup.mem_normalizer_iff.1 hbP _).1 h1
  have hEtL : E.map (MulAut.conj (a * b⁻¹)⁻¹).toMonoidHom ≤
      centralizer ((L : Subgroup G) : Set G) := by
    intro y hy
    obtain ⟨e, he, rfl⟩ := hEtmem y hy
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [SetLike.mem_coe, ← hLzp] at hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hxe : (l : G) * e = e * (l : G) := hE.mul_comm (hLE hxL) he
    have hbase : Commute (l : G) ((a * b⁻¹)⁻¹ * e * (a * b⁻¹)) := by
      change (l : G) * _ = _ * (l : G)
      calc (l : G) * ((a * b⁻¹)⁻¹ * e * (a * b⁻¹))
            = ((a * b⁻¹)⁻¹ * (l : G) * (a * b⁻¹)) * ((a * b⁻¹)⁻¹ * e * (a * b⁻¹)) := by
              rw [hxt]
        _ = (a * b⁻¹)⁻¹ * ((l : G) * e) * (a * b⁻¹) := by group
        _ = (a * b⁻¹)⁻¹ * (e * (l : G)) * (a * b⁻¹) := by rw [hxe]
        _ = ((a * b⁻¹)⁻¹ * e * (a * b⁻¹)) * ((a * b⁻¹)⁻¹ * (l : G) * (a * b⁻¹)) := by group
        _ = ((a * b⁻¹)⁻¹ * e * (a * b⁻¹)) * (l : G) := by rw [hxt]
    exact (hbase.zpow_left n).eq
  have hEtC : E.map (MulAut.conj (a * b⁻¹)⁻¹).toMonoidHom ≤
      centralizerWithin (hallCoreIn M) L :=
    le_inf (hEtP.trans (pCoreIn_le p _)) hEtL
  have hEtea : IsElementaryAbelian p (E.map (MulAut.conj (a * b⁻¹)⁻¹).toMonoidHom) :=
    hE.map _
  have hEtcard : Nat.card ↥(E.map (MulAut.conj (a * b⁻¹)⁻¹).toMonoidHom) = p ^ d := by
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj (a * b⁻¹)⁻¹).toMonoidHom)
      (MulAut.conj (a * b⁻¹)⁻¹).injective, hEcard]
  calc d ≤ elementaryAbelianPRank p ↥(centralizerWithin (hallCoreIn M) L) :=
        hEtea.le_elementaryAbelianPRank hp hEtcard hEtC
    _ ≤ maxElementaryAbelianPRank ↥(centralizerWithin (hallCoreIn M) L) :=
        elementaryAbelianPRank_le_maxElementaryAbelianPRank hp
    _ ≤ 2 := hrank

theorem nonabelian_fitting_overlap_maximal_plane_of_isFittingOverlapSetup
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : _root_.CFSG.FeitThompson.Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₅ : _root_.CFSG.FeitThompson.Statements.FPL_low_rank_sylow_central_product.{u})
    (h₆ : _root_.CFSG.FeitThompson.Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₇ : _root_.CFSG.FeitThompson.Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : _root_.CFSG.FeitThompson.Statements.FTS_proper_subgroup_p_length_one.{u})
    (hG : IsFBGAmbient G) (hsetup : IsFittingOverlapSetup M X g)
    (hnab : ¬ IsMulCommutative ↥(hallCoreIn M)) (hp : p ∈ (Nat.card ↥X).primeFactors)
    (hLX : L ≤ X) (hLcard : Nat.card ↥L = p) :
    ¬ IsMulCommutative ↥(pCoreIn p (hallCoreIn M)) ∧
      (∃ Q : Sylow p G, (Q : Subgroup G) = pCoreIn p (hallCoreIn M)) ∧
      (∃ Z₀ : Subgroup G,
        (Z₀ : Set G) = pTorsionSet p (centreIn (pCoreIn p (hallCoreIn M))) ∧
          (Z₀.subgroupOf (pCoreIn p (hallCoreIn M))).Characteristic ∧
          Nat.card ↥Z₀ = p ∧
          ∃ A : Subgroup G, IsInternalDirectProduct A L Z₀ ∧ IsElementaryAbelian p A ∧
            Nat.card ↥A = p ^ 2 ∧ Maximal (IsElementaryAbelian p) A) ∧
      X = L ∧ Nat.card ↥X = p := by
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have := Fact.mk hpp
  have := hG.isSimpleGroup
  have _inst : Fintype G := Fintype.ofFinite G
  obtain ⟨hXcyc, hXp, hXP, hPnab, -, -, hLnotZ⟩ :=
    nonabelian_fitting_overlap_primary_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₆ h₇ h₈ hG hsetup
      hnab hp
  obtain ⟨hSnil, hHS, hXS⟩ :=
    isNilpotent_sigmaCore_and_hallCoreIn_eq_and_le h₁ h₂ h₃ h₈ hG hsetup
  have hHnil : Group.IsNilpotent ↥(hallCoreIn M) := isNilpotent_hallCoreIn M
  have hXH : X ≤ hallCoreIn M := hHS ▸ hXS
  have hLne : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hLcard
    exact hpp.one_lt.ne' hLcard.symm
  have hLp : IsPGroup p ↥L := IsPGroup.of_card (n := 1) (by simpa using hLcard)
  have hLP : L ≤ pCoreIn p (hallCoreIn M) :=
    le_pCoreIn_of_isPGroup_of_isNilpotent hpp (hLX.trans hXH) hLp
  have hPne : pCoreIn p (hallCoreIn M) ≠ ⊥ := by
    intro h
    rw [h] at hPnab
    exact hPnab inferInstance
  have hpσ : p ∈ sigmaPrimes M :=
    _root_.CFSG.FeitThompson.Proofs.mem_sigmaPrimes_of_isPGroup_le_sigmaCore hpp hLne hLp
      (hLX.trans hXS)
  have hG2 : IsOddOrderMinimalSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  obtain ⟨-, hHallG, -⟩ := h₃ G hG2 M hsetup.isCoatom
  have hfac : (Nat.card ↥(sigmaCore M)).factorization p = (Nat.card G).factorization p :=
    _root_.CFSG.FeitThompson.Proofs.factorization_natCard_eq_of_isHallPiSubgroup hpp hHallG hpσ
  have hPcardG : Nat.card ↥(pCoreIn p (hallCoreIn M)) = p ^ (Nat.card G).factorization p := by
    rw [natCard_pCoreIn_eq_pow_factorization hpp _ hHnil, hHS, hfac]
  have hQ : ∃ Q : Sylow p G, (Q : Subgroup G) = pCoreIn p (hallCoreIn M) :=
    ⟨Sylow.ofCard _ hPcardG, Sylow.coe_ofCard _ _⟩
  have hZ₀coe := coe_subgroupCenterTorsionBy_eq_pTorsionSet_centreIn p (pCoreIn p (hallCoreIn M))
  have hZ₀char :
      ((subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p).subgroupOf
        (pCoreIn p (hallCoreIn M))).Characteristic :=
    characteristic_subgroupOf_subgroupCenterTorsionBy_self hpp _ (isPGroup_pCoreIn hpp _)
  have hZ₀ne : subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p ≠ ⊥ :=
    _root_.CFSG.FeitThompson.Proofs.subgroupCenterTorsionBy_ne_bot_of_isPGroup hpp
      (isPGroup_pCoreIn hpp _) hPne
  have hZ₀P : subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p ≤ pCoreIn p (hallCoreIn M) :=
    subgroupCenterTorsionBy_le
  have hZ₀cent : subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p ≤
      centralizer ((pCoreIn p (hallCoreIn M) : Subgroup G) : Set G) :=
    subgroupCenterTorsionBy_le_centralizer
  have hZ₀ea : IsElementaryAbelian p (subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) :=
    _root_.CFSG.FeitThompson.Proofs.isElementaryAbelian_subgroupCenterTorsionBy (G := G) p
      (pCoreIn p (hallCoreIn M))
  have hZ₀centre : subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p ≤
      centreIn (pCoreIn p (hallCoreIn M)) := by
    rw [centreIn_eq]; exact le_inf hZ₀P hZ₀cent
  have hLZ₀ : L ⊓ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p = ⊥ := by
    have hdvd : Nat.card ↥(L ⊓ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) ∣ p :=
      hLcard ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases hpp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd (hLnotZ L hLX hLcard)
        (not_not.2 ((Subgroup.eq_of_le_of_card_ge inf_le_left
          (by rw [hLcard, h1])) ▸ (inf_le_right.trans hZ₀centre)))
  have hcomm : ∀ x ∈ L, ∀ y ∈ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p,
      Commute x y := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.1 (hZ₀cent hy)) x (hLP hx)
  have hAprod : IsInternalDirectProduct
      (L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) L
      (subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) :=
    IsInternalDirectProduct.mk' (coe_sup_eq_mul_of_commute hcomm) hLZ₀ hcomm
  have hLea : IsElementaryAbelian p L := IsElementaryAbelian.of_natCard_eq_prime hpp hLcard
  have hAea : IsElementaryAbelian p
      (L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) := by
    refine isElementaryAbelian_iff.2 ⟨_root_.CFSG.FeitThompson.Proofs.isMulCommutative_sup
      hLea.isMulCommutative hZ₀ea.isMulCommutative (fun x hx y hy => (hcomm x hx y hy).eq), ?_⟩
    intro a ha
    have ha' : a ∈ ((L : Set G) *
        ((subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p : Subgroup G) : Set G)) := by
      rw [← hAprod.coe_eq_mul]; exact ha
    obtain ⟨x, hx, y, hy, rfl⟩ := ha'
    change (x * y) ^ p = 1
    rw [(hcomm x hx y hy).mul_pow, hLea.pow_eq_one hx, hZ₀ea.pow_eq_one hy, one_mul]
  have hAcardmul : Nat.card ↥(L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p)
      = p * Nat.card ↥(subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) := by
    rw [hAprod.card_eq_mul, hLcard]
  have hrank : maxElementaryAbelianPRank ↥(centralizerWithin (hallCoreIn M) L) ≤ 2 :=
    (centralizerWithin_hallCoreIn_properties_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₈ hG hsetup
      hpp hLX hLcard).2.2.1
  have key : ∀ E : Subgroup G, IsElementaryAbelian p E → L ≤ E → ∀ d : ℕ,
      Nat.card ↥E = p ^ d → d ≤ 2 := fun E hE hLE d hEc =>
    le_two_of_isElementaryAbelian_of_le hpp hG hsetup.isCoatom hpσ hPcardG hrank hLP hLcard hE
      hLE hEc
  obtain ⟨k, hk⟩ := hZ₀ea.isPGroup.exists_card_eq
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hZ₀ne
    · exact h
  have hAcardk : Nat.card ↥(L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p)
      = p ^ (1 + k) := by rw [hAcardmul, hk, pow_add, pow_one]
  have hkle : 1 + k ≤ 2 := key _ hAea le_sup_left _ hAcardk
  have hZ₀card : Nat.card ↥(subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) = p := by
    rw [hk, show k = 1 by omega, pow_one]
  have hAcard : Nat.card ↥(L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) = p ^ 2 := by
    rw [hAcardmul, hZ₀card, sq]
  have hAmax : Maximal (IsElementaryAbelian p)
      (L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) := by
    refine ⟨hAea, fun E hE hAE => ?_⟩
    obtain ⟨d, hd⟩ := hE.isPGroup.exists_card_eq
    have hd2 : d ≤ 2 := key E hE (le_sup_left.trans hAE) d hd
    refine (Subgroup.eq_of_le_of_card_ge hAE ?_).ge
    rw [hd, hAcard]
    exact Nat.pow_le_pow_right hpp.pos hd2
  have hpodd : Odd p :=
    Odd.of_dvd_nat hG.odd_natCard (hLcard ▸ Subgroup.card_subgroup_dvd_card L)
  have hG6 : _root_.CFSG.FeitThompson.Prep06.IsMinimalOddSimple G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable⟩
  have hAP : L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p ≤
      pCoreIn p (hallCoreIn M) := sup_le hLP hZ₀P
  obtain ⟨Z', hZ'coe, -, -, ⟨Y, hYle, hYcyc, -, hYdecomp⟩, -⟩ :=
    _root_.CFSG.FeitThompson.Proofs.FPL_global_maximal_plane_geometry h₅ G hG6 p hpp hpodd
      (L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p) (pCoreIn p (hallCoreIn M))
      (nonempty_mulEquiv_pi_of_isElementaryAbelian hpp hAea hAcard)
      (forall_not_nonempty_mulEquiv_of_maximal
        (_root_.CFSG.FeitThompson.Proofs.maximal_isElementaryAbelianSubgroup_of_maximal_isElementaryAbelian
          hAmax))
      ((isPGroup_pCoreIn hpp _).exists_card_eq) hAP hPnab
      {z | z ∈ pCoreIn p (hallCoreIn M) ⊓
        centralizer ((pCoreIn p (hallCoreIn M) : Subgroup G) : Set G) ∧ z ^ p = 1} rfl
  have hZ'eq : Z' = subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p := by
    refine SetLike.coe_injective ?_
    rw [hZ'coe, hZ₀coe]
    ext z
    rw [mem_pTorsionSet, centreIn_eq]
    rfl
  have hLZne : L ≠ Z' := by
    rw [hZ'eq]
    intro h
    rw [h, inf_idem] at hLZ₀
    exact hZ₀ne hLZ₀
  obtain ⟨hsup, hinfY, hcommLY⟩ := hYdecomp L le_sup_left hLcard hLZne
  have hXCA : X ≤ pCoreIn p (hallCoreIn M) ⊓
      centralizer ((L ⊔ subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p : Subgroup G) :
        Set G) := by
    refine le_inf hXP ?_
    have := hXcyc
    have hXab : IsMulCommutative ↥X := IsCyclic.isMulCommutative
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ ((L : Set G) *
        ((subgroupCenterTorsionBy (pCoreIn p (hallCoreIn M)) p : Subgroup G) : Set G)) := by
      rw [← hAprod.coe_eq_mul]; exact ha
    obtain ⟨l, hl, z, hz, rfl⟩ := ha'
    have hcl : Commute x l := by
      have h := congrArg (fun t : ↥X => (t : G))
        (mul_comm' (⟨x, hx⟩ : ↥X) (⟨l, hLX hl⟩ : ↥X))
      simpa [Commute, SemiconjBy] using h
    have hcz : Commute x z := (Subgroup.mem_centralizer_iff.1 (hZ₀cent hz)) x (hXP hx)
    exact ((hcl.mul_right hcz).symm).eq
  have hXY : X ⊓ Y = ⊥ := by
    by_contra hne
    have hXYp : IsPGroup p ↥(X ⊓ Y) := hXp.to_le inf_le_left
    obtain ⟨n, hn⟩ := hXYp.exists_card_eq
    have hdvdp : p ∣ Nat.card ↥(X ⊓ Y) := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rw [pow_zero] at hn
        exact absurd (Subgroup.card_eq_one.mp hn) hne
      · rw [hn]
        exact dvd_pow_self p hpos.ne'
    obtain ⟨L', hL'XY, hL'card⟩ :=
      _root_.CFSG.FeitThompson.Proofs.exists_le_natCard_eq_of_prime_dvd hpp hdvdp
    have := hXcyc
    have hL'L : L' = L :=
      eq_of_le_of_natCard_eq_of_isCyclic (hL'XY.trans inf_le_left) hLX (by rw [hL'card, hLcard])
    have hLY : L ≤ Y := hL'L ▸ (hL'XY.trans inf_le_right)
    rw [inf_eq_left.2 hLY] at hinfY
    exact hLne hinfY
  have hXL : X = L := by
    refine le_antisymm (fun x hx => ?_) hLX
    have hx' : x ∈ L ⊔ Y := by rw [hsup]; exact hXCA hx
    have hcomm2 : ∀ a ∈ L, ∀ b ∈ Y, Commute a b := fun a ha b hb =>
      (Subgroup.mem_centralizer_iff.1
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcommLY ha) b hb).symm
    have hx'' : x ∈ ((L : Set G) * (Y : Set G)) := by
      rw [← coe_sup_eq_mul_of_commute hcomm2]; exact hx'
    obtain ⟨l, hl, y, hy, rfl⟩ := hx''
    change l * y ∈ L
    have hyX : y ∈ X := by
      have hinv : l⁻¹ * (l * y) = y := by group
      rw [← hinv]
      exact X.mul_mem (X.inv_mem (hLX hl)) hx
    have hyXY : y ∈ X ⊓ Y := Subgroup.mem_inf.2 ⟨hyX, hy⟩
    rw [hXY, Subgroup.mem_bot] at hyXY
    rw [hyXY, mul_one]
    exact hl
  exact ⟨hPnab, hQ, ⟨_, hZ₀coe, hZ₀char, hZ₀card, _, hAprod, hAea, hAcard, hAmax⟩, hXL,
    by rw [hXL, hLcard]⟩

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open CFSG.FeitThompson

universe u

theorem FBG_nonabelian_fitting_overlap_maximal_plane
    (h₁ : Statements.FBG_nilpotent_sigma_core_fitting_structure.{u})
    (h₂ : Statements.FBG_nonnilpotent_sigma_core_hall_structure.{u})
    (h₃ : Statements.FBG_sigma_core_normal_hall.{u})
    (h₄ : Statements.FNI_nonabelian_prime_subgroup_unique_maximum.{u})
    (h₅ : Statements.FPL_low_rank_sylow_central_product.{u})
    (h₆ : Statements.FTS_beta_or_derived_line_centralizer_unique.{u})
    (h₇ : Statements.FTS_plane_maximal_overgroups.{u})
    (h₈ : Statements.FTS_proper_subgroup_p_length_one.{u}) :
    Statements.FBG_nonabelian_fitting_overlap_maximal_plane.{u} :=
  fun _ _ _ hG _ _ _ hsetup hnab _ hp _ hLX hLcard =>
    nonabelian_fitting_overlap_maximal_plane_of_isFittingOverlapSetup h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ hG
      hsetup hnab hp hLX hLcard

end

end CFSG.FeitThompson.Proofs
