module

public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
public import CFSG.FeitThompson.Local.CyclicCentralizerFactorRestriction
public import CFSG.FeitThompson.Representations.PrimeCentralTorsionCharacteristic
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Local.SigmaHallInDerivedSubgroup
import CFSG.FeitThompson.Local.HighRankCentralTorsionLine
import CFSG.FeitThompson.Local.SigmaCoreNormalHallDerived
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Local.MaximalPlaneDerivedNormalComplement
import CFSG.FeitThompson.Local.LowRankFittingDerivedNilpotent
import CFSG.FeitThompson.Local.PrimeCentralizerMinimalFittingAbelian
import CFSG.FeitThompson.Local.CoprimePlaneGeneratesSolvableGroup
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import all CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
import CFSG.FeitThompson.Foundations.HomPreservesGeneratedCommutators
import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions
import CFSG.FeitThompson.Foundations.NilpotentSubgroupNilpotent
import CFSG.FeitThompson.Foundations.SolvableHomImageSolvable
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import CFSG.FeitThompson.Local.CoprimeSolvableFixedCosetLifting
import Mathlib

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson.Prep08
  Subgroup

universe u

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
theorem exists_isSylowOf_ge {p : ℕ} (hp : p.Prime) {A M : Subgroup G} (hAM : A ≤ M)
    (hA : IsPGroup p ↥A) : ∃ P : Subgroup G, IsSylowOf p P M ∧ A ≤ P := by
  have := Fact.mk hp
  obtain ⟨S, hS⟩ := (hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAM).symm).exists_le_sylow
  refine ⟨(S : Subgroup ↥M).map M.subtype, ⟨S, rfl⟩, ?_⟩
  calc A = (A.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hAM).symm
    _ ≤ _ := Subgroup.map_mono hS

theorem elementaryAbelianPRank_of_isSylowOf {p : ℕ} (hp : p.Prime) {P M : Subgroup G}
    (h : IsSylowOf p P M) : elementaryAbelianPRank p ↥P = elementaryAbelianPRank p ↥M := by
  have := Fact.mk hp
  obtain ⟨S, rfl⟩ := h
  rw [← elementaryAbelianPRank_eq_of_mulEquiv (p := p) hp.one_lt
    ((S : Subgroup ↥M).equivMapOfInjective M.subtype M.subtype_injective)]
  exact elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hp S.card_eq_multiplicity

theorem elementaryAbelianPRank_le_alphaCore {L : Type*} [Group L] [Finite L] {r : ℕ}
    (hHall : IsHallSubgroup (alphaPrimes L) (alphaCore L)) (hr : r ∈ alphaPrimes L) :
    elementaryAbelianPRank r L ≤ elementaryAbelianPRank r ↥(alphaCore L) := by
  have hrp : r.Prime := (mem_alphaPrimes.1 hr).1
  have := alphaCore_normal L
  obtain ⟨H, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1
    (elementaryAbelianPRank_mem_elementaryAbelianRanks (X := L) (p := r) hrp.one_lt)
  have hcard : Nat.card ↥H = r ^ elementaryAbelianPRank r L := by
    rw [Nat.card_congr e.toEquiv, card_pi_multiplicative_zmod]
  have hpi : IsPiSubgroup (alphaPrimes L) H := by
    rw [isPiSubgroup_iff]
    intro q hq
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hqp, hqd, -⟩ := hq
    rw [hcard] at hqd
    have hqr : q = r := (Nat.prime_dvd_prime_iff_eq hqp hrp).1 (hqp.dvd_of_dvd_pow hqd)
    exact hqr ▸ hr
  have hHle : H ≤ alphaCore L :=
    IsHallPiSubgroup.le_of_isPiSubgroup hHall.isHallPiSubgroup hpi
  exact le_elementaryAbelianPRank hrp.one_lt (mem_elementaryAbelianRanks.2
    ⟨H.subgroupOf (alphaCore L), ⟨(Subgroup.subgroupOfEquivOfLe hHle).trans e⟩⟩)

omit [Finite G] in
theorem eq_subgroupCenterTorsionBy {p : ℕ} {P Z0 : Subgroup G}
    (h : (Z0 : Set G) = {z | z ∈ P ∧ (∀ y ∈ P, z * y = y * z) ∧ z ^ p = 1}) :
    Z0 = subgroupCenterTorsionBy P p := by
  refine SetLike.coe_injective ?_
  rw [h]
  ext z
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, mem_subgroupCenterTorsionBy]
  exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, fun x hx => (h2 x hx).symm, h3⟩,
    fun ⟨h1, h2, h3⟩ => ⟨h1, fun y hy => (h2 y hy).symm, h3⟩⟩

omit [Finite G] in
theorem subgroupCenterTorsionBy_eq_map (P : Subgroup G) (n : ℕ) :
    subgroupCenterTorsionBy P n = (centerTorsionBy ↥P n).map P.subtype := by
  ext z
  rw [mem_subgroupCenterTorsionBy, Subgroup.mem_map]
  constructor
  · rintro ⟨hzP, hcomm, hzn⟩
    refine ⟨⟨z, hzP⟩, mem_centerTorsionBy_of_mem_center (Subgroup.mem_center_iff.2 ?_)
      (Subtype.ext hzn), rfl⟩
    exact fun x => Subtype.ext (hcomm x.1 x.2)
  · rintro ⟨w, hw, rfl⟩
    rw [mem_centerTorsionBy] at hw
    exact ⟨w.2, fun x hx => congrArg Subtype.val (Subgroup.mem_center_iff.1 hw.1 ⟨x, hx⟩),
      congrArg Subtype.val hw.2⟩

theorem subgroupCenterTorsionBy_ne_bot_of_isPGroup {p : ℕ} (hp : p.Prime) {P : Subgroup G}
    (hP : IsPGroup p ↥P) (hPbot : P ≠ ⊥) : subgroupCenterTorsionBy P p ≠ ⊥ := by
  have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).2 hPbot
  have h := centerTorsionBy_ne_bot_of_isPGroup (R := ↥P) hp hP
  rw [subgroupCenterTorsionBy_eq_map, Ne, Subgroup.map_eq_bot_iff]
  simpa [P.ker_subtype] using h

omit [Finite G] in
theorem isElementaryAbelian_subgroupCenterTorsionBy (p : ℕ) (P : Subgroup G) :
    IsElementaryAbelian p (subgroupCenterTorsionBy P p) := by
  rw [subgroupCenterTorsionBy_eq_map]
  exact IsElementaryAbelian.map_subtype
    (IsElementaryAbelian.mono (p := p) (A := centerTorsionBy ↥P p)
      (isElementaryAbelian_iff.2 ⟨inferInstance, fun _ hx => pow_eq_one_of_mem_centerTorsionBy hx⟩)
      le_rfl)

theorem nonuniqueLine_sylow_clauses {p : ℕ} {M A P : Subgroup G} (hp : p.Prime)
    (hplane : IsPlaneAt p A) (hAM : A ≤ M)
    (hb1 : ∀ Y ≤ A, Nat.card ↥Y = p → ∀ r : ℕ,
      elementaryAbelianPRank r ↥(M ⊓ centralizer ((Y : Subgroup G) : Set G)) ≤ 2)
    (hb4 : ∀ r : ℕ, elementaryAbelianPRank r ↥(M ⊓ centralizer ((A : Subgroup G) : Set G)) ≤ 2)
    (hPM : IsSylowOf p P M) (hAP : A ≤ P) :
    subgroupCenterTorsionBy P p ≠ ⊥ ∧ subgroupCenterTorsionBy P p ≤ A ∧
      elementaryAbelianPRank p ↥P = 2 := by
  have hfact := Fact.mk hp
  obtain ⟨hAcomm, hAexp⟩ := isElementaryAbelian_iff.1 hplane.isElementaryAbelian
  have hAcard : Nat.card ↥A = p ^ 2 := hplane.natCard
  have hAbot : A ≠ ⊥ := by
    intro h
    rw [h, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩] at hAcard
    have := Nat.one_lt_pow (a := p) (n := 2) two_ne_zero hp.one_lt
    omega
  have hPbot : P ≠ ⊥ := fun h => hAbot (le_bot_iff.1 (h ▸ hAP))
  set Z0 : Subgroup G := subgroupCenterTorsionBy P p with hZ0def
  have hZ0ne : Z0 ≠ ⊥ := subgroupCenterTorsionBy_ne_bot_of_isPGroup hp hPM.isPGroup hPbot
  have hZ0cent : Z0 ≤ centralizer ((P : Subgroup G) : Set G) :=
    subgroupCenterTorsionBy_le_centralizer
  have hZ0P : Z0 ≤ P := subgroupCenterTorsionBy_le
  have hsupEA : IsElementaryAbelian p (A ⊔ Z0) := by
    have hA' : IsElementaryAbelian p (A.subgroupOf P) :=
      isElementaryAbelian_iff_isElementaryAbelianSubgroup.2
        ((isElementaryAbelian_iff_isElementaryAbelianSubgroup.1
          hplane.isElementaryAbelian).comap P.subtype_injective)
    have hZ' : IsElementaryAbelian p (centerTorsionBy ↥P p) :=
      isElementaryAbelian_iff.2 ⟨inferInstance, fun x hx => pow_eq_one_of_mem_centerTorsionBy hx⟩
    have h := (hA'.sup_of_le_center hZ' (centerTorsionBy_le_center p)).map_subtype (H := P)
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAP,
      ← subgroupCenterTorsionBy_eq_map] at h
  have hsupLe : A ⊔ Z0 ≤ M ⊓ centralizer ((A : Subgroup G) : Set G) := by
    refine sup_le (le_inf hAM ?_) (le_inf (hZ0P.trans hPM.le) ?_)
    · exact hplane.isElementaryAbelian.le_centralizer le_rfl
    · exact hZ0cent.trans (Subgroup.centralizer_le hAP)
  obtain ⟨d, hd⟩ := hsupEA.isPGroup.exists_card_eq
  have hd2 : d ≤ 2 :=
    le_trans (hsupEA.le_elementaryAbelianPRank hp hd hsupLe) (hb4 p)
  have h2d : 2 ≤ d := by
    have hdvd : p ^ 2 ∣ p ^ d := by
      rw [← hAcard, ← hd]; exact Subgroup.card_dvd_of_le le_sup_left
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
  have hdeq : d = 2 := le_antisymm hd2 h2d
  have hsupA : A = A ⊔ Z0 := by
    refine Subgroup.eq_of_le_of_card_ge le_sup_left ?_
    rw [hd, hdeq, hAcard]
  have hZ0A : Z0 ≤ A := hsupA ▸ le_sup_right
  refine ⟨hZ0ne, hZ0A, le_antisymm ?_ ?_⟩
  · have : Nontrivial ↥Z0 := (Subgroup.nontrivial_iff_ne_bot Z0).2 hZ0ne
    obtain ⟨z, hz, hz1⟩ := Z0.exists_ne_one_of_nontrivial
    have hzp : z ^ p = 1 := (mem_subgroupCenterTorsionBy.1 hz).2.2
    have hzord : orderOf z = p := orderOf_eq_prime hzp hz1
    have hYle : Subgroup.zpowers z ≤ A := (Subgroup.zpowers_le).2 (hZ0A hz)
    have hYcard : Nat.card ↥(Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzord]
    have hPle : P ≤ M ⊓ centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      refine le_inf hPM.le ?_
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ((mem_subgroupCenterTorsionBy.1 hz).2.1 x hx).symm
    exact le_trans (elementaryAbelianPRank_le_of_le hp.one_lt hPle)
      (hb1 _ hYle hYcard p)
  · exact hplane.isElementaryAbelian.le_elementaryAbelianPRank hp hAcard hAP

theorem alphaCoreOf_le_inf_centralizer {p : ℕ} {M A : Subgroup G} (hp : p.Prime)
    (hplane : IsPlaneAt p A) (hAM : A ≤ M) (hpα : p ∉ alphaPrimes ↥M)
    (hb3 : ∀ Y ≤ A, Nat.card ↥Y = p →
      alphaCoreOf M ⊓ centralizer ((Y : Subgroup G) : Set G) ≤
        M ⊓ centralizer ((A : Subgroup G) : Set G))
    (hsolv : Group.IsSolvable ↥M) :
    alphaCoreOf M ≤ M ⊓ centralizer ((A : Subgroup G) : Set G) := by
  have hfact := Fact.mk hp
  obtain ⟨hAcomm, hAexp⟩ := isElementaryAbelian_iff.1 hplane.isElementaryAbelian
  have hnormal : (alphaCore ↥M).Normal := alphaCore_normal ↥M
  set A' : Subgroup ↥M := A.subgroupOf M with hA'def
  have hA'card : Nat.card ↥A' = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hplane.natCard]
  have hA'exp : ∀ a : ↥A', a ^ p = 1 := by
    intro a
    refine Subtype.ext (Subtype.ext ?_)
    exact hAexp _ a.2
  have hpB : ¬ p ∣ Nat.card ↥(alphaCore ↥M) := by
    intro hdvd
    exact hpα (isPiSubgroup_iff.1 (isPiSubgroup_alphaCore ↥M) p
      (Nat.mem_primeFactors.2 ⟨hp, hdvd, Nat.card_pos.ne'⟩))
  let ρ : ↥A' →* MulAut ↥(alphaCore ↥M) :=
    (MulAut.conjNormal (H := alphaCore ↥M)).comp A'.subtype
  have hgen : ⨆ (a : ↥A') (_ : a ≠ 1), autFixedSubgroup (ρ a) = ⊤ :=
    iSup_autFixedSubgroup_eq_top hp hA'card hA'exp ρ hpB
  let f : ↥(alphaCore ↥M) →* G := M.subtype.comp (alphaCore ↥M).subtype
  have hfmem : ∀ w : ↥(alphaCore ↥M), f w ∈ alphaCoreOf M := by
    intro w
    exact Subgroup.mem_map.2 ⟨w.1, w.2, rfl⟩
  have key : ∀ a : ↥A', a ≠ 1 →
      autFixedSubgroup (ρ a) ≤ Subgroup.comap f (M ⊓ centralizer ((A : Subgroup G) : Set G)) := by
    intro a ha
    have hgA : ((a : ↥M) : G) ∈ A := a.2
    have hg1 : ((a : ↥M) : G) ≠ 1 := by
      intro h
      exact ha (Subtype.ext (Subtype.ext h))
    have hgord : orderOf ((a : ↥M) : G) = p := orderOf_eq_prime (hAexp _ hgA) hg1
    have hYle : Subgroup.zpowers ((a : ↥M) : G) ≤ A := (Subgroup.zpowers_le).2 hgA
    have hYcard : Nat.card ↥(Subgroup.zpowers ((a : ↥M) : G)) = p := by
      rw [Nat.card_zpowers, hgord]
    intro w hw
    have hfix : ρ a w = w := mem_autFixedSubgroup.1 hw
    have hcomm : ((a : ↥M) : G) * f w * ((a : ↥M) : G)⁻¹ = f w := by
      have := congrArg (fun x : ↥(alphaCore ↥M) => ((x : ↥M) : G)) hfix
      simpa [ρ, f, MulAut.conjNormal_apply] using this
    have hmem : f w ∈ alphaCoreOf M ⊓
        centralizer ((Subgroup.zpowers ((a : ↥M) : G) : Subgroup G) : Set G) := by
      refine ⟨hfmem w, ?_⟩
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc ((a : ↥M) : G) * f w = ((a : ↥M) : G) * f w * ((a : ↥M) : G)⁻¹ * ((a : ↥M) : G) := by
            group
        _ = f w * ((a : ↥M) : G) := by rw [hcomm]
    exact Subgroup.mem_comap.2 (hb3 _ hYle hYcard hmem)
  have htop : (⊤ : Subgroup ↥(alphaCore ↥M)) ≤
      Subgroup.comap f (M ⊓ centralizer ((A : Subgroup G) : Set G)) := by
    rw [← hgen]
    exact iSup₂_le key
  intro b hb
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hb
  exact Subgroup.mem_comap.1 (htop (Subgroup.mem_top (⟨w, hw⟩ : ↥(alphaCore ↥M))))

theorem alphaPrimes_eq_empty_of_nonuniqueLine [IsSimpleGroup G] {M A : Subgroup G}
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hle : alphaCoreOf M ≤ M ⊓ centralizer ((A : Subgroup G) : Set G))
    (hb4 : ∀ r : ℕ, elementaryAbelianPRank r ↥(M ⊓ centralizer ((A : Subgroup G) : Set G)) ≤ 2) :
    alphaPrimes ↥M = ∅ := by
  have hsolvM : Group.IsSolvable ↥M := hsolv M hM.1
  refine Set.eq_empty_iff_forall_notMem.2 fun r hr => ?_
  have hrp : r.Prime := (mem_alphaPrimes.1 hr).1
  have hr3 : 3 ≤ elementaryAbelianPRank r ↥M := (mem_alphaPrimes.1 hr).2
  have hHall : IsHallSubgroup (alphaPrimes ↥M) (alphaCore ↥M) :=
    isHallSubgroup_alphaCore hna hodd hsolv hM
  have h1 : elementaryAbelianPRank r ↥M ≤ elementaryAbelianPRank r ↥(alphaCore ↥M) :=
    elementaryAbelianPRank_le_alphaCore hHall hr
  have h2 : elementaryAbelianPRank r ↥(alphaCore ↥M) = elementaryAbelianPRank r ↥(alphaCoreOf M) :=
    elementaryAbelianPRank_eq_of_mulEquiv hrp.one_lt
      ((alphaCore ↥M).equivMapOfInjective M.subtype M.subtype_injective)
  have h3 : elementaryAbelianPRank r ↥(alphaCoreOf M) ≤
      elementaryAbelianPRank r ↥(M ⊓ centralizer ((A : Subgroup G) : Set G)) :=
    elementaryAbelianPRank_le_of_le hrp.one_lt hle
  have := hb4 r
  omega

theorem isNilpotent_sigmaCore_of_alphaPrimes_eq_empty [IsSimpleGroup G] {M : Subgroup G}
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y) (hM : IsCoatom M)
    (hα : alphaPrimes ↥M = ∅) : Group.IsNilpotent ↥(sigmaCore M) := by
  have hsolvM : Group.IsSolvable ↥M := hsolv M hM.1
  have hoddM : Odd (Nat.card ↥M) := hodd.of_dvd_nat M.card_subgroup_dvd_card
  have hrank : ∀ r : ℕ, r.Prime → elementaryAbelianPRank r ↥(fittingRaw ↥M) ≤ 2 := by
    intro r hr
    have hM2 : elementaryAbelianPRank r ↥M ≤ 2 := by
      by_contra hcon
      have : r ∈ alphaPrimes ↥M := mem_alphaPrimes.2 ⟨hr, by omega⟩
      rw [hα] at this
      exact this
    exact le_trans (elementaryAbelianPRank_subgroup_le hr.one_lt _) hM2
  have hcomm : _root_.commutator ↥M ≤ fittingRaw ↥M := commutator_le_fittingRaw hoddM hrank
  have hS : (sigmaCore M).subgroupOf M ≤ fittingRaw ↥M :=
    le_trans (le_commutator_of_isHallSubgroup_sigmaPrimes hna hodd hsolv hM
      (isHallSubgroup_subgroupOf_sigmaCore hna hodd hsolv hM)) hcomm
  exact Group.nilpotent_of_mulEquiv (_h := isNilpotent_of_le_fittingRaw hS)
    (Subgroup.subgroupOfEquivOfLe (sigmaCore_le M))

theorem FTS_nonunique_lines_alpha_core_trivial
    (h₁ : Statements.FTS_nonunique_line_centralizer_bounds.{u}) :
    Statements.FTS_nonunique_lines_alpha_core_trivial.{u} := by
  intro G _ _ hG M A p hsetup
  have := hG.isSimpleGroup
  have hp : p.Prime := hsetup.prime
  obtain ⟨hb1, -, hb3, hb4⟩ := h₁ G hG M A p hsetup
  have hsolvM : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hsetup.isCoatom_M.1
  have hsylow : ∀ P : Subgroup G, IsSylowOf p P M → A ≤ P →
      subgroupCenterTorsionBy P p ≠ ⊥ ∧ subgroupCenterTorsionBy P p ≤ A ∧
        elementaryAbelianPRank p ↥P = 2 := fun P hPM hAP =>
    nonuniqueLine_sylow_clauses hp hsetup.isPlane hsetup.le hb1 hb4 hPM hAP
  have hpα : p ∉ alphaPrimes ↥M := by
    obtain ⟨P, hPM, hAP⟩ := exists_isSylowOf_ge hp hsetup.le
      hsetup.isPlane.isElementaryAbelian.isPGroup
    have h2 := (hsylow P hPM hAP).2.2
    rw [elementaryAbelianPRank_of_isSylowOf hp hPM] at h2
    intro hmem
    have := (mem_alphaPrimes.1 hmem).2
    omega
  have hle := alphaCoreOf_le_inf_centralizer hp hsetup.isPlane hsetup.le hpα (hb3 hpα) hsolvM
  have hα : alphaPrimes ↥M = ∅ :=
    alphaPrimes_eq_empty_of_nonuniqueLine hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hsetup.isCoatom_M hle hb4
  refine ⟨?_, ?_, ?_⟩
  · rw [alphaCoreOf, alphaCore_eq_bot_of_alphaPrimes_eq_empty ↥M hα, Subgroup.map_bot]
  · exact isNilpotent_sigmaCore_of_alphaPrimes_eq_empty hG.not_isMulCommutative hG.odd_natCard
      hG.isSolvable_of_ne_top hsetup.isCoatom_M hα
  · intro P hPM hAP Z0 hZ0
    obtain ⟨h1, h2, h3⟩ := hsylow P hPM hAP
    rw [eq_subgroupCenterTorsionBy hZ0]
    exact ⟨h1, h2, h3, hpα⟩

end

end CFSG.FeitThompson.Proofs
