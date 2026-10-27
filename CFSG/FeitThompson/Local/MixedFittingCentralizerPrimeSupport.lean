module

public import CFSG.FeitThompson.Definitions.LocalComplementaryPrimeConstraint
public import CFSG.FeitThompson.Definitions.RawFittingSubgroupConstruction
public import CFSG.FeitThompson.Local.ElementaryAbelianCubeInvariantPlane
public import CFSG.FeitThompson.Local.SmallRankLineInMaximalPlane
public import Mathlib.GroupTheory.Nilpotent
import CFSG.FeitThompson.Representations.ChiefActionKernelNormalQuotientLayers
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Foundations.FittingCharacteristicNilpotent
import CFSG.FeitThompson.Foundations.MinimalNormalInFittingCenter
import CFSG.FeitThompson.Foundations.NilpotentSylowNormalCharacteristic
import CFSG.FeitThompson.Foundations.FittingContainsCentralizerSolvable
import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
import CFSG.FeitThompson.Local.ConstrainedCentralizerCoreCoverage
import CFSG.FeitThompson.Local.CoprimeActionNilpotentSelfCentralizing
import CFSG.FeitThompson.Local.CoprimeActionSelfCentralizingFixedPGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G]

theorem normalizer_le_normalizer_centralizer (A : Subgroup G) :
    normalizer (A : Set G) ≤ normalizer ((centralizer (A : Set G) : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_iff_map_conj_eq.2 (map_centralizer_conj hg)

private theorem inf_center_ne_bot_aux {N : Type*} [Group N] {H : Subgroup N} [hH : H.Normal]
    (n : ℕ) (hn : H ⊓ Subgroup.upperCentralSeries N n ≠ ⊥) : H ⊓ Subgroup.center N ≠ ⊥ := by
  induction n with
  | zero => simp at hn
  | succ k ih =>
    by_cases hk : H ⊓ Subgroup.upperCentralSeries N k = ⊥
    · obtain ⟨x, hx, hx1⟩ := (Subgroup.nontrivial_iff_exists_ne_one _).1
        ((Subgroup.nontrivial_iff_ne_bot _).2 hn)
      intro hbot
      refine hx1 ?_
      have hxc : x ∈ Subgroup.center N := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h1 := Subgroup.mem_upperCentralSeries_succ_iff.1 hx.2 y
        rw [commutatorElement_def] at h1
        have h2 : x * y * x⁻¹ * y⁻¹ ∈ H := by
          have hc : y * x⁻¹ * y⁻¹ ∈ H := hH.conj_mem _ (H.inv_mem hx.1) y
          have he : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
          rw [he]; exact H.mul_mem hx.1 hc
        have hmem : x * y * x⁻¹ * y⁻¹ ∈ H ⊓ Subgroup.upperCentralSeries N k := ⟨h2, h1⟩
        rw [hk, Subgroup.mem_bot] at hmem
        exact (mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 hmem)).symm
      have hmem : x ∈ H ⊓ Subgroup.center N := ⟨hx.1, hxc⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    · exact ih hk

theorem inf_center_ne_bot_of_normal_of_isNilpotent {N : Type*} [Group N] [Group.IsNilpotent N]
    {H : Subgroup N} [H.Normal] (hH : H ≠ ⊥) : H ⊓ Subgroup.center N ≠ ⊥ := by
  obtain ⟨n, hn⟩ := (inferInstance : Group.IsNilpotent N)
  exact inf_center_ne_bot_aux n (by rw [hn, inf_top_eq]; exact hH)

def centreIn (X : Subgroup G) : Subgroup G := X ⊓ centralizer (X : Set G)

theorem centreIn_eq (X : Subgroup G) : centreIn X = X ⊓ centralizer (X : Set G) := (rfl)

theorem centreIn_eq_map_center (X : Subgroup G) :
    centreIn X = (Subgroup.center ↥X).map X.subtype :=
  (map_center_subtype_eq_inf_centralizer X).symm

theorem centreIn_le (X : Subgroup G) : centreIn X ≤ X := inf_le_left

theorem centreIn_le_centralizer (X : Subgroup G) : centreIn X ≤ centralizer (X : Set G) :=
  inf_le_right

theorem mem_centreIn_iff {X : Subgroup G} {x : G} :
    x ∈ centreIn X ↔ x ∈ X ∧ ∀ y ∈ X, y * x = x * y :=
  ⟨fun h => ⟨h.1, fun y hy => Subgroup.mem_centralizer_iff.1 h.2 y hy⟩,
    fun h => ⟨h.1, Subgroup.mem_centralizer_iff.2 h.2⟩⟩

variable [Finite G]

@[expose]
def pCoreIn (q : ℕ) (X : Subgroup G) : Subgroup G := (pCore q ↥X).map X.subtype

theorem pCoreIn_eq (q : ℕ) (X : Subgroup G) : pCoreIn q X = (pCore q ↥X).map X.subtype := (rfl)

theorem pCoreIn_le (q : ℕ) (X : Subgroup G) : pCoreIn q X ≤ X := Subgroup.map_subtype_le _

theorem isPGroup_pCoreIn {q : ℕ} (hq : q.Prime) (X : Subgroup G) : IsPGroup q ↥(pCoreIn q X) :=
  (isPGroup_pCore hq ↥X).map _

theorem le_normalizer_pCoreIn (q : ℕ) {X L : Subgroup G} (hL : L ≤ normalizer (X : Set G)) :
    L ≤ normalizer ((pCoreIn q X : Subgroup G) : Set G) :=
  le_normalizer_map_subtype_of_characteristic _ hL

theorem le_pCoreIn {q : ℕ} (hq : q.Prime) {X N : Subgroup G} (hNX : N ≤ X)
    (hnorm : X ≤ normalizer (N : Set G)) (hN : IsPGroup q ↥N) : N ≤ pCoreIn q X := by
  rw [pCoreIn_eq, pCore_eq_piCore]
  exact le_map_piCore_of_le_of_le_normalizer hNX hnorm ((isPiSubgroup_singleton_iff hq N).2 hN)

theorem pCoreIn_ne_bot_of_isMulCommutative {q : ℕ} (hq : q.Prime) {X : Subgroup G}
    (hab : IsMulCommutative ↥X) (hdvd : q ∣ Nat.card ↥X) : pCoreIn q X ≠ ⊥ := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) q hdvd
  have hyo : orderOf (y : G) = q := by rw [Subgroup.orderOf_coe, hy]
  have hyne : (y : G) ≠ 1 := fun hcon => by
    rw [hcon, orderOf_one] at hyo; exact hq.one_lt.ne hyo
  have hzle : Subgroup.zpowers (y : G) ≤ X := by rw [Subgroup.zpowers_le]; exact y.2
  have hzq : IsPGroup q ↥(Subgroup.zpowers (y : G)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  have hznorm : X ≤ normalizer ((Subgroup.zpowers (y : G) : Subgroup G) : Set G) := by
    refine (?_ : X ≤ centralizer _).trans (Subgroup.centralizer_le_normalizer _)
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have h2 := congrArg (fun w : ↥X => (w : G)) (hab.is_comm.comm ⟨g, hg⟩ (y ^ n))
    simpa using h2.symm
  intro hbot
  have hle := le_pCoreIn hq hzle hznorm hzq
  rw [hbot, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact hyne hle

omit [Finite G] in
theorem fixedPoints_conjOnNormalized {F : Subgroup G} {x : G}
    (hx : Subgroup.zpowers x ≤ normalizer (F : Set G)) :
    FixedPoints.subgroup (conjOnNormalized F hx).range ↥F
      = (F ⊓ centralizer ({x} : Set G)).subgroupOf F := by
  ext y
  rw [mem_fixedPoints_range_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro hcon
    refine ⟨y.2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    have h2 := congrArg (fun w : ↥F => (w : G)) (hcon ⟨x, Subgroup.mem_zpowers x⟩)
    simp only [conjOnNormalized_apply_coe] at h2
    rw [hz]
    exact mul_inv_eq_iff_eq_mul.1 h2
  · rintro ⟨-, hyc⟩ a
    have hcomm : Commute x (y : G) :=
      Subgroup.mem_centralizer_iff.1 hyc x (Set.mem_singleton x)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 a.2
    ext
    rw [conjOnNormalized_apply_coe, ← hn, mul_inv_eq_iff_eq_mul, (hcomm.zpow_left n).eq]

theorem le_centralizer_of_coprime_of_isNilpotent {F : Subgroup G} {x : G}
    (hx : Subgroup.zpowers x ≤ normalizer (F : Set G)) [Group.IsNilpotent ↥F]
    (hcop : (orderOf x).Coprime (Nat.card ↥F))
    (hself : F ⊓ centralizer ((F ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G)
      ≤ F ⊓ centralizer ({x} : Set G)) :
    F ≤ centralizer ({x} : Set G) := by
  have hcopA : (Nat.card ↥(Subgroup.zpowers x)).Coprime (Nat.card ↥F) := by
    rwa [Nat.card_zpowers]
  have hselfF : centralizer ((FixedPoints.subgroup (conjOnNormalized F hx).range ↥F :
      Subgroup ↥F) : Set ↥F) ≤ FixedPoints.subgroup (conjOnNormalized F hx).range ↥F := by
    rw [fixedPoints_conjOnNormalized hx]
    intro w hw
    rw [Subgroup.mem_subgroupOf]
    refine hself (Subgroup.mem_inf.2 ⟨w.2, Subgroup.mem_centralizer_iff.2 fun c hc => ?_⟩)
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hw
      (⟨c, (Subgroup.mem_inf.1 hc).1⟩ : ↥F) (Subgroup.mem_subgroupOf.2 hc))
  have htop := fixedPoints_range_eq_top_of_coprime_of_isNilpotent
    (conjOnNormalized F hx) hcopA hselfF
  rw [fixedPoints_conjOnNormalized hx] at htop
  intro y hy
  have hmem : (⟨y, hy⟩ : ↥F) ∈ (F ⊓ centralizer ({x} : Set G)).subgroupOf F :=
    htop ▸ Subgroup.mem_top _
  exact (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).2

def mixedFitting (M : Subgroup G) : Subgroup G := (fittingRaw ↥M).map M.subtype

theorem mixedFitting_eq (M : Subgroup G) :
    mixedFitting M = (fittingRaw ↥M).map M.subtype := (rfl)

theorem mixedFitting_le (M : Subgroup G) : mixedFitting M ≤ M := map_fittingRaw_subtype_le M

instance isNilpotent_mixedFitting (M : Subgroup G) : Group.IsNilpotent ↥(mixedFitting M) :=
  Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective)

theorem le_normalizer_mixedFitting (M : Subgroup G) :
    M ≤ normalizer ((mixedFitting M : Subgroup G) : Set G) :=
  le_normalizer_map_subtype_of_characteristic _ Subgroup.le_normalizer

theorem mem_mixedFitting_of_mem_of_le_centralizer {M : Subgroup G} [Group.IsSolvable ↥M] {x : G}
    (hxM : x ∈ M) (hx : mixedFitting M ≤ centralizer ({x} : Set G)) : x ∈ mixedFitting M := by
  have hcent : (⟨x, hxM⟩ : ↥M) ∈ centralizer ((fittingRaw ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    refine Subtype.ext ?_
    have hyF : (y : G) ∈ mixedFitting M := ⟨y, hy, rfl⟩
    exact (Subgroup.mem_centralizer_iff.1 (hx hyF) x (Set.mem_singleton x)).symm
  exact ⟨_, centralizer_fittingRaw_le_fittingRaw ↥M hcent, rfl⟩

def mixedFittingCentralizer (M E : Subgroup G) : Subgroup G :=
  mixedFitting M ⊓ centralizer (E : Set G)

theorem mixedFittingCentralizer_eq (M E : Subgroup G) :
    mixedFittingCentralizer M E = mixedFitting M ⊓ centralizer (E : Set G) := (rfl)

theorem mixedFittingCentralizer_le (M E : Subgroup G) :
    mixedFittingCentralizer M E ≤ mixedFitting M := inf_le_left

theorem mixedFittingCentralizer_le_centralizer (M E : Subgroup G) :
    mixedFittingCentralizer M E ≤ centralizer (E : Set G) := inf_le_right

theorem isMulCommutative_centreIn (X : Subgroup G) : IsMulCommutative ↥(centreIn X) := by
  refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
  push_cast
  exact Subgroup.mem_centralizer_iff.1 (centreIn_le_centralizer X y.2) (x : G)
    (centreIn_le X x.2)

theorem le_normalizer_centreIn_mixedFitting (M : Subgroup G) :
    M ≤ normalizer ((centreIn (mixedFitting M) : Subgroup G) : Set G) :=
  le_normalizer_inf (le_normalizer_mixedFitting M)
    ((le_normalizer_mixedFitting M).trans (normalizer_le_normalizer_centralizer _))

theorem le_normalizer_pCoreIn_centreIn_mixedFitting (q : ℕ) (M : Subgroup G) :
    M ≤ normalizer ((pCoreIn q (centreIn (mixedFitting M)) : Subgroup G) : Set G) :=
  le_normalizer_pCoreIn q (le_normalizer_centreIn_mixedFitting M)

structure IsMixedFittingSetup (p : ℕ) (M E : Subgroup G) : Prop where
  isCoatom : IsCoatom M
  isSolvable : Group.IsSolvable ↥M
  prime : p.Prime
  isElementaryAbelian : IsElementaryAbelian p E
  le : E ≤ mixedFitting M
  three_mem_ranks : 3 ∈ elementaryAbelianRanks p ↥E
  not_isPGroup : ¬ IsPGroup p ↥(mixedFitting M)

namespace IsMixedFittingSetup

variable {p : ℕ} {M E : Subgroup G} (h : IsMixedFittingSetup p M E)

include h

theorem ne_top : M ≠ ⊤ := h.isCoatom.1

theorem le_mixedFittingCentralizer : E ≤ mixedFittingCentralizer M E :=
  le_inf h.le (h.isElementaryAbelian.le_centralizer le_rfl)

theorem centreIn_le_mixedFittingCentralizer :
    centreIn (mixedFitting M) ≤ mixedFittingCentralizer M E :=
  le_inf (centreIn_le _) ((centreIn_le_centralizer _).trans (Subgroup.centralizer_le h.le))

theorem pCoreIn_centreIn_le_mixedFittingCentralizer (q : ℕ) :
    pCoreIn q (centreIn (mixedFitting M)) ≤ mixedFittingCentralizer M E :=
  (pCoreIn_le q _).trans h.centreIn_le_mixedFittingCentralizer

theorem pow_three_dvd_natCard : p ^ 3 ∣ Nat.card ↥E := by
  obtain ⟨H, hH⟩ := exists_subgroup_card_eq_of_mem_elementaryAbelianRanks h.three_mem_ranks
  exact hH ▸ Subgroup.card_subgroup_dvd_card H

theorem mem_primeFactors_mixedFitting : p ∈ (Nat.card ↥(mixedFitting M)).primeFactors := by
  refine Nat.mem_primeFactors.2 ⟨h.prime, ?_, Nat.card_pos.ne'⟩
  exact dvd_trans (dvd_trans (dvd_pow_self p (by norm_num)) h.pow_three_dvd_natCard)
    (Subgroup.card_dvd_of_le h.le)

theorem exists_mem_primeFactors_ne :
    ∃ q ∈ (Nat.card ↥(mixedFitting M)).primeFactors, q ≠ p := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  refine h.not_isPGroup ((isPGroup_iff_primeFactors_card_subset h.prime.ne_zero).2 fun q hq => ?_)
  rw [hcon q hq, h.prime.primeFactors]
  simp

theorem two_le_card_primeFactors : 2 ≤ (Nat.card ↥(mixedFitting M)).primeFactors.card := by
  obtain ⟨q, hq, hqp⟩ := h.exists_mem_primeFactors_ne
  have hsub : ({p, q} : Finset ℕ) ⊆ (Nat.card ↥(mixedFitting M)).primeFactors := by
    intro r hr
    rcases Finset.mem_insert.1 hr with rfl | hr
    · exact h.mem_primeFactors_mixedFitting
    · rw [Finset.mem_singleton] at hr; exact hr ▸ hq
  calc 2 = ({p, q} : Finset ℕ).card := by rw [Finset.card_pair (Ne.symm hqp)]
    _ ≤ _ := Finset.card_le_card hsub

omit h in
theorem dvd_natCard_centreIn {q : ℕ} (hq : q.Prime)
    (hqF : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors) :
    q ∣ Nat.card ↥(centreIn (mixedFitting M)) := by
  have : Fact q.Prime := ⟨hq⟩
  set F := mixedFitting M with hF
  obtain Q := (default : Sylow q ↥F)
  have hQcard : Nat.card ↥(Q : Subgroup ↥F) = q ^ (Nat.card ↥F).factorization q :=
    Q.card_eq_multiplicity
  have hQne : (Q : Subgroup ↥F) ≠ ⊥ := by
    intro hb
    rw [hb, Nat.card_eq_one_iff_unique.2 ⟨inferInstance, inferInstance⟩] at hQcard
    have hpos : 0 < (Nat.card ↥F).factorization q :=
      hq.factorization_pos_of_dvd Nat.card_pos.ne' (Nat.dvd_of_mem_primeFactors hqF)
    exact absurd hQcard.symm (Nat.one_lt_pow hpos.ne' hq.one_lt).ne'
  have hQnormal : (Q : Subgroup ↥F).Normal := sylow_normal_of_isNilpotent Q
  have hinf : (Q : Subgroup ↥F) ⊓ Subgroup.center ↥F ≠ ⊥ :=
    inf_center_ne_bot_of_normal_of_isNilpotent hQne
  have hqZ : q ∣ Nat.card ↥(Subgroup.center ↥F) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (IsPGroup.to_le Q.2 (inf_le_left :
      (Q : Subgroup ↥F) ⊓ Subgroup.center ↥F ≤ (Q : Subgroup ↥F)))
    have hn1 : 1 ≤ n := by
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · rw [pow_zero, Subgroup.card_eq_one] at hn; exact absurd hn hinf
      · exact hpos
    refine dvd_trans ?_ (Subgroup.card_dvd_of_le (inf_le_right :
      (Q : Subgroup ↥F) ⊓ Subgroup.center ↥F ≤ Subgroup.center ↥F))
    rw [hn]; exact dvd_pow_self q (by omega)
  have hcard : Nat.card ↥(centreIn F) = Nat.card ↥(Subgroup.center ↥F) := by
    rw [centreIn_eq_map_center]
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective _ F.subtype F.subtype_injective).toEquiv).symm
  exact hcard ▸ hqZ

theorem pCoreIn_centreIn_ne_bot {q : ℕ} (hq : q.Prime)
    (hqF : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors) :
    pCoreIn q (centreIn (mixedFitting M)) ≠ ⊥ :=
  pCoreIn_ne_bot_of_isMulCommutative hq (isMulCommutative_centreIn (mixedFitting M))
    (dvd_natCard_centreIn (M := M) hq hqF)

theorem pCoreIn_centreIn_le_pCoreIn_mixedFittingCentralizer {q : ℕ} (hq : q.Prime) :
    pCoreIn q (centreIn (mixedFitting M)) ≤ pCoreIn q (mixedFittingCentralizer M E) := by
  refine le_pCoreIn hq (h.pCoreIn_centreIn_le_mixedFittingCentralizer q) ?_
    (isPGroup_pCoreIn hq _)
  refine (?_ : mixedFittingCentralizer M E ≤ centralizer _).trans
    (Subgroup.centralizer_le_normalizer _)
  refine (mixedFittingCentralizer_le M E).trans
    (le_centralizer_of_le_centralizer (Y := pCoreIn q (centreIn (mixedFitting M))) ?_)
  exact (pCoreIn_le q _).trans (centreIn_le_centralizer (mixedFitting M))

theorem le_centreIn_mixedFittingCentralizer : E ≤ centreIn (mixedFittingCentralizer M E) :=
  le_inf h.le_mixedFittingCentralizer
    (le_centralizer_of_le_centralizer (mixedFittingCentralizer_le_centralizer M E))

theorem normalizer_pCoreIn_centreIn_eq [IsSimpleGroup G] {q : ℕ} (hq : q.Prime)
    (hqF : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors) :
    normalizer ((pCoreIn q (centreIn (mixedFitting M)) : Subgroup G) : Set G) = M := by
  set Z := pCoreIn q (centreIn (mixedFitting M)) with hZ
  have hZM : Z ≤ M :=
    (pCoreIn_le q _).trans ((centreIn_le _).trans (mixedFitting_le M))
  have hbot : ⊥ < Z := lt_of_le_of_ne bot_le (Ne.symm (h.pCoreIn_centreIn_ne_bot hq hqF))
  have htop : Z < ⊤ := lt_of_le_of_lt hZM (lt_of_le_of_ne le_top h.ne_top)
  have hlt : normalizer (Z : Set G) < ⊤ := normalizer_lt_top_of_isSimpleGroup hbot htop
  rcases eq_or_lt_of_le (le_normalizer_pCoreIn_centreIn_mixedFitting q M) with heq | hlt2
  · exact heq.symm
  · exact absurd (h.isCoatom.2 _ hlt2) hlt.ne

omit h in
theorem centralizer_le_centralizer_pCoreIn (q : ℕ) :
    centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G)
      ≤ centralizer ((pCoreIn q (mixedFittingCentralizer M E) : Subgroup G) : Set G) :=
  Subgroup.centralizer_le fun _ hx => pCoreIn_le q _ hx

theorem centralizer_pCoreIn_le [IsSimpleGroup G] {q : ℕ} (hq : q.Prime)
    (hqF : q ∈ (Nat.card ↥(mixedFitting M)).primeFactors) :
    centralizer ((pCoreIn q (mixedFittingCentralizer M E) : Subgroup G) : Set G) ≤ M := by
  have hZT : (pCoreIn q (centreIn (mixedFitting M)) : Set G)
      ⊆ (pCoreIn q (mixedFittingCentralizer M E) : Set G) :=
    fun _ hx => h.pCoreIn_centreIn_le_pCoreIn_mixedFittingCentralizer hq hx
  calc centralizer ((pCoreIn q (mixedFittingCentralizer M E) : Subgroup G) : Set G)
      ≤ centralizer ((pCoreIn q (centreIn (mixedFitting M)) : Subgroup G) : Set G) :=
        Subgroup.centralizer_le hZT
    _ ≤ normalizer ((pCoreIn q (centreIn (mixedFitting M)) : Subgroup G) : Set G) :=
        Subgroup.centralizer_le_normalizer _
    _ = M := h.normalizer_pCoreIn_centreIn_eq hq hqF

theorem centralizer_mixedFittingCentralizer_le [IsSimpleGroup G] :
    centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G) ≤ M := by
  obtain ⟨q, hq, -⟩ := h.exists_mem_primeFactors_ne
  exact (centralizer_le_centralizer_pCoreIn (M := M) (E := E) q).trans
    (h.centralizer_pCoreIn_le (Nat.prime_of_mem_primeFactors hq) hq)

theorem primeFactors_mixedFittingCentralizer :
    (Nat.card ↥(mixedFittingCentralizer M E)).primeFactors
      = (Nat.card ↥(mixedFitting M)).primeFactors := by
  refine Finset.Subset.antisymm (Nat.primeFactors_mono
    (Subgroup.card_dvd_of_le (mixedFittingCentralizer_le M E)) Nat.card_pos.ne') fun q hq => ?_
  have hqp := Nat.prime_of_mem_primeFactors hq
  have : Fact q.Prime := ⟨hqp⟩
  refine Nat.mem_primeFactors.2 ⟨hqp, ?_, Nat.card_pos.ne'⟩
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le
    (h.pCoreIn_centreIn_le_mixedFittingCentralizer q))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 (isPGroup_pCoreIn hqp (centreIn (mixedFitting M)))
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · rw [pow_zero, Subgroup.card_eq_one] at hn
      exact absurd hn (h.pCoreIn_centreIn_ne_bot hqp hq)
    · exact hpos
  rw [hn]
  exact dvd_pow_self q (by omega)

theorem mem_mixedFitting_of_mem_centralizer_of_coprime {x : G} (hxM : x ∈ M)
    (hxT : x ∈ centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G))
    (hcop : (orderOf x).Coprime (Nat.card ↥(mixedFitting M))) :
    x ∈ mixedFitting M := by
  have := h.isSolvable
  have hxn : Subgroup.zpowers x ≤ normalizer ((mixedFitting M : Subgroup G) : Set G) := by
    rw [Subgroup.zpowers_le]; exact le_normalizer_mixedFitting M hxM
  have hTC : mixedFittingCentralizer M E ≤ mixedFitting M ⊓ centralizer ({x} : Set G) := by
    refine le_inf (mixedFittingCentralizer_le M E) fun t ht => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (Subgroup.mem_centralizer_iff.1 hxT t ht).symm
  have hself : mixedFitting M ⊓ centralizer
      ((mixedFitting M ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G)
      ≤ mixedFitting M ⊓ centralizer ({x} : Set G) := by
    refine le_trans (inf_le_inf_left (mixedFitting M)
      (Subgroup.centralizer_le fun y hy => hTC hy)) ?_
    refine le_trans (inf_le_inf_left (mixedFitting M) (Subgroup.centralizer_le
      fun y hy => h.le_mixedFittingCentralizer hy)) ?_
    exact le_trans (le_of_eq (mixedFittingCentralizer_eq M E).symm) hTC
  exact mem_mixedFitting_of_mem_of_le_centralizer hxM
    (le_centralizer_of_coprime_of_isNilpotent hxn hcop hself)

theorem mem_primeFactors_mixedFitting_of_mem_primeFactors_centralizer [IsSimpleGroup G] {r : ℕ}
    (hr : r ∈ (Nat.card
      ↥(centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G))).primeFactors) :
    r ∈ (Nat.card ↥(mixedFitting M)).primeFactors := by
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have : Fact r.Prime := ⟨hrp⟩
  set C := centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G) with hC
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) r
    (Nat.dvd_of_mem_primeFactors hr)
  have hyo : orderOf (y : G) = r := by rw [Subgroup.orderOf_coe, hy]
  by_contra hrF
  have hcop : (orderOf (y : G)).Coprime (Nat.card ↥(mixedFitting M)) := by
    rw [hyo]
    exact (Nat.Prime.coprime_iff_not_dvd hrp).2 fun hdvd =>
      hrF (Nat.mem_primeFactors.2 ⟨hrp, hdvd, Nat.card_pos.ne'⟩)
  have hyF := h.mem_mixedFitting_of_mem_centralizer_of_coprime
    (h.centralizer_mixedFittingCentralizer_le y.2) y.2 hcop
  refine hrF (Nat.mem_primeFactors.2 ⟨hrp, ?_, Nat.card_pos.ne'⟩)
  have hzle : Subgroup.zpowers (y : G) ≤ mixedFitting M := by
    rw [Subgroup.zpowers_le]; exact hyF
  refine dvd_trans ?_ (Subgroup.card_dvd_of_le hzle)
  rw [Nat.card_zpowers, hyo]

theorem isPiSubgroup_centralizer_mixedFittingCentralizer [IsSimpleGroup G] :
    IsPiSubgroup (subgroupPrimeSupport (mixedFitting M))
      (centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G)) := by
  rw [isPiSubgroup_iff]
  intro r hr
  exact mem_subgroupPrimeSupport_iff.2
    (h.mem_primeFactors_mixedFitting_of_mem_primeFactors_centralizer hr)

theorem piCore_centralizer_eq_bot [IsSimpleGroup G] :
    piCore (subgroupPrimeSupportCompl (mixedFitting M))
      ↥(centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G)) = ⊥ := by
  set C := centralizer ((mixedFittingCentralizer M E : Subgroup G) : Set G) with hC
  refine le_bot_iff.1 (piCore_le fun N _ hN => ?_)
  have hNC : IsPiSubgroup (subgroupPrimeSupport (mixedFitting M)) N := by
    rw [← isPiSubgroup_map_subtype_iff]
    exact h.isPiSubgroup_centralizer_mixedFittingCentralizer.of_le (Subgroup.map_subtype_le N)
  have hcard : (Nat.card ↥N).primeFactors = ∅ := by
    ext s
    simp only [Finset.notMem_empty, iff_false]
    exact fun hs => (mem_subgroupPrimeSupportCompl_iff.1 (isPiSubgroup_iff.1 hN s hs)).2
      (isPiSubgroup_iff.1 hNC s hs)
  rcases Nat.primeFactors_eq_empty.1 hcard with hz | ho
  · exact absurd hz Nat.card_pos.ne'
  · exact le_of_eq (Subgroup.card_eq_one.1 ho)

end IsMixedFittingSetup

end

end CFSG.FeitThompson
