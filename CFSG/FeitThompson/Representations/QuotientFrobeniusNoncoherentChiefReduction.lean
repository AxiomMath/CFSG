module

public import CFSG.FeitThompson.Representations.NilpotentNormalSectionCoherenceDescent
public import CFSG.FeitThompson.Representations.QuotientFrobeniusLinearLayerCoherence
public import CFSG.FeitThompson.Local.ChiefFactorIrreducibleModule
import CFSG.FeitThompson.Representations.EqualDegreeDifferenceSaturatesAntirealBlocks
import CFSG.FeitThompson.Local.NilpotentFrobeniusAbelianizationPrimePower
import CFSG.FeitThompson.Local.SmallFrobeniusCyclicKernel
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.PGroupCyclicAbelianizationCyclic
import CFSG.FeitThompson.Local.NilpotentAbelianizationSamePrimes
import CFSG.FeitThompson.Local.FixedFreeComplementNilpotentSections
import CFSG.FeitThompson.Representations.SolvableFrobeniusKernelInducedIndexDegree
import CFSG.FeitThompson.Foundations.MinimalNormalSolvableElemAbelian
import CFSG.FeitThompson.Foundations.QuotientOrderByNormal
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace QuotientFrobeniusNoncoherent

open NormalInducedFamily NilpotentSectionCoherence CentralSectionCoherence WeightedFeitExtension

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
open FrobeniusQuotientLayer (FixesOnlyCommutatorCoset fixedPointFree_conjAbelianizationAut
  conjAbelianizationAut_of_eq_self_iff abelianization_of_eq_one_iff
  isCoherent_kerLayerIndFam_commutator)
open NormalLinearInduced (coe_mem_commutator_iff)
open Subgroup QuotientGroup
open scoped Pointwise

variable {L : Type*} [Group L] {K E : Subgroup L}

theorem mem_commutator_of_fixesOnlyCommutatorCoset [K.Normal]
    (hfree : FixesOnlyCommutatorCoset K E) {u : L} (hu : u ∈ E) (hu1 : u ≠ 1) {k : L}
    (hk : k ∈ K) (hmem : k⁻¹ * (u⁻¹ * k * u) ∈ (⁅K, K⁆ : Subgroup L)) :
    k ∈ (⁅K, K⁆ : Subgroup L) := by
  have h := fixedPointFree_conjAbelianizationAut hfree hu hu1 (Abelianization.of ⟨k, hk⟩)
    ((conjAbelianizationAut_of_eq_self_iff u hk).2 hmem)
  rw [abelianization_of_eq_one_iff] at h
  simpa using (coe_mem_commutator_iff (K := K)).2 h

theorem inf_centralizer_quotientFactor_eq_bot [K.Normal] (hfree : FixesOnlyCommutatorCoset K E)
    {v : L ⧸ (⁅K, K⁆ : Subgroup L)} (hv : v ∈ quotientFactor E ⁅K, K⁆) (hv1 : v ≠ 1) :
    quotientFactor K (⁅K, K⁆ : Subgroup L) ⊓ Subgroup.centralizer {v} = ⊥ := by
  obtain ⟨u, huE, rfl⟩ := (mem_quotientFactor E _).1 hv
  have hu1 : u ≠ 1 := by rintro rfl; exact hv1 (by simp)
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxK, hxC⟩
  obtain ⟨k, hkK, rfl⟩ := (mem_quotientFactor K _).1 hxK
  have hcomm : ((k * u : L) : L ⧸ (⁅K, K⁆ : Subgroup L)) = ((u * k : L) : L ⧸ ⁅K, K⁆) := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 hxC
    simpa using h
  have hmem : k⁻¹ * (u⁻¹ * k * u) ∈ (⁅K, K⁆ : Subgroup L) := by
    have h := QuotientGroup.eq.1 hcomm
    have he : (k * u)⁻¹ * (u * k) = (k⁻¹ * (u⁻¹ * k * u))⁻¹ := by group
    rw [he] at h
    simpa using (⁅K, K⁆ : Subgroup L).inv_mem h
  exact (QuotientGroup.eq_one_iff _).2
    (mem_commutator_of_fixesOnlyCommutatorCoset hfree huE hu1 hkK hmem)

theorem natCard_quotientFactor_eq [K.Normal] (hinf : K ⊓ E = ⊥) :
    Nat.card ↥(quotientFactor E (⁅K, K⁆ : Subgroup L)) = Nat.card ↥E := by
  have hker : ((mk' (⁅K, K⁆ : Subgroup L)).comp E.subtype).ker = ⊥ := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, mk'_apply, eq_one_iff,
      coe_subtype, Subgroup.mem_bot]
    constructor
    · intro hx
      have hm : (x : L) ∈ K ⊓ E := ⟨(Subgroup.commutator_le_self K) hx, x.2⟩
      rw [hinf] at hm
      exact Subtype.ext (by simpa using hm)
    · intro hx; subst hx; simp
  have hinj : Function.Injective ((mk' (⁅K, K⁆ : Subgroup L)).comp E.subtype) :=
    (MonoidHom.ker_eq_bot_iff _).1 hker
  rw [← range_mk'_comp_subtype_eq_quotientFactor E (⁅K, K⁆ : Subgroup L),
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]

theorem eq_bot_of_normal_lt_quotientFactor_commutator_self [Finite L] [K.Normal]
    (hodd : Odd (Nat.card L)) (hinf : K ⊓ E = ⊥) (hfree : FixesOnlyCommutatorCoset K E)
    (hbd : (⁅K, K⁆ : Subgroup L).relIndex K ≤ 4 * Nat.card ↥E ^ 2 + 1)
    (J : Subgroup (L ⧸ (⁅K, K⁆ : Subgroup L))) (hJ : J.Normal)
    (hJlt : J < quotientFactor K ⁅K, K⁆) : J = ⊥ := by
  have hcomm : (⁅quotientFactor K (⁅K, K⁆ : Subgroup L),
      quotientFactor K (⁅K, K⁆ : Subgroup L)⁆ : Subgroup (L ⧸ (⁅K, K⁆ : Subgroup L))) = ⊥ :=
    Subgroup.commutator_self_eq_bot_iff.2 inferInstance
  have : Group.IsNilpotent ↥(quotientFactor K (⁅K, K⁆ : Subgroup L)) :=
    isNilpotent_of_isMulCommutative _
  have hbd' : (⁅quotientFactor K (⁅K, K⁆ : Subgroup L),
        quotientFactor K (⁅K, K⁆ : Subgroup L)⁆).relIndex (quotientFactor K ⁅K, K⁆)
      ≤ 4 * Nat.card ↥(quotientFactor E (⁅K, K⁆ : Subgroup L)) ^ 2 + 1 := by
    rw [hcomm, Subgroup.relIndex_bot_left, natCard_quotientFactor_eq hinf,
      natCard_quotientFactor_commutator_self, ← relIndex_commutator_self_eq_index_commutator]
    exact hbd
  by_contra hJne
  have _ := hJ
  exact not_lt_lt_commutator_self (H := quotientFactor K (⁅K, K⁆ : Subgroup L))
    (E := quotientFactor E (⁅K, K⁆ : Subgroup L)) (odd_natCard_quotient _ hodd)
    (fun v hv hv1 => inf_centralizer_quotientFactor_eq_bot hfree hv hv1) hbd' J
    (hcomm ▸ lt_of_le_of_ne bot_le (Ne.symm hJne)) hJlt

theorem exists_prime_pow_natCard_of_relIndex_le [Finite L] [K.Normal] [Group.IsNilpotent ↥K]
    (hodd : Odd (Nat.card L)) (hK : K ≠ ⊥) (hinf : K ⊓ E = ⊥)
    (hfree : FixesOnlyCommutatorCoset K E)
    (hbd : (⁅K, K⁆ : Subgroup L).relIndex K ≤ 4 * Nat.card ↥E ^ 2 + 1) :
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥K = p ^ a ∧
      (⁅K, K⁆ : Subgroup L).relIndex K = p ^ d ∧
      Nonempty (↥(quotientFactor K (⁅K, K⁆ : Subgroup L)) ≃* Multiplicative (Fin d → ZMod p)) := by
  have hnb : quotientFactor K (⁅K, K⁆ : Subgroup L) ≠ ⊥ :=
    quotientFactor_ne_bot K _ (commutator_self_lt_self_of_isNilpotent hK)
  obtain ⟨p, d, hp, hd, ⟨φ⟩⟩ :=
    exists_prime_nonempty_mulEquiv_of_isSolvable_of_forall_normal_lt_eq_bot hnb
      fun J hJ hJlt =>
        eq_bot_of_normal_lt_quotientFactor_commutator_self (E := E) hodd hinf hfree hbd J hJ hJlt
  have hfact : Fact p.Prime := ⟨hp⟩
  have hidx : (⁅K, K⁆ : Subgroup L).relIndex K = p ^ d := by
    rw [relIndex_commutator_self_eq_index_commutator, ← natCard_quotientFactor_commutator_self,
      Nat.card_eq_of_bijective φ φ.bijective]
    simp [Nat.card_eq_fintype_card]
  obtain ⟨a, ha⟩ := exists_natCard_eq_prime_pow_of_index_commutator_eq_prime_pow ↥K hp
    (by rw [← relIndex_commutator_self_eq_index_commutator]; exact hidx)
  refine ⟨p, a, d, hp, ?_, hd, ha, hidx, ⟨φ⟩⟩
  rcases Nat.eq_zero_or_pos a with rfl | ha0
  · exact absurd (by simpa using ha)
      (Finite.one_lt_card_iff_nontrivial.2 ((Subgroup.nontrivial_iff_ne_bot K).2 hK)).ne'
  · exact ha0

theorem isCyclic_of_dvd_sub_one [Finite L] [K.Normal] {p a d : ℕ} (hodd : Odd (Nat.card L))
    (hp : p.Prime) (hcard : Nat.card ↥K = p ^ a) (ha : 1 ≤ a)
    (hidx : (⁅K, K⁆ : Subgroup L).relIndex K = p ^ d) (hd : 1 ≤ d)
    (hbd : (⁅K, K⁆ : Subgroup L).relIndex K ≤ 4 * Nat.card ↥E ^ 2 + 1)
    (hep : Nat.card ↥E ∣ p - 1) : IsCyclic ↥K := by
  have hpK : p ∣ Nat.card ↥K := hcard ▸ dvd_pow_self p (by omega)
  have hpodd : Odd p := (odd_natCard_subgroup hodd K).of_dvd_nat hpK
  have heodd : Odd (Nat.card ↥E) := odd_natCard_subgroup hodd E
  have hp3 : 3 ≤ p := by
    obtain ⟨m, hm⟩ := hpodd
    have := hp.two_le
    omega
  have hple : 2 * Nat.card ↥E + 1 ≤ p :=
    two_mul_add_one_le_of_odd_of_dvd_sub_one hpodd heodd hp3 hep
  have hlt : p ^ d < p ^ 2 :=
    calc p ^ d = (⁅K, K⁆ : Subgroup L).relIndex K := hidx.symm
      _ ≤ 4 * Nat.card ↥E ^ 2 + 1 := hbd
      _ < (2 * Nat.card ↥E + 1) ^ 2 := by nlinarith [Nat.card_pos (α := ↥E)]
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hple 2
  have hd1 : d = 1 := by
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).1 hlt
    omega
  subst hd1
  have hfact : Fact p.Prime := ⟨hp⟩
  have habcard : Nat.card (Abelianization ↥K) = p := by
    rw [natCard_abelianization_eq_index_commutator,
      ← relIndex_commutator_self_eq_index_commutator, hidx, pow_one]
  have : IsCyclic (Abelianization ↥K) := isCyclic_of_prime_card habcard
  exact isCyclic_of_natCard_eq_prime_pow_of_isCyclic_abelianization hp hcard

section Baseline

variable {G : Type*} [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}

theorem cfInner_subTauHom (hc : IsSubcoherent S tau R) {U : Set (L → ℂ)}
    (hUS : U ⊆ (S : Set (L → ℂ))) (f g : charSpanZero U) :
    cfInner (subTauHom hc hUS f : G → ℂ) (subTauHom hc hUS g : G → ℂ)
      = cfInner (f : L → ℂ) (g : L → ℂ) := by
  rw [subTauHom_apply, subTauHom_apply, ← charInner_eq_cfInner, ← charInner_eq_cfInner]
  exact hc.charInner_tau_tau _ (mem_intSpanZeroAtOne_of_mem_charSpanZero hUS f.2) _
    (mem_intSpanZeroAtOne_of_mem_charSpanZero hUS g.2)

theorem subTauHom_apply_one (hc : IsSubcoherent S tau R) {U : Set (L → ℂ)}
    (hUS : U ⊆ (S : Set (L → ℂ))) (f : charSpanZero U) :
    (subTauHom hc hUS f : G → ℂ) 1 = 0 := by
  rw [subTauHom_apply]
  exact hc.tau_apply_one _ (mem_intSpanZeroAtOne_of_mem_charSpanZero hUS f.2)

end Baseline

section Main

variable {G : Type*} [Fintype L] [Group G] [Fintype G]
  {S : Finset (L → ℂ)} {tau : (L → ℂ) → (G → ℂ)} {R : (L → ℂ) → Finset (G → ℂ)}
  [K.Normal]

theorem isCoherent_kerLayerIndFam_commutator_subTauHom (hc : IsSubcoherent S tau R)
    (hS : (S : Set (L → ℂ)) = kerLayerIndFam ⊥ K)
    (hmul : (K : Set L) * (E : Set L) = Set.univ) (hfree : FixesOnlyCommutatorCoset K E) :
    IsCoherent (kerLayerIndFam ⁅K, K⁆ K)
      (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS ⁅K, K⁆)) :=
  isCoherent_kerLayerIndFam_commutator (E := E) hmul hfree _
    (cfInner_subTauHom hc _) (subTauHom_apply_one hc _)

variable (hc : IsSubcoherent S tau R) (hodd : Odd (Nat.card L)) (hK : K ≠ ⊥)
  (hS : (S : Set (L → ℂ)) = kerLayerIndFam ⊥ K)
  (hmul : (K : Set L) * (E : Set L) = Set.univ) (hinf : K ⊓ E = ⊥)
  (hfree : FixesOnlyCommutatorCoset K E)
  (hnc : ¬ IsCoherent (kerLayerIndFam (⊥ : Subgroup L) K)
    (subTauHom hc (kerLayerIndFam_subset_of_eq_bot hS ⊥)))

include hS hmul hfree hnc

theorem not_isMulCommutative_of_not_isCoherent : ¬ IsMulCommutative ↥K := fun hab => by
  have hcb : (⁅K, K⁆ : Subgroup L) = ⊥ := Subgroup.commutator_self_eq_bot_iff.2 hab
  exact hnc (isCoherent_of_eq (congrArg (fun A => kerLayerIndFam A K) hcb)
    (subTauHom_congr hc _ _)
    (isCoherent_kerLayerIndFam_commutator_subTauHom (E := E) hc hS hmul hfree))

variable [Group.IsNilpotent ↥K]

theorem relIndex_commutator_self_le_index_sq_of_not_isCoherent :
    (⁅K, K⁆ : Subgroup L).relIndex K ≤ 4 * K.index ^ 2 + 1 := by
  have hsolv : Group.IsSolvable ↥K := IsNilpotent.to_isSolvable
  refine le_of_not_gt fun hlt => hnc ?_
  exact isCoherent_kerLayerIndFam_of_isNilpotent_quotient_of_eq_bot hc hS inferInstance
    inferInstance bot_le (Subgroup.commutator_le_self K) le_rfl hlt
    (isCoherent_kerLayerIndFam_commutator_subTauHom (E := E) hc hS hmul hfree)

include hinf

theorem relIndex_commutator_self_le_of_not_isCoherent :
    (⁅K, K⁆ : Subgroup L).relIndex K ≤ 4 * Nat.card ↥E ^ 2 + 1 := by
  have h := relIndex_commutator_self_le_index_sq_of_not_isCoherent (E := E) hc hS hmul hfree hnc
  rwa [index_eq_natCard_of_isComplement'
    (isComplement'_of_mul_eq_univ_of_inf_eq_bot hmul hinf)] at h

include hodd hK

theorem nontrivial_quotientFactor_commutator_self_of_not_isCoherent :
    Nontrivial ↥(quotientFactor K (⁅K, K⁆ : Subgroup L)) :=
  nontrivial_quotientFactor K _ (commutator_self_lt_self_of_isNilpotent hK)

theorem eq_bot_of_normal_lt_quotientFactor_commutator_self_of_not_isCoherent
    (J : Subgroup (L ⧸ (⁅K, K⁆ : Subgroup L))) (hJ : J.Normal)
    (hJlt : J < quotientFactor K ⁅K, K⁆) : J = ⊥ :=
  eq_bot_of_normal_lt_quotientFactor_commutator_self (E := E) hodd hinf hfree
    (relIndex_commutator_self_le_of_not_isCoherent (E := E) hc hS hmul hinf hfree hnc) J hJ hJlt

theorem exists_prime_pow_natCard_not_dvd_sub_one_of_not_isCoherent :
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥K = p ^ a ∧
      Nonempty (↥(quotientFactor K (⁅K, K⁆ : Subgroup L)) ≃* Multiplicative (Fin d → ZMod p)) ∧
      ¬ Nat.card ↥E ∣ p - 1 := by
  have hbd := relIndex_commutator_self_le_of_not_isCoherent (E := E) hc hS hmul hinf hfree hnc
  obtain ⟨p, a, d, hp, ha, hd, hcard, hidx, hφ⟩ :=
    exists_prime_pow_natCard_of_relIndex_le (E := E) hodd hK hinf hfree hbd
  refine ⟨p, a, d, hp, ha, hd, hcard, hφ, fun hdvd => ?_⟩
  exact not_isMulCommutative_of_not_isCoherent (E := E) hc hS hmul hfree hnc
    (isCyclic_of_dvd_sub_one (E := E) hodd hp hcard ha hidx hd hbd hdvd).isMulCommutative

theorem obstruction_of_not_isCoherent :
    (Nontrivial ↥(quotientFactor K (⁅K, K⁆ : Subgroup L)) ∧
      ∀ J : Subgroup (L ⧸ (⁅K, K⁆ : Subgroup L)), J.Normal →
        J < quotientFactor K ⁅K, K⁆ → J = ⊥) ∧
    (⁅K, K⁆ : Subgroup L).relIndex K ≤ 4 * Nat.card ↥E ^ 2 + 1 ∧
    ¬ IsMulCommutative ↥K ∧
    ∃ p a d : ℕ, p.Prime ∧ 1 ≤ a ∧ 1 ≤ d ∧ Nat.card ↥K = p ^ a ∧
      Nonempty (↥(quotientFactor K (⁅K, K⁆ : Subgroup L)) ≃* Multiplicative (Fin d → ZMod p)) ∧
      ¬ Nat.card ↥E ∣ p - 1 :=
  ⟨⟨nontrivial_quotientFactor_commutator_self_of_not_isCoherent
      (E := E) hc hodd hK hS hmul hinf hfree hnc,
    eq_bot_of_normal_lt_quotientFactor_commutator_self_of_not_isCoherent
      (E := E) hc hodd hK hS hmul hinf hfree hnc⟩,
   relIndex_commutator_self_le_of_not_isCoherent (E := E) hc hS hmul hinf hfree hnc,
   not_isMulCommutative_of_not_isCoherent (E := E) hc hS hmul hfree hnc,
   exists_prime_pow_natCard_not_dvd_sub_one_of_not_isCoherent
     (E := E) hc hodd hK hS hmul hinf hfree hnc⟩

end Main

end QuotientFrobeniusNoncoherent

end CFSG.FeitThompson
