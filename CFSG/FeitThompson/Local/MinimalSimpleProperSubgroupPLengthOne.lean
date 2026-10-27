module

public import CFSG.FeitThompson.Local.PLengthOneNormalComplementElementSubgroup
public import CFSG.FeitThompson.Foundations.HallContainsNormalPrimeSupport
public import CFSG.FeitThompson.Statements.NonconjugateOutsideSigmaStatements
import CFSG.FeitThompson.Local.PrimeCentralizerCommutatorPrimeLength
import CFSG.FeitThompson.Local.RankTwoPCoreSeriesAbelianTop
import CFSG.FeitThompson.Local.AlphaCoreNormalHall
import CFSG.FeitThompson.Local.SigmaHallInDerivedSubgroup
import CFSG.FeitThompson.Local.AlphaPrimesInSigmaPrimes
import CFSG.FeitThompson.Local.AlphaCoreCentralizerCyclicSylow
import CFSG.FeitThompson.Local.SolvableDerivedKernelCommutators
import CFSG.FeitThompson.Local.PElementNormalSubgroupPLength
import CFSG.FeitThompson.Local.ThreePrimeComplementDecomposition
import CFSG.FeitThompson.Local.PrimeFreeFactorizationFixedSubgroupTransport
import CFSG.FeitThompson.Local.PLengthOneQuotientLift
import CFSG.FeitThompson.Local.PLengthOneSubgroupInheritance
import CFSG.FeitThompson.Foundations.NormalHallContainsPiSubgroups
import CFSG.FeitThompson.Foundations.SolvableHallExistence
import CFSG.FeitThompson.OddOrder.RegularPrimeActionLargeAbelianization
import CFSG.FeitThompson.OddOrder.MaximalOvergroupExistence
import CFSG.FeitThompson.Foundations.CommutatorMonotone
import CFSG.FeitThompson.Definitions.FittingSubgroupAndNormalSylowHallCore
import CFSG.FeitThompson.Foundations.SubgroupOrderAndIndex
import CFSG.FeitThompson.Representations.AlgebraicIntegersRing
import CFSG.FeitThompson.Representations.NormalInducedSupportBasis
import CFSG.FeitThompson.Representations.SchurLemmaIntertwiningMaps
import Mathlib

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

theorem pElements_subset_of_isHallSubgroup {X : Type*} [Group X] [Finite X] {π : Set ℕ}
    {B : Subgroup X} [B.Normal] (hB : IsHallSubgroup π B) {p : ℕ} (hpp : p.Prime) (hp : p ∈ π) :
    pElements p X ⊆ (B : Set X) := by
  intro y hy
  obtain ⟨n, hn⟩ := mem_pElements.1 hy
  refine (hB.isHallPiSubgroup.mem_iff y).2 fun r hr => ?_
  rw [hn] at hr
  obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
  exact ((Nat.prime_dvd_prime_iff_eq hrp hpp).1 (hrp.dvd_of_dvd_pow hrd)) ▸ hp

variable {G : Type*} [Group G] [Finite G]

theorem HasPLengthLeOne.mono {p : ℕ} [Fact p.Prime] {H M : Subgroup G}
    (hHM : H ≤ M) (hM : HasPLengthLeOne p ↥M) : HasPLengthLeOne p ↥H :=
  HasPLengthLeOne.of_surjective (f := (Subgroup.subgroupOfEquivOfLe hHM).toMonoidHom)
    (MulEquiv.surjective _) (hM.subgroup (H.subgroupOf M))

theorem hasPLengthLeOne_of_isCoatom [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {M : Subgroup G} (hM : IsCoatom M) {p : ℕ} (hp : p.Prime) : HasPLengthLeOne p ↥M := by
  have := Fact.mk hp
  have hMsolv : Group.IsSolvable ↥M := hsolv M hM.1
  rcases Classical.em (p ∣ Nat.card ↥M) with hpM | hpM
  swap
  · exact hasPLengthLeOne_of_not_dvd_card hpM
  have hModd : Odd (Nat.card ↥M) := hodd.of_dvd_nat M.card_subgroup_dvd_card
  have hpodd : Odd p := hModd.of_dvd_nat hpM
  rcases Classical.em (p ∈ alphaPrimes ↥M) with hpα | hpα
  swap
  · have hrank : elementaryAbelianPRank p ↥M ≤ 2 := by
      by_contra h
      exact hpα (mem_alphaPrimes.2 ⟨hp, by omega⟩)
    rw [hasPLengthLeOne_iff_not_dvd_index_pComplPCore, Subgroup.index_eq_card]
    exact not_dvd_natCard_quotient_pComplPCore hp hpodd hModd hrank
  have hBnormal := alphaCore_normal ↥M
  have hBhall : IsHallSubgroup (alphaPrimes ↥M) (alphaCore ↥M) :=
    isHallSubgroup_alphaCore hna hodd hsolv hM
  obtain ⟨K, hK⟩ := exists_isHallSubgroup (X := ↥M) (alphaPrimes ↥M)ᶜ
  have hcompl : (alphaCore ↥M).IsComplement' K :=
    hBhall.isComplement' hK (fun q hq hq' => hq' hq)
      (fun q _ => (Classical.em (q ∈ alphaPrimes ↥M)).imp id id)
  have hsup : alphaCore ↥M ⊔ K = ⊤ := hcompl.sup_eq_top
  have hinf : alphaCore ↥M ⊓ K = ⊥ := disjoint_iff.1 hcompl.disjoint
  have hBcomm : alphaCore ↥M = ⁅alphaCore ↥M, K⁆ :=
    eq_commutator_of_isSolvable_of_le_commutator _ _ hsup hinf
      (alphaCore_le_commutator hna hodd hsolv hM)
  have hcop : (Nat.card ↥(alphaCore ↥M)).Coprime (Nat.card ↥K) :=
    hBhall.natCard.coprime_of_compl hK.natCard Nat.card_pos.ne' Nat.card_pos.ne'
  have hMnt : Nontrivial ↥M := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    exact lt_of_lt_of_le hp.one_lt (Nat.le_of_dvd Nat.card_pos hpM)
  obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd
    (n := Nat.card (↥M ⧸ _root_.commutator ↥M))
    (by have := one_lt_card_quotient_commutator (K := ↥M); omega)
  have hqidx : q ∣ (_root_.commutator ↥M).index := by rwa [Subgroup.index_eq_card]
  have hqσ : q ∉ sigmaPrimes M := fun h =>
    not_dvd_index_commutator_of_mem_sigmaPrimes hna hodd hsolv hM h hqidx
  have hqα : q ∉ alphaPrimes ↥M := fun h =>
    hqσ (alphaPrimes_subset_sigmaPrimes hna hodd hsolv hM h)
  have hqM : q ∣ Nat.card ↥M := hqidx.trans (Subgroup.index_dvd_card _)
  have hqK : ¬ q ∣ K.index := by
    intro h
    exact hqα (by
      simpa using isPiNumber_iff.1 hK.index q
        (Nat.mem_primeFactors.2 ⟨hq, h, Subgroup.index_ne_zero_of_finite⟩))
  have hfact : (Nat.card ↥K).factorization q = (Nat.card ↥M).factorization q := by
    have h := Subgroup.card_mul_index K
    have h0 : (Nat.card ↥K).factorization q + K.index.factorization q
        = (Nat.card ↥M).factorization q := by
      rw [← h, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite]
      simp
    rw [Nat.factorization_eq_zero_of_not_dvd hqK] at h0
    omega
  have := Fact.mk hq
  obtain ⟨Qk⟩ : Nonempty (Sylow q ↥K) := inferInstance
  set Q : Subgroup ↥M := (Qk : Subgroup ↥K).map K.subtype with hQdef
  have hQK : Q ≤ K := Subgroup.map_subtype_le _
  have hQcard : Nat.card ↥Q = q ^ (Nat.card ↥M).factorization q := by
    rw [hQdef, Subgroup.card_map_of_injective K.subtype_injective, Qk.card_eq_multiplicity, hfact]
  have hqpos : 0 < (Nat.card ↥M).factorization q :=
    hq.factorization_pos_of_dvd Nat.card_pos.ne' hqM
  set Q' : Subgroup G := Q.map M.subtype with hQ'def
  have hQ'M : Q' ≤ M := Subgroup.map_subtype_le _
  have hQ'card : Nat.card ↥Q' = q ^ (Nat.card ↥M).factorization q := by
    rw [hQ'def, Subgroup.card_map_of_injective M.subtype_injective, hQcard]
  have hQ'ne : Q' ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQ'card
    have : q ^ (Nat.card ↥M).factorization q ≠ 1 :=
      Nat.ne_of_gt (Nat.one_lt_pow (by omega) hq.one_lt)
    omega
  obtain ⟨x, hxQ', hxo, hxcyc⟩ :=
    exists_mem_orderOf_eq_isCyclic_of_notMem_sigmaPrimes hna hodd hsolv hM hq hqσ hQ'M hQ'card hQ'ne
  obtain ⟨y, hyQ, hyx⟩ := hxQ'
  have hyK : (zpowers y : Subgroup ↥M) ≤ K := Subgroup.zpowers_le_of_mem (hQK hyQ)
  have hyorder : orderOf y = q := by
    rw [← hxo, ← hyx]
    exact (Subgroup.orderOf_coe y).symm
  have hycard : Nat.card ↥(zpowers y : Subgroup ↥M) = q := by rw [Nat.card_zpowers, hyorder]
  have hZ : IsZGroup
      (centralizer ((zpowers y : Subgroup ↥M) : Set ↥M) ⊓ alphaCore ↥M : Subgroup ↥M) := by
    have key : ∀ C : Subgroup ↥M,
        C = centralizer ((zpowers y : Subgroup ↥M) : Set ↥M) ⊓ alphaCore ↥M → IsZGroup ↥C := by
      intro C hCeq
      rw [isZGroup_iff]
      intro r hr S
      have hCle : C ≤ alphaCore ↥M := hCeq.le.trans inf_le_right
      have hpush : Subgroup.map M.subtype (Subgroup.map C.subtype (S : Subgroup ↥C))
          ≤ Subgroup.map M.subtype (alphaCore ↥M) ⊓ centralizer ({x} : Set G) := by
        refine le_inf (Subgroup.map_mono ((Subgroup.map_subtype_le _).trans hCle)) ?_
        intro g hg
        obtain ⟨z, hz, rfl⟩ := hg
        obtain ⟨w, -, rfl⟩ := hz
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        simp only [Set.mem_singleton_iff] at hh
        subst hh
        have hwC : (w : ↥M) ∈ centralizer ((zpowers y : Subgroup ↥M) : Set ↥M) :=
          (Subgroup.mem_inf.1 (hCeq.le w.2)).1
        have hc := Subgroup.mem_centralizer_iff.1 hwC y (Subgroup.mem_zpowers y)
        rw [← hyx]
        exact congrArg M.subtype hc
      have hpg : IsPGroup r ↥(Subgroup.map M.subtype (Subgroup.map C.subtype (S : Subgroup ↥C))) :=
        (S.isPGroup'.map C.subtype).map M.subtype
      have hcy := hxcyc r hr _ hpush hpg
      exact isCyclic_of_injective
        (((Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective).trans
          (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective)) :
            ↥(S : Subgroup ↥C) ≃* _).toMonoidHom (MulEquiv.injective _)
    exact key _ rfl
  have hadm : IsAdmissibleCoprimeActionQuadruple ↥M (alphaCore ↥M) K (zpowers y) :=
    { isSolvable := hMsolv
      odd_card := hModd
      normal := hBnormal
      sup_eq_top := hsup
      inf_eq_bot := hinf
      coprime := hcop
      le := hyK
      prime_card := by rw [hycard]; exact hq
      isZGroup_centralizer := hZ }
  have hBlen : HasPLengthLeOne p ↥(alphaCore ↥M) := by
    have h := hasPLengthLeOne_commutator_of_admissible (p := p) hadm
    rwa [← hBcomm] at h
  exact hasPLengthLeOne_of_pElements_subset
    (pElements_subset_of_isHallSubgroup hBhall hp hpα) hBlen

theorem hasPLengthLeOne_of_ne_top [IsSimpleGroup G] (hna : ¬ IsMulCommutative G)
    (hodd : Odd (Nat.card G)) (hsolv : ∀ Y : Subgroup G, Y ≠ ⊤ → Group.IsSolvable ↥Y)
    {H : Subgroup G} (hH : H ≠ ⊤) {p : ℕ} (hp : p.Prime) : HasPLengthLeOne p ↥H := by
  have := Fact.mk hp
  obtain ⟨M, hM, hHM⟩ := exists_isCoatom_ge_of_ne_top hH
  exact HasPLengthLeOne.mono hHM (hasPLengthLeOne_of_isCoatom hna hodd hsolv hM hp)

end

end CFSG.FeitThompson

namespace CFSG.FeitThompson.Proofs

public section

open Subgroup CFSG.FeitThompson

universe u

theorem FTS_proper_subgroup_p_length_one :
    Statements.FTS_proper_subgroup_p_length_one.{u} := by
  intro G _ _ hG p hp H hH
  have := Fact.mk hp
  have := hG.isSimpleGroup
  have h := hasPLengthLeOne_of_ne_top hG.not_isMulCommutative hG.odd_natCard
    hG.isSolvable_of_ne_top hH hp
  rw [hasPLengthLeOne_iff_not_dvd_index_pComplPCore, pComplPCore_eq_comap] at h
  exact h

end

end CFSG.FeitThompson.Proofs
