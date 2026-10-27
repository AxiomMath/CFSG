module

public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.SigmaComplementPrimeData
import CFSG.FeitThompson.Local.CriticalSubgroupFixedLine
import CFSG.FeitThompson.Local.AbelianSylowNormalPrimeCentralizerFitting
import CFSG.FeitThompson.Local.PComplementQuotientSylowRank
import CFSG.FeitThompson.Foundations.SolvableHallExistence
public import CFSG.FeitThompson.Foundations.NilpotenceEquivalentDefinitions

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open CFSG.FeitThompson CFSG.FeitThompson Subgroup

universe u

variable {G : Type u} [Group G]

theorem isMulCommutative_sylow_of_notMem_sigmaPrimes
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    [Finite G] (hG : IsOddSimpleMinimal G)
    {M : Subgroup G} (hM : IsCoatom M) {q : ℕ} (hq : q.Prime) (hqσ : q ∉ sigmaPrimes M)
    (P : Sylow q ↥M) : IsMulCommutative ↥(P : Subgroup ↥M) := by
  have := hG.isSimpleGroup
  have hfq := Fact.mk hq
  have hPcard : Nat.card ↥(P : Subgroup ↥M) = q ^ (Nat.card ↥M).factorization q :=
    P.card_eq_multiplicity
  by_cases hdvd : q ∣ Nat.card ↥M
  ·
    have hMG : Nat.card ↥M ∣ Nat.card G := M.card_subgroup_dvd_card
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hG.odd_natCard) (even_iff_two_dvd.2 (hdvd.trans hMG))
    have hqodd : Odd q := hq.odd_of_ne_two hq2
    have hrank : elementaryAbelianPRank q ↥M ≤ 2 := by
      by_contra hcon
      exact hqσ (alphaPrimes_subset_sigmaPrimes hG.not_isMulCommutative hG.odd_natCard
        hG.isSolvable_of_ne_top hM (mem_alphaPrimes.2 ⟨hq, by omega⟩))
    rcases Nat.lt_or_ge (elementaryAbelianPRank q ↥M) 2 with h1 | h2
    ·
      have hPrank : elementaryAbelianPRank q ↥(P : Subgroup ↥M) = elementaryAbelianPRank q ↥M :=
        elementaryAbelianPRank_eq_of_natCard_eq_pow_factorization hq hPcard
      exact (isCyclic_of_elementaryAbelianPRank_le_one hq hqodd P.isPGroup'
        (by omega)).isMulCommutative
    ·
      have hr2 : elementaryAbelianPRank q ↥M = 2 := by omega
      obtain ⟨A₀, ⟨e⟩⟩ := mem_elementaryAbelianRanks.1
        (hr2 ▸ elementaryAbelianPRank_mem_elementaryAbelianRanks (X := ↥M) hq.one_lt)
      have hplane : IsElementaryAbelianPlane q (A₀.map M.subtype) :=
        ⟨(A₀.equivMapOfInjective M.subtype M.subtype_injective).symm.trans e⟩
      obtain ⟨-, -, hsyl, -⟩ := h₂ G hG q M (A₀.map M.subtype)
        ⟨hM, hq, hqσ, Subgroup.map_subtype_le _, hplane⟩
      have hcomm : IsMulCommutative ↥((P : Subgroup ↥M).map M.subtype) := (hsyl _ ⟨P, rfl⟩).1
      exact isMulCommutative_of_mulEquiv
        ((P : Subgroup ↥M).equivMapOfInjective M.subtype M.subtype_injective)
  ·
    have hcard1 : Nat.card ↥(P : Subgroup ↥M) = 1 := by
      rw [hPcard, Nat.factorization_eq_zero_of_not_dvd hdvd, pow_zero]
    have : Subsingleton ↥(P : Subgroup ↥M) := (Nat.card_eq_one_iff_unique.1 hcard1).1
    exact IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _

theorem isMulCommutative_of_isPGroup_le_of_notMem_sigmaPrimes
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    [Finite G] (hG : IsOddSimpleMinimal G)
    {M : Subgroup G} (hM : IsCoatom M) {q : ℕ} (hq : q.Prime) (hqσ : q ∉ sigmaPrimes M)
    {S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup q ↥S) : IsMulCommutative ↥S := by
  have hfq := Fact.mk hq
  obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥M))
  have hPab := isMulCommutative_sylow_of_notMem_sigmaPrimes h₂ hG hM hq hqσ P
  have hS' : IsPGroup q ↥(S.subgroupOf M) := hS.of_equiv (subgroupOfEquivOfLe hSM).symm
  have := isMulCommutative_of_isPGroup_of_isMulCommutative_sylow hq P hPab hS'
  exact isMulCommutative_of_mulEquiv (subgroupOfEquivOfLe hSM).symm

theorem isMulCommutative_of_isNilpotent_of_isPiSubgroup_compl_sigmaPrimes
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u})
    [Finite G] (hG : IsOddSimpleMinimal G)
    {M : Subgroup G} (hM : IsCoatom M) {Q : Subgroup G} (hQM : Q ≤ M)
    (hQnil : Group.IsNilpotent ↥Q) (hQπ : IsPiSubgroup ((sigmaPrimes M)ᶜ) Q) :
    IsMulCommutative ↥Q := by
  obtain ⟨P, -, hcard, ⟨e⟩⟩ := exists_mulEquiv_pi_normal_sylow ↥Q
  have habel : ∀ p : (Nat.card ↥Q).primeFactors, IsMulCommutative ↥(P p) := by
    intro p
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have hpσ : (p : ℕ) ∉ sigmaPrimes M := isPiSubgroup_iff.1 hQπ _ p.2
    have hPG : IsPGroup (p : ℕ) ↥((P p).map Q.subtype) :=
      (IsPGroup.of_card (hcard p)).of_equiv
        ((P p).equivMapOfInjective Q.subtype Q.subtype_injective)
    have := isMulCommutative_of_isPGroup_le_of_notMem_sigmaPrimes h₂ hG hM hp hpσ
      ((Subgroup.map_subtype_le _).trans hQM) hPG
    exact isMulCommutative_of_mulEquiv
      ((P p).equivMapOfInjective Q.subtype Q.subtype_injective)
  have hprod : IsMulCommutative (∀ p : (Nat.card ↥Q).primeFactors, ↥(P p)) :=
    IsMulCommutative.of_comm fun a b => funext fun p => (habel p).is_comm.comm (a p) (b p)
  exact isMulCommutative_of_mulEquiv e.symm

theorem FBG_sigma_complement_abelian_nilpotent
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FNI_outside_sigma_plane_sylow.{u}) :
    _root_.CFSG.FeitThompson.Statements.FBG_sigma_complement_abelian_nilpotent.{u} := by
  intro G _ _ hG M hM
  have hG' : IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  refine ⟨fun Q hQM hQnil hQπ =>
    isMulCommutative_of_isNilpotent_of_isPiSubgroup_compl_sigmaPrimes h₂ hG' hM hQM hQnil hQπ,
    fun E hE => ?_⟩
  obtain ⟨hπE, -, -, -, hnil, -⟩ := FNI_sigma_complement_prime_data h₁ G hG' M E ⟨hM, hE⟩
  have hEM : E ≤ M := hE.right_le
  have hE'E : (⁅E, E⁆ : Subgroup G) ≤ E := commutator_le_self E
  refine isMulCommutative_of_isNilpotent_of_isPiSubgroup_compl_sigmaPrimes h₂ hG' hM
    (hE'E.trans hEM) hnil (isPiSubgroup_iff.2 fun r hr => ?_)
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
  have hdvd : r ∣ Nat.card ↥E :=
    (Nat.dvd_of_mem_primeFactors hr).trans (Subgroup.card_dvd_of_le hE'E)
  have hrE : r ∈ primeDivisorsOf ↥E := ⟨hrp, hdvd⟩
  rw [hπE] at hrE
  exact hrE.2

end

end CFSG.FeitThompson.Proofs
