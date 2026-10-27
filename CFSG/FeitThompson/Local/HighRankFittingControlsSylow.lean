module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
public import CFSG.FeitThompson.Definitions.UniqueMaximalOvergroup
import CFSG.FeitThompson.Local.LargeAbelianNormalNoComplementaryPrime
import CFSG.FeitThompson.Local.PPrimeFreeSubgroupUniqueMaximal
import CFSG.FeitThompson.Local.TrivialComplementaryCoreMaximalSylow
import CFSG.FeitThompson.Local.FittingSupportExcludesNormalCore
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup

variable {G : Type*} [Group G] [Finite G] {p : ℕ} {M P A : Subgroup G}

omit [Finite G] in
theorem ne_bot_of_le_elementaryAbelianPRank {d : ℕ} (hp : 1 < p) (hd : d ≠ 0)
    (h : d ≤ elementaryAbelianPRank p ↥A) : A ≠ ⊥ := by
  rintro rfl
  rw [elementaryAbelianPRank_eq_zero_of_subsingleton hp] at h
  omega

theorem isPGroup_fittingRaw_of_isPGroup_mixedFitting (hFp : IsPGroup p ↥(mixedFitting M)) :
    IsPGroup p ↥(fittingRaw ↥M) := by
  rw [mixedFitting_eq] at hFp
  exact hFp.of_injective
    (Subgroup.equivMapOfInjective (fittingRaw ↥M) M.subtype M.subtype_injective).toMonoidHom
    (MulEquiv.injective _)

theorem pComplCore_eq_bot_of_isPGroup_mixedFitting [Group.IsSolvable ↥M] (hp : p.Prime)
    (hFp : IsPGroup p ↥(mixedFitting M)) : pComplCore p ↥M = ⊥ :=
  pComplCore_eq_bot_of_isPGroup_fittingRaw hp ↥M (isPGroup_fittingRaw_of_isPGroup_mixedFitting hFp)

theorem prime_dvd_natCard_of_isPGroup_mixedFitting (hp : p.Prime)
    (hFp : IsPGroup p ↥(mixedFitting M)) (hFbot : mixedFitting M ≠ ⊥) : p ∣ Nat.card ↥M :=
  (prime_dvd_natCard_of_isPGroup_of_ne_bot hp hFp hFbot).trans
    (Subgroup.card_dvd_of_le (mixedFitting_le M))

theorem natCard_sylow_eq_of_isPGroup_mixedFitting_of_rank_three [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime) (hFp : IsPGroup p ↥(mixedFitting M))
    (hFrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) :
    Nat.card ↥P = p ^ (Nat.card G).factorization p := by
  have := hsolv M hM.1
  have hFbot : mixedFitting M ≠ ⊥ :=
    ne_bot_of_le_elementaryAbelianPRank hp.one_lt three_ne_zero hFrank
  exact (normalizer_le_and_natCard_eq_of_trivial_pComplCore hp hna hodd hsolv hM
    (prime_dvd_natCard_of_isPGroup_mixedFitting hp hFp hFbot) hPM hPcard
    (pComplCore_eq_bot_of_isPGroup_mixedFitting hp hFp)).2

theorem exists_sylow_coe_eq_of_isPGroup_mixedFitting_of_rank_three [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime) (hFp : IsPGroup p ↥(mixedFitting M))
    (hFrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) :
    ∃ T : Sylow p G, (T : Subgroup G) = P :=
  exists_sylow_coe_eq_of_natCard_eq_pow_factorization hp
    (natCard_sylow_eq_of_isPGroup_mixedFitting_of_rank_three hna hodd hsolv hM hp hFp hFrank hPM
      hPcard)

private theorem isPrimeFittingSylowSetup_of_rank_three (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime) (hFp : IsPGroup p ↥(mixedFitting M))
    (hFrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) (hAP : A ≤ P)
    (hAnormal : (A.subgroupOf P).Normal) (hAcomm : IsMulCommutative ↥A)
    (hCP : P ⊓ centralizer (A : Set G) = A) : IsPrimeFittingSylowSetup p M P A where
  isCoatom := hM
  isSolvable := hsolv M hM.1
  odd := odd_natCard_subgroup hodd M
  prime := hp
  mixedFitting_ne_bot := ne_bot_of_le_elementaryAbelianPRank hp.one_lt three_ne_zero hFrank
  isPGroup_mixedFitting := hFp
  sylow_le := hPM
  card_sylow := hPcard
  le_sylow := hAP
  normal := hAnormal
  isMulCommutative := hAcomm
  centralizer_inf_eq := hCP

theorem le_mixedFitting_of_isPGroup_mixedFitting_of_rank_three (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime) (hFp : IsPGroup p ↥(mixedFitting M))
    (hFrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) (hAP : A ≤ P)
    (hAnormal : (A.subgroupOf P).Normal) (hAcomm : IsMulCommutative ↥A)
    (hCP : P ⊓ centralizer (A : Set G) = A) (_hArank : 3 ≤ elementaryAbelianPRank p ↥A) :
    A ≤ mixedFitting M :=
  (isPrimeFittingSylowSetup_of_rank_three hodd hsolv hM hp hFp hFrank hPM hPcard hAP hAnormal
    hAcomm hCP).le_mixedFitting

theorem isUniqueMaximalOvergroup_of_isPGroup_mixedFitting_of_rank_three [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    (hM : IsCoatom M) (hp : p.Prime) (hFp : IsPGroup p ↥(mixedFitting M))
    (hFrank : 3 ≤ elementaryAbelianPRank p ↥(mixedFitting M)) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) (hAP : A ≤ P)
    (hAnormal : (A.subgroupOf P).Normal) (hAcomm : IsMulCommutative ↥A)
    (hCP : P ⊓ centralizer (A : Set G) = A) (hArank : 3 ≤ elementaryAbelianPRank p ↥A) :
    IsUniqueMaximalOvergroup A M := by
  have h := isPrimeFittingSylowSetup_of_rank_three hodd hsolv hM hp hFp hFrank hPM hPcard hAP
    hAnormal hAcomm hCP
  have hA3 : 3 ∈ elementaryAbelianRanks p ↥A := (le_elementaryAbelianPRank_iff hp.one_lt).1 hArank
  refine isUniqueMaximalOvergroup_of_control hp hna hodd hsolv hM
    (bot_lt_iff_ne_bot.2 (ne_bot_of_le_elementaryAbelianPRank hp.one_lt three_ne_zero hArank))
    ((IsPGroup.of_card hPcard).to_le hAP) (hAP.trans hPM) fun Y hY hYA => ?_
  exact h.eq_bot_of_not_dvd_natCard_of_le_normalizer hna hodd hsolv hA3
    (hp.coprime_iff_not_dvd.1 hY) hYA

theorem natCard_sylow_eq_and_le_mixedFitting_and_isUniqueMaximalOvergroup [IsSimpleGroup G]
    (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ K : Subgroup G, K ≠ ⊤ → Group.IsSolvable ↥K)
    {F : Subgroup G} (hM : IsCoatom M) (hp : p.Prime) (hF : F = mixedFitting M)
    (hFp : IsPGroup p ↥F) (hFrank : 3 ≤ elementaryAbelianPRank p ↥F) (hPM : P ≤ M)
    (hPcard : Nat.card ↥P = p ^ (Nat.card ↥M).factorization p) :
    Nat.card ↥P = p ^ (Nat.card G).factorization p ∧
      ∀ A : Subgroup G, A ≤ P → (A.subgroupOf P).Normal → IsMulCommutative ↥A →
        P ⊓ centralizer (A : Set G) = A → 3 ≤ elementaryAbelianPRank p ↥A →
        A ≤ F ∧ IsUniqueMaximalOvergroup A M := by
  subst hF
  refine ⟨natCard_sylow_eq_of_isPGroup_mixedFitting_of_rank_three hna hodd hsolv hM hp hFp hFrank
    hPM hPcard, fun A hAP hAnormal hAcomm hCP hArank => ⟨?_, ?_⟩⟩
  · exact le_mixedFitting_of_isPGroup_mixedFitting_of_rank_three hodd hsolv hM hp hFp hFrank hPM
      hPcard hAP hAnormal hAcomm hCP hArank
  · exact isUniqueMaximalOvergroup_of_isPGroup_mixedFitting_of_rank_three hna hodd hsolv hM hp hFp
      hFrank hPM hPcard hAP hAnormal hAcomm hCP hArank

end

end CFSG.FeitThompson
