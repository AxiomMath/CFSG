module

public import CFSG.FeitThompson.Local.MixedFittingCentralizerPrimeSupport
import CFSG.FeitThompson.Local.HighRankFittingUniqueOvergroup
import CFSG.FeitThompson.Local.LargestPrimeCharacteristicSylow
import CFSG.FeitThompson.Local.MaximalIntersectionSylowNormalizerControl
import CFSG.FeitThompson.Local.MixedFittingComplementCoreEquality
import CFSG.FeitThompson.Local.FittingOverlapPrimeCoreNoncyclic
import CFSG.FeitThompson.Local.InvariantControlUniqueMaximalOvergroup
import CFSG.FeitThompson.OddOrder.NontrivialPSubgroupProper
import CFSG.FeitThompson.OddOrder.RankTwoKernelSmallerComplementPrimes
import CFSG.FeitThompson.Foundations.SylowContainmentConjugacy
import CFSG.FeitThompson.Foundations.PrimeCoreLargestNormalPSubgroup
import CFSG.FeitThompson.Foundations.NormalNilpotentInFitting
import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Pointwise Subgroup

variable {G : Type*} [Group G] [Finite G] {p q : ℕ} {A M P : Subgroup G}

theorem elementaryAbelianPRank_fittingRaw_le_pCore (hq : q.Prime) (X : Type*) [Group X]
    [Finite X] :
    elementaryAbelianPRank q ↥(fittingRaw X) ≤ elementaryAbelianPRank q ↥(pCore q X) := by
  obtain ⟨B, hBF, hcomm, hexp, hcard⟩ :=
    (mem_elementaryAbelianRanks_subgroup_iff (H := fittingRaw X) hq).1
      (elementaryAbelianPRank_mem_elementaryAbelianRanks hq.one_lt)
  exact le_elementaryAbelianPRank hq.one_lt
    ((mem_elementaryAbelianRanks_subgroup_iff (H := pCore q X) hq).2
      ⟨B, le_pCore_of_isPGroup_of_le_fittingRaw hq (IsPGroup.of_card hcard) hBF, hcomm, hexp,
        hcard⟩)

theorem elementaryAbelianPRank_pCoreIn (hq : q.Prime) (X : Subgroup G) :
    elementaryAbelianPRank q ↥(pCoreIn q X) = elementaryAbelianPRank q ↥(pCore q ↥X) := by
  rw [pCoreIn_eq]
  exact elementaryAbelianPRank_eq_of_mulEquiv hq.one_lt
    ((pCore q ↥X).equivMapOfInjective X.subtype X.subtype_injective).symm

theorem elementaryAbelianPRank_conj_smul (hp : 1 < p) (g : G) (H : Subgroup G) :
    elementaryAbelianPRank p ↥(MulAut.conj g • H) = elementaryAbelianPRank p ↥H :=
  elementaryAbelianPRank_eq_of_mulEquiv hp (Subgroup.equivSMul (MulAut.conj g) H).symm

theorem elementaryAbelianPRank_mixedFitting_le_two_of_exists_coatom_ne
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X) (hp : p.Prime)
    (hAcomm : IsMulCommutative ↥A) (hApg : IsPGroup p ↥A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) :
    elementaryAbelianPRank p ↥(mixedFitting M) ≤ 2 := by
  by_contra hcon
  obtain ⟨M₁, M₂, hM₁, hM₂, hAM₁, hAM₂, hne⟩ := hAtwo
  obtain ⟨N, hN⟩ := exists_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_mixedFitting
    hna hodd hsolv hM hp (by omega) hAcomm hApg hArank
  exact hne ((hN.eq_of_isCoatom hM₁ hAM₁).trans (hN.eq_of_isCoatom hM₂ hAM₂).symm)

theorem exists_prime_ne_normal_isPGroup_forall_normalizer_le
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X)
    (hM : IsCoatom M) (hMbot : M ≠ ⊥) (hp : p.Prime)
    (hApg : IsPGroup p ↥A) (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hFrank : elementaryAbelianPRank p ↥(mixedFitting M) ≤ 2) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ ∃ J : Subgroup G, J ≤ M ∧ (J.subgroupOf M).Normal ∧
      IsPGroup q ↥J ∧ J ≠ ⊥ ∧
      ∀ Q : Subgroup G, IsPGroup q ↥Q → J ≤ Q → normalizer (Q : Set G) ≤ M := by
  by_cases hall : ∀ r : ℕ, r.Prime → elementaryAbelianPRank r ↥(fittingRaw ↥M) ≤ 2
  ·
    have hMsolv : Group.IsSolvable ↥M := hsolv M hM.1
    have hMnt : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).2 hMbot
    have hoddM : Odd (Nat.card ↥M) := odd_natCard_subgroup hodd M
    obtain ⟨hq, hqM, hqmax⟩ := max'_primeFactors_natCard_spec ↥M
    set q := (Nat.card ↥M).primeFactors.max' (primeFactors_natCard_nonempty ↥M) with hqdef
    have := Fact.mk hq
    obtain ⟨Q, hQchar, hQcard⟩ :=
      exists_characteristic_natCard_eq_pow_factorization hoddM hall hq hqM hqmax
    set J : Subgroup G := Q.map M.subtype with hJdef
    have hJM : J ≤ M := Subgroup.map_subtype_le _
    have hJsub : J.subgroupOf M = Q :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective Q
    have hQnormal : Q.Normal := Subgroup.normal_of_characteristic Q
    have hJnormal : (J.subgroupOf M).Normal := hJsub ▸ hQnormal
    have hJcard : Nat.card ↥J = q ^ (Nat.card ↥M).factorization q := by
      rw [hJdef, Subgroup.card_map_of_injective M.subtype_injective, hQcard]
    have hJpg : IsPGroup q ↥J := IsPGroup.of_card hJcard
    have hJne : J ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hJcard
      have hpos : 0 < (Nat.card ↥M).factorization q :=
        hq.factorization_pos_of_dvd Nat.card_pos.ne' hqM
      have := Nat.one_lt_pow (n := (Nat.card ↥M).factorization q) hpos.ne' hq.one_lt
      omega
    have hMnorm : M ≤ normalizer (J : Set G) :=
      le_normalizer_of_normal_subgroupOf (hK := hJnormal) hJM
    have hNJ : normalizer (J : Set G) = M := normalizer_eq_of_isCoatom hM hJne hJM hMnorm
    have hJfull : Nat.card ↥J = q ^ (Nat.card G).factorization q :=
      natCard_eq_pow_factorization_of_normalizer_le hq hJcard hNJ.le
    have hSJ : ((Sylow.ofCard J hJfull : Sylow q G) : Subgroup G) = J := Sylow.coe_ofCard _ _
    have hJF : J ≤ mixedFitting M := by
      rw [mixedFitting_eq, hJdef]
      exact Subgroup.map_mono
        (le_fittingRaw_of_normal_of_isNilpotent hQnormal (IsPGroup.of_card hQcard).isNilpotent)
    refine ⟨q, hq, ?_, J, hJM, hJnormal, hJpg, hJne, ?_⟩
    ·
      rintro rfl
      obtain ⟨g, hg⟩ := exists_le_conj_smul_sylow (Sylow.ofCard J hJfull) hApg
      rw [hSJ] at hg
      have h1 : 3 ≤ elementaryAbelianPRank q ↥J := by
        calc 3 ≤ elementaryAbelianPRank q ↥A := hArank
        _ ≤ elementaryAbelianPRank q ↥(MulAut.conj g • J) :=
            elementaryAbelianPRank_le_of_le hq.one_lt hg
        _ = elementaryAbelianPRank q ↥J := elementaryAbelianPRank_conj_smul hq.one_lt g J
      have h2 := (elementaryAbelianPRank_le_of_le hq.one_lt hJF).trans hFrank
      omega
    ·
      intro R hRpg hJR
      have hRJ : R = J := by
        have h := (Sylow.ofCard J hJfull).is_maximal' hRpg (by rw [hSJ]; exact hJR)
        rwa [hSJ] at h
      rw [hRJ, hNJ]
  ·
    obtain ⟨r, hr, hrrank⟩ := by
      simpa only [not_forall, not_le, Nat.lt_iff_add_one_le, exists_prop] using hall
    have hrF : 3 ≤ elementaryAbelianPRank r ↥(mixedFitting M) := by
      rw [← elementaryAbelianPRank_fittingRaw_eq hr]; omega
    set J : Subgroup G := pCoreIn r M with hJdef
    have hJM : J ≤ M := pCoreIn_le r M
    have hJsub : J.subgroupOf M = pCore r ↥M := by
      rw [hJdef, pCoreIn_eq]
      exact Subgroup.comap_map_eq_self_of_injective M.subtype_injective _
    have hJnormal : (J.subgroupOf M).Normal := hJsub ▸ pCore_normal r ↥M
    have hJpg : IsPGroup r ↥J := isPGroup_pCoreIn hr M
    have hJrank : 3 ≤ elementaryAbelianPRank r ↥J := by
      rw [hJdef, elementaryAbelianPRank_pCoreIn hr]
      refine le_trans ?_ (elementaryAbelianPRank_fittingRaw_le_pCore hr ↥M)
      omega
    have hJne : J ≠ ⊥ := by
      intro h
      rw [h] at hJrank
      have hle : elementaryAbelianPRank r ↥(⊥ : Subgroup G) ≤ Nat.card ↥(⊥ : Subgroup G) :=
        elementaryAbelianPRank_le_card hr.one_lt
      rw [Subgroup.card_bot] at hle
      omega
    have hrp : r ≠ p := by
      intro h
      rw [h] at hrrank
      rw [← elementaryAbelianPRank_fittingRaw_eq hp] at hFrank
      omega
    obtain ⟨E, hEJ, hEcomm, hEexp, hEcard⟩ :=
      (mem_elementaryAbelianRanks_subgroup_iff (H := J) (d := 3) hr).1
        ((le_elementaryAbelianPRank_iff hr.one_lt).1 hJrank)
    have hEea : IsElementaryAbelian r E := isElementaryAbelian_iff.2
      ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hEcomm a a.2 b b.2), hEexp⟩
    have hErank : 3 ≤ elementaryAbelianPRank r ↥E :=
      hEea.le_elementaryAbelianPRank hr hEcard le_rfl
    obtain ⟨N, hN⟩ :=
      exists_isUniqueMaximalOvergroup_of_three_le_elementaryAbelianPRank_mixedFitting
        hna hodd hsolv hM hr hrF hEea.isMulCommutative hEea.isPGroup hErank
    have hEM : IsUniqueMaximalOvergroup E M := by
      have h : M = N := hN.eq_of_isCoatom hM (hEJ.trans hJM)
      rw [h]; exact hN
    refine ⟨r, hr, hrp, J, hJM, hJnormal, hJpg, hJne, ?_⟩
    intro R hRpg hJR
    have hRne : R ≠ ⊥ := fun h => hJne (le_bot_iff.1 (h ▸ hJR))
    have hRtop : normalizer (R : Set G) ≠ ⊤ :=
      (normalizer_lt_top_of_isPGroup hna hr hRne hRpg).ne
    exact hEM.le_of_ne_top ((hEJ.trans hJR).trans Subgroup.le_normalizer) hRtop

theorem elementaryAbelianPRank_mixedFitting_le_two_of_scn
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X) (hp : p.Prime)
    (hPcard : Nat.card ↥P = p ^ (Nat.card G).factorization p)
    (hAP : A ≤ P) (_hAnormal : (A.subgroupOf P).Normal) (hAcomm : IsMulCommutative ↥A)
    (_hACP : P ⊓ centralizer (A : Set G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) (_hCM : centralizer (A : Set G) ≤ M) :
    elementaryAbelianPRank p ↥(mixedFitting M) ≤ 2 :=
  elementaryAbelianPRank_mixedFitting_le_two_of_exists_coatom_ne hna hodd hsolv hp hAcomm
    ((IsPGroup.of_card hPcard).to_le hAP) hArank hAtwo hM

theorem exists_prime_ne_normal_isPGroup_forall_normalizer_le_of_scn
    [IsSimpleGroup G] (hna : ¬ IsMulCommutative G) (hodd : Odd (Nat.card G))
    (hsolv : ∀ X : Subgroup G, X ≠ ⊤ → Group.IsSolvable ↥X) (hp : p.Prime)
    (hPcard : Nat.card ↥P = p ^ (Nat.card G).factorization p)
    (hAP : A ≤ P) (hAnormal : (A.subgroupOf P).Normal) (hAcomm : IsMulCommutative ↥A)
    (hACP : P ⊓ centralizer (A : Set G) = A)
    (hArank : 3 ≤ elementaryAbelianPRank p ↥A)
    (hAtwo : ∃ M₁ M₂ : Subgroup G, IsCoatom M₁ ∧ IsCoatom M₂ ∧ A ≤ M₁ ∧ A ≤ M₂ ∧ M₁ ≠ M₂)
    (hM : IsCoatom M) (hCM : centralizer (A : Set G) ≤ M) :
    ∃ q : ℕ, q.Prime ∧ q ≠ p ∧ ∃ J : Subgroup G, J ≤ M ∧ (J.subgroupOf M).Normal ∧
      IsPGroup q ↥J ∧ J ≠ ⊥ ∧
      ∀ Q : Subgroup G, IsPGroup q ↥Q → J ≤ Q → normalizer (Q : Set G) ≤ M := by
  have hAne : A ≠ ⊥ := by
    intro h
    rw [h] at hArank
    have hle : elementaryAbelianPRank p ↥(⊥ : Subgroup G) ≤ Nat.card ↥(⊥ : Subgroup G) :=
      elementaryAbelianPRank_le_card hp.one_lt
    rw [Subgroup.card_bot] at hle
    omega
  have hMbot : M ≠ ⊥ := fun h =>
    hAne (le_bot_iff.1 (h ▸ (Subgroup.le_centralizer A).trans hCM))
  exact exists_prime_ne_normal_isPGroup_forall_normalizer_le hna hodd hsolv hM hMbot hp
    ((IsPGroup.of_card hPcard).to_le hAP) hArank
    (elementaryAbelianPRank_mixedFitting_le_two_of_scn hna hodd hsolv hp hPcard hAP hAnormal
      hAcomm hACP hArank hAtwo hM hCM)

end

end CFSG.FeitThompson
