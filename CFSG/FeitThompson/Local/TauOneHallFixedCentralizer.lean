module

public import CFSG.FeitThompson.Statements.SignalizerTypeStatements
public import CFSG.FeitThompson.Statements.TypeIIIIVExclusionStatements
public import CFSG.FeitThompson.Statements.NonabelianAmbientPlaneStatements
import CFSG.FeitThompson.Local.SigmaComplementThreeHallFactors
import CFSG.FeitThompson.Local.CyclicSylowSigmaComplementFixedCentralizer
import CFSG.FeitThompson.Local.TauOnePrimeCentralizerInclusion
import CFSG.FeitThompson.Foundations.SolvableHallConjugacy
import CFSG.FeitThompson.Local.FittingSplitsNormalHall
import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
import CFSG.FeitThompson.Representations.TypeIIDerivedFrobeniusOrEqualDegreePair
import CFSG.FeitThompson.Local.NilpotentDerivedNormalizerFactorization

namespace CFSG.FeitThompson.Proofs

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup CFSG.FeitThompson
open CFSG.FeitThompson.Prep09

universe u

theorem le_centralizer_of_forall_sylow_map_le_centralizer {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {S : Set G}
    (h : ∀ q : ℕ, q.Prime → ∀ Q : Sylow q ↥H,
      (Q : Subgroup ↥H).map H.subtype ≤ centralizer S) :
    H ≤ centralizer S := by
  have htop : (H ⊓ centralizer S).subgroupOf H = ⊤ := by
    refine eq_top_of_forall_sylow_le fun q hq Q x hx => ?_
    exact Subgroup.mem_subgroupOf.2
      (le_inf (Subgroup.map_subtype_le _) (h q hq Q) (Subgroup.mem_map_of_mem H.subtype hx))
  exact (Subgroup.subgroupOf_eq_top.1 htop).trans inf_le_right

theorem FTS_tau_one_hall_fixed_centralizer
    (h₁ : _root_.CFSG.FeitThompson.Statements.FBG_sigma_core_normal_hall.{u})
    (h₂ : _root_.CFSG.FeitThompson.Statements.FTS_admissible_tau_one_prime_centralizer_inclusion.{u})
    (h₃ : _root_.CFSG.FeitThompson.Statements.FTS_tau_one_three_prime_normalizer_transfer.{u}) :
    _root_.CFSG.FeitThompson.Statements.FTS_tau_one_hall_fixed_centralizer.{u} := by
  intro G _ _ hG M hM E hEM hsd E₁ hE₁E hE₁Hall
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_ne_top M hM.1
  have hEsolv : Group.IsSolvable ↥E := @isSolvable_of_le _ _ _ _ hEM hMsolv
  have hamb04 : _root_.CFSG.FeitThompson.IsOddSimpleMinimal G :=
    ⟨hG.odd_natCard, hG.isSimpleGroup, hG.not_isMulCommutative, hG.isSolvable_of_ne_top⟩
  have hamb07 : _root_.CFSG.FeitThompson.IsFTAmbient G :=
    ⟨hG.isSimpleGroup, hG.not_isMulCommutative, hG.odd_natCard, hG.isSolvable_of_ne_top⟩
  have hcardE₁ : Nat.card ↥(E₁.subgroupOf E) = Nat.card ↥E₁ :=
    Nat.card_congr (subgroupOfEquivOfLe hE₁E).toEquiv
  have hπ : ∀ q ∈ (Nat.card ↥E₁).primeFactors, q ∈ tau1Primes M := fun q hq =>
    isPiSubgroup_iff.1 hE₁Hall.isPiSubgroup q (by rwa [hcardE₁])
  have hfac : ∀ q : ℕ, q.Prime → q ∣ Nat.card ↥E₁ →
      (Nat.card ↥E₁).factorization q = (Nat.card ↥E).factorization q := by
    intro q hq hqd
    have hmul : Nat.card ↥(E₁.subgroupOf E) * (E₁.subgroupOf E).index = Nat.card ↥E :=
      Subgroup.card_mul_index _
    have hqidx : ¬ q ∣ (E₁.subgroupOf E).index := fun hd =>
      hE₁Hall.notMem_of_mem_primeFactors_index q
        (Nat.mem_primeFactors.2 ⟨hq, hd, Subgroup.index_ne_zero_of_finite⟩)
        (hπ q (Nat.mem_primeFactors.2 ⟨hq, hqd, Nat.card_pos.ne'⟩))
    rw [← hmul, hcardE₁,
      Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hqidx, add_zero]
  obtain ⟨F₁, F₂, F₃, hsplit, -⟩ :=
    FNI_sigma_complement_three_factors h₁ G hamb04 M E ⟨hM, hsd⟩
  have hcyc : IsCyclic ↥E₁ := by
    obtain ⟨g, hg⟩ := exists_map_conj_eq_of_isHallSubgroup
      (isHallSubgroup_iff_isHallPiSubgroup.2 hsplit.isHall_E₁)
      (isHallSubgroup_iff_isHallPiSubgroup.2 hE₁Hall)
    have hF₁ : IsCyclic ↥(F₁.subgroupOf E) := isCyclic_subgroupOf hsplit.le_E₁ hsplit.isCyclic_E₁
    have h := (isCyclic_map_conj_iff (F₁.subgroupOf E) g).2 hF₁
    rw [hg] at h
    exact isCyclic_of_isCyclic_subgroupOf hE₁E h
  refine ⟨hcyc, ?_⟩
  have hkey : ∀ p : ℕ, p.Prime → p ∈ tau1Primes M → ∀ P : Subgroup G, P ≤ E₁ →
      Nat.card ↥P = p → sigmaCore M ⊓ centralizer (P : Set G) ≤ centralizer (E₁ : Set G) := by
    intro p hp hpτ P hPE₁ hPcard
    rw [← Subgroup.le_centralizer_iff]
    set D : Subgroup G := sigmaCore M ⊓ centralizer (P : Set G) with hD
    refine le_centralizer_of_forall_sylow_map_le_centralizer fun q hq Q => ?_
    have : Fact q.Prime := ⟨hq⟩
    set V : Subgroup G := (Q : Subgroup ↥E₁).map E₁.subtype with hV
    have hVE₁ : V ≤ E₁ := Subgroup.map_subtype_le _
    have hVcard : Nat.card ↥V = q ^ (Nat.card ↥E₁).factorization q := by
      rw [hV, Nat.card_congr ((Q : Subgroup ↥E₁).equivMapOfInjective E₁.subtype
        (Subgroup.subtype_injective E₁)).toEquiv.symm]
      exact Q.card_eq_multiplicity
    by_cases hVbot : V = ⊥
    · rw [hVbot]; exact bot_le
    have hqV : q ∣ Nat.card ↥V := by
      rw [hVcard]
      refine dvd_pow_self q ?_
      intro h0
      rw [h0, pow_zero] at hVcard
      exact hVbot (Subgroup.card_eq_one.1 hVcard)
    have hqE₁ : q ∣ Nat.card ↥E₁ := hqV.trans (Subgroup.card_dvd_of_le hVE₁)
    have hqτ : q ∈ tau1Primes M := hπ q (Nat.mem_primeFactors.2 ⟨hq, hqE₁, Nat.card_pos.ne'⟩)
    have hVcyc : IsCyclic ↥V := (isCyclic_map_subtype_iff _).2 inferInstance
    have hVsylow : _root_.CFSG.FeitThompson.IsSylowSubgroupOf q V E :=
      ⟨hVE₁.trans hE₁E, by rw [hVcard, hfac q hq hqE₁]⟩
    obtain ⟨z, hzV, hz⟩ := exists_mem_orderOf_eq_of_dvd hq hqV
    have hRcard : Nat.card ↥(zpowers z) = q := by rw [Nat.card_zpowers, hz]
    have hRV : (zpowers z : Subgroup G) ≤ V := zpowers_le.2 hzV
    have hRne : (zpowers z : Subgroup G) ≠ ⊥ := by
      intro h
      rw [h, Subgroup.card_bot] at hRcard
      exact hq.one_lt.ne hRcard
    have hRE₁ : (zpowers z : Subgroup G) ≤ E₁ := hRV.trans hVE₁
    have hE₁comm : (E₁ : Subgroup G) ≤ centralizer (E₁ : Set G) :=
      le_centralizer_iff_isMulCommutative.2 (@IsCyclic.isMulCommutative _ _ hcyc)
    have hRcentP : (zpowers z : Subgroup G) ≤ centIn E (P : Set G) :=
      le_inf (hRE₁.trans hE₁E)
        ((hRE₁.trans hE₁comm).trans (centralizer_le (SetLike.coe_subset_coe.2 hPE₁)))
    have hstep₁ := FTS_tau_one_prime_centralizer_inclusion h₂ G hG M hM E hEM hsd p q hp hq
      hpτ P (hPE₁.trans hE₁E) hPcard (zpowers z) hRcentP hRcard
    have hstep₂ := FTS_cyclic_sylow_complement_fixed_centralizer h₁ h₃ G hamb07 M hM E hEM
      hsd q hq V hVsylow hVbot hVcyc (zpowers z) hRV hRne
    rw [centIn_def, centIn_def] at hstep₁
    rw [hD]
    exact Subgroup.le_centralizer_iff.1 ((hstep₁.trans hstep₂.le).trans inf_le_right)
  intro X hXE₁ hXne
  have hXcard : Nat.card ↥X ≠ 1 := fun h => hXne (Subgroup.card_eq_one.1 h)
  have hp : ((Nat.card ↥X).minFac).Prime := Nat.minFac_prime hXcard
  have hpX : (Nat.card ↥X).minFac ∣ Nat.card ↥X := Nat.minFac_dvd _
  have hpE₁ : (Nat.card ↥X).minFac ∣ Nat.card ↥E₁ := hpX.trans (Subgroup.card_dvd_of_le hXE₁)
  have hpτ : (Nat.card ↥X).minFac ∈ tau1Primes M :=
    hπ _ (Nat.mem_primeFactors.2 ⟨hp, hpE₁, Nat.card_pos.ne'⟩)
  obtain ⟨y, hyX, hy⟩ := exists_mem_orderOf_eq_of_dvd hp hpX
  have hPcard : Nat.card ↥(zpowers y) = (Nat.card ↥X).minFac := by rw [Nat.card_zpowers, hy]
  have hPX : (zpowers y : Subgroup G) ≤ X := zpowers_le.2 hyX
  have hcent := hkey _ hp hpτ (zpowers y) (hPX.trans hXE₁) hPcard
  rw [centIn_def, centIn_def]
  refine le_antisymm ?_ (inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hXE₁)))
  have hmono : sigmaCore M ⊓ centralizer (X : Set G) ≤
      sigmaCore M ⊓ centralizer ((zpowers y : Subgroup G) : Set G) :=
    inf_le_inf_left _ (centralizer_le (SetLike.coe_subset_coe.2 hPX))
  exact le_inf (hmono.trans inf_le_left) (hmono.trans hcent)

end

end CFSG.FeitThompson.Proofs
