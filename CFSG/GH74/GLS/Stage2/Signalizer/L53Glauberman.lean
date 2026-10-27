module

public import CFSG.GH74.GLS.Stage2.Signalizer.L53Even
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Crit
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Kfam
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L53

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Bg
open scoped commutatorElement

variable {M : Type} [Group M]

theorem A_mem_classTwo {p : ℕ} {T A S : Subgroup M} (hS : Setup p T A) (hTS : T ≤ S) :
    A ∈ classTwo S := by
  refine ⟨hS.leT.trans hTS, ?_⟩
  have h1 : ⁅A, A⁆ ≤ centralizer (A : Set M) :=
    ((Subgroup.commutator_mono_left hS.leT).trans hS.commTA).trans inf_le_right
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h1

theorem exists_target [Finite M] {p : ℕ} [Fact p.Prime] {T A S : Subgroup M} (hS : Setup p T A)
    (hTS : T ≤ S) (hbad : ¬ ∀ m, 1 ≤ m → gen (Kfam S m) ≤ T) : Target A S := by
  classical
  have hAn := hS.normalA
  have hAS := A_mem_classTwo hS hTS
  obtain ⟨m, hm⟩ := not_forall.mp hbad
  obtain ⟨hm1, hm2⟩ := not_imp.mp hm
  have hex : ∃ n, 1 ≤ n ∧ ¬ gen (Kfam S n) ≤ T := ⟨m, hm1, hm2⟩
  obtain ⟨n, hn1, hnbad, hmin⟩ : ∃ n, 1 ≤ n ∧ ¬ gen (Kfam S n) ≤ T ∧
      ∀ m, m < n → 1 ≤ m → gen (Kfam S m) ≤ T := by
    refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun m hlt hm1 => ?_⟩
    by_contra hc
    exact Nat.find_min hex hlt ⟨hm1, hc⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  by_cases hA : A ∈ Kfam S k
  ·
    have hAQ : A ≤ gen (Kfam S k) := le_gen hA
    obtain ⟨B, hB, hBT⟩ : ∃ B ∈ Kfam S (k + 1), ¬ B ≤ T := by
      by_contra hc
      push Not at hc
      exact hnbad (gen_le hc)
    obtain ⟨g, hgB, hgT⟩ := IsConcreteLE.not_le_iff_exists.mp hBT
    have hBcl := Kfam_subset_classTwo S _ hB
    have hgS : g ∈ S := hBcl.1 hgB
    by_cases hk : Even k
    · rw [Kfam_succ_even S hk] at hB
      obtain ⟨-, hQnorm, hall⟩ := hB
      have hAB : A ≤ normalizer (B : Set M) := hAQ.trans hQnorm
      have hBcc : ⁅B, B⁆ ≤ B ⊓ centralizer (B : Set M) :=
        le_inf (Subgroup.commutator_le_of_le le_rfl le_rfl)
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBcl.2)
      by_cases hZB : B ⊓ centralizer (B : Set M) ≤ T
      · refine even_branch hS hgB hgT hgS hAB hBcc hZB ?_
        intro A' hA'A hBA' h1 h2
        refine hall A' ⟨hA'A.trans (hS.leT.trans hTS), ?_⟩ (hA'A.trans hAQ) hBA' h1 h2
        exact le_bot_iff.mp ((Subgroup.commutator_mono (Subgroup.commutator_mono hA'A hA'A)
          hA'A).trans hAS.2.le)
      · obtain ⟨g', hg', hg'T⟩ := IsConcreteLE.not_le_iff_exists.mp hZB
        refine target_of_quad hS (hBcl.1 hg'.1) hg'T fun X Y hc hXA x hx => ?_
        rw [quad_of_zB hAB hg' x (hXA hx)]
        exact Y.one_mem
    · rw [Kfam_succ_odd S hk] at hB
      have h1 : ⁅A, B⁆ ≤ B ⊓ centralizer (B : Set M) := by
        rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono_right hAQ).trans hB.2
      refine target_of_quad hS hgS hgT fun X Y hc hXA x hx => ?_
      rw [quad_of_up hgB h1 x (hXA hx)]
      exact Y.one_mem
  ·
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hA hAS
    by_cases hk : Even k
    · exfalso
      apply hA
      obtain ⟨j, hj⟩ := hk
      have hk' : ¬ Even (k - 1) := by
        rw [Nat.not_even_iff_odd]
        exact ⟨j - 1, by omega⟩
      have e : Kfam S k = Kup S (gen (Kfam S (k - 1))) := by
        have := Kfam_succ_odd S hk'
        rwa [Nat.sub_add_cancel (by omega)] at this
      rw [e]
      refine ⟨hAS, ?_⟩
      have hQ' : gen (Kfam S (k - 1)) ≤ T := hmin (k - 1) (by omega) (by omega)
      calc ⁅A, gen (Kfam S (k - 1))⁆ ≤ ⁅A, T⁆ := Subgroup.commutator_mono_right hQ'
        _ = ⁅T, A⁆ := Subgroup.commutator_comm A T
        _ ≤ A ⊓ centralizer (A : Set M) := hS.commTA
    · have hk1 : k = 1 := by
        by_contra hne
        obtain ⟨j, hj⟩ : Odd k := Nat.not_even_iff_odd.mp hk
        have hj1 : 1 ≤ j := by omega
        have h1 := (Kfam_mono_aux S j).1
        have hk2 : k + 1 = 2 * j + 2 := by omega
        apply hnbad
        rw [hk2]
        exact (gen_mono h1).trans (hmin (2 * j) (by omega) (by omega))
      subst hk1
      have hA' : A ∉ Klow S (gen (Kfam S 0)) := by
        rwa [Kfam_succ_even S (by decide : Even 0)] at hA
      have hQ₀ : gen (Kfam S 0) ≤ normalizer (A : Set M) :=
        le_top.trans (normalizer_top_of_normal hAn)
      by_contra hT
      apply hA'
      refine ⟨hAS, hQ₀, ?_⟩
      intro A₂ hA₂ hA₂Q hAA₂ h1 h2
      by_contra h3
      exact hT (lowfail_branch hS hA₂.1 hAA₂ h1 h2 h3)

theorem glauberman_kinfty_thm :
    ∀ (M : Type) [Group M] [Finite M] (p : ℕ), p.Prime → ∀ S : Subgroup M, IsPGroup p S →
      pCore p M ≤ S → generalizedFitting M = pCore p M →
        ((kInfty S).Normal ∧ (kLowInfty S).Normal) ∨
        ∃ g ∈ S, ∃ A : Subgroup M, A ≤ pCore p M ∧
          CFSG.SectionRank.Ccomm.IsThompsonCritical (A.subgroupOf (pCore p M)) ∧
          ∃ X Y : Subgroup M, X.Normal ∧ Y.Normal ∧ Y ≤ X ∧
            (∀ Z : Subgroup M, Z.Normal → Y ≤ Z → Z ≤ X → Z = Y ∨ Z = X) ∧ X ≤ A ∧
            ⁅⁅X, zpowers g⁆, zpowers g⁆ ≤ Y ∧ ¬ ⁅X, zpowers g⁆ ≤ Y := by
  intro M _ _ p hp S hS hTS hF
  have hpf : Fact p.Prime := ⟨hp⟩
  have hTn : (pCore p M).Normal := CFSG.pCore_normal
  have hTp : IsPGroup p ↥(pCore p M) := CFSG.pCore_isPGroup
  have hmax : ∀ N : Subgroup M, N.Normal → IsPGroup p ↥N → N ≤ pCore p M :=
    fun N hN hNp => le_sSup ⟨hN, hNp⟩
  have hcent : centralizer ((pCore p M : Subgroup M) : Set M) ≤ pCore p M := by
    have := CFSG.centralizer_generalizedFitting_le M
    rwa [hF] at this
  by_cases hall : ∀ m, 1 ≤ m → gen (Kfam S m) ≤ pCore p M
  · left
    exact normal_of_le hTn hTS hall
  · right
    obtain ⟨A, hAT, hcrit, hSet⟩ := exists_setup hTn hTp hmax hcent
    obtain ⟨g, hgS, X, Y, hc, hXA, hq, x, hx, hxY⟩ := exists_target hSet hTS hall
    refine ⟨g, hgS, A, hAT, hcrit, X, Y, hc.1, hc.2.1, hc.2.2.1.le, hc.2.2.2, hXA,
      comm_comm_le_of_quad hc.2.1 hq, ?_⟩
    intro hle
    exact hxY (((comm_zpowers_le_iff hc.2.1).mp hle) x hx)

end CFSG.GH74.GLS.Stage2.Signalizer.L53
