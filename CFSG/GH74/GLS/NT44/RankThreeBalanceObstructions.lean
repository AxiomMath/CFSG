module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalGlobal
import CFSG.GroupTheory.RankThreeCentralizer

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Th2.Bal
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance
open scoped commutatorElement

private theorem exists_rank_three_balance_obstruction_of_image
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hA8 : Nat.card ↥A = 8)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hAH : A ≤ Subgroup.centralizer ({a} : Set G))
    {k : ℕ} (hk : 1 ≤ k) {D : Subgroup G}
    (hD : CFSG.GH74.GLS.IsE k A D)
    {N : Subgroup (CFSG.GH74.CentralizerBar a)}
    (hNR : N ≤ ((CFSG.GH74.GLS.AG D ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf
      (Subgroup.centralizer ({a} : Set G))).map (CFSG.GH74.GLS.Th2.Bal.piBar a))
    (hN1 : N ≠ ⊥)
    (hbranch : 2 ≤ k ∨ N =
      ⁅((CFSG.GH74.GLS.AG D ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf
          (Subgroup.centralizer ({a} : Set G))).map (CFSG.GH74.GLS.Th2.Bal.piBar a),
        (A.subgroupOf (Subgroup.centralizer ({a} : Set G))).map
          (CFSG.GH74.GLS.Th2.Bal.piBar a)⁆) :
    ∃ L : Subgroup (CFSG.GH74.CentralizerBar a),
      let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
      let E : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (A.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      let F : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (D.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      let Y : Subgroup G := CFSG.GH74.GLS.AG D ⊓ H
      let R : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (Y.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      a ≠ 1 ∧ orderOf a = 2 ∧
        CFSG.GH74.GLS.IsE k A D ∧
        CFSG.IsComponent L ∧
        F ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        F ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) = ⊥ ∧
        R ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        R ≤ Subgroup.centralizer (F : Set (CFSG.GH74.CentralizerBar a)) ∧
        N ≠ ⊥ ∧ N ≤ R ∧
        ¬ N ≤ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        E ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) =
          Subgroup.zpowers (CFSG.GH74.GLS.Th2.Bal.piBar a ⟨a, hAH haA⟩) ∧
        ¬ CFSG.GH74.GLS.Th2.Bal.IsLocallyKBalanced k (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer ({a} : Set G) with hH
  set Y : Subgroup G := CFSG.GH74.GLS.AG D ⊓ H with hYdef
  set E : Subgroup (CFSG.GH74.CentralizerBar a) :=
    (A.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a) with hE
  set F : Subgroup (CFSG.GH74.CentralizerBar a) :=
    (D.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a) with hF
  set R : Subgroup (CFSG.GH74.CentralizerBar a) :=
    (Y.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a) with hR
  have hDA : D ≤ A := hD.1
  have hDel : CFSG.IsElementaryAbelian 2 ↥D := hD.2.1
  have hDrk : k ≤ pRank 2 ↥D := hD.2.2
  obtain ⟨hAc, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hA
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have hDH : D ≤ H := hDA.trans hAH
  have hDcard : Nat.card ↥D = 2 ^ pRank 2 ↥D :=
    C3.Layer1.Back.card_eq_two_pow_pRank hDel
  have hDk : 2 ^ k ≤ Nat.card D := by
    rw [hDcard]
    exact Nat.pow_le_pow_right (by norm_num) hDrk
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hAsq a haA) ha1
  have hY : ∀ d ∈ D, d ≠ 1 →
      Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
    fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
  have hNR' : N ≤ R := hNR
  have hRdelta : R ≤ deltaCore F := by
    simpa [hR, hF, hH] using
      map_le_deltaCore (a := a) (D := D) (Y := Y) hDsq hY
  obtain ⟨L, hL, hFL, hFfaith, hNL, hNnc, hnb⟩ :=
    exists_component_of_image (a := a) (k := k) hk hDH hDk hDsq hY hNR' hN1
  have hFnorm : F ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) :=
    fun f hf => mem_normalizer_of_conjSub_eq (hFL f hf)
  have hFcent : F ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro f hf
    rw [Subgroup.mem_bot]
    by_contra hf1
    obtain ⟨hfF, hfC⟩ := Subgroup.mem_inf.mp hf
    exact hFfaith f hfF hf1 (fun x hx =>
      (Subgroup.mem_centralizer_iff.mp hfC x hx).symm)
  have hRcentF : R ≤ Subgroup.centralizer (F : Set (CFSG.GH74.CentralizerBar a)) :=
    hRdelta.trans (deltaCore_le_centralizer F)
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    rintro _ ⟨d₀, hd₀, rfl⟩
    have hdD : (d₀ : G) ∈ D := Subgroup.mem_subgroupOf.mp hd₀
    have : d₀ * d₀ = 1 := Subtype.ext (hDsq _ hdD)
    rw [← map_mul, this, map_one]
  have hFcard : Nat.card F = Nat.card D := by
    rw [hF, card_map_piBar hDsq hDH]
  have hFk : 2 ^ k ≤ Nat.card F := by
    rw [hFcard]
    exact hDk
  obtain ⟨f0, hf0F, hf01⟩ :=
    exists_ne_one_of_two_pow_le (F := F) (k := k) hk hFk
  have hf0sq : f0 * f0 = 1 := hF2 f0 hf0F
  have hFne : F ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hf0F
    exact hf01 hf0F
  have hFE : F ≤ E := by
    rw [hF, hE]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hDA)
  have hEcard : Nat.card E = 8 := by
    rw [hE, card_map_piBar hAsq hAH, hA8]
  have hEelem : CFSG.IsElementaryAbelian 2 ↥E := by
    rw [hE]
    have : CFSG.IsElementaryAbelian 2 ↥A := hA
    have : CFSG.IsElementaryAbelian 2 ↥(A.subgroupOf H) :=
      CFSG.IsElementaryAbelian.subgroupOf (p := 2) hAH
    exact CFSG.IsElementaryAbelian.map (CFSG.GH74.GLS.Th2.Bal.piBar a)
  have hNnc' : ¬ N ≤ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) := by
    intro hle
    apply hNnc
    intro n hn x hx
    exact (Subgroup.mem_centralizer_iff.mp (hle hn) x hx).symm
  have hRnorm : R ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) := by
    intro r hr
    exact mem_normalizer_of_conjSub_eq
      (conjSub_eq_of_mem_involutionOddCore hL hf0sq (hFL f0 hf0F)
        (deltaCore_le_involutionOddCore hf0F hf01 (hRdelta hr)))
  have he1 : piBar a ⟨a, hAH haA⟩ ≠ 1 := by
    intro h
    have hmem1 : (1 : ↥H) ∈ A.subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr A.one_mem
    have hcontra : (⟨a, hAH haA⟩ : ↥H) = 1 :=
      piBar_injOn (a := a) (D := A) hAsq (Subgroup.mem_subgroupOf.mpr haA) hmem1
        (by simpa using h)
    exact ha1 (congrArg Subtype.val hcontra)
  have ha0sq : (⟨a, hAH haA⟩ : ↥H) * ⟨a, hAH haA⟩ = 1 :=
    Subtype.ext (hAsq a haA)
  have he2 : orderOf (piBar a ⟨a, hAH haA⟩) = 2 := by
    refine orderOf_eq_prime ?_ he1
    rw [sq, ← map_mul, ha0sq, map_one]
  have heE : piBar a ⟨a, hAH haA⟩ ∈ E := by
    rw [hE]
    exact ⟨⟨a, hAH haA⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
  have ha0_center : (⟨a, hAH haA⟩ : ↥H) ∈ Subgroup.center ↥H := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp x.2
  have he_center : piBar a ⟨a, hAH haA⟩ ∈
      Subgroup.center (CFSG.GH74.CentralizerBar a) :=
    Subgroup.map_center_le_center (f := CFSG.GH74.GLS.Th2.Bal.piBar a)
      (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H))
      (Subgroup.mem_map_of_mem (CFSG.GH74.GLS.Th2.Bal.piBar a) ha0_center)
  have heL : piBar a ⟨a, hAH haA⟩ ∈
      Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) :=
    Subgroup.center_le_centralizer (L : Set (CFSG.GH74.CentralizerBar a)) he_center
  have hcase : 4 ≤ Nat.card ↥F ∨
      ∃ Y' : Subgroup (CFSG.GH74.CentralizerBar a),
        Y' ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        Y' ≤ Subgroup.centralizer (F : Set (CFSG.GH74.CentralizerBar a)) ∧
        ¬ ⁅Y', E⁆ ≤
          Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) := by
    rcases hbranch with hk2 | hN
    · left
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        _ ≤ Nat.card F := hFk
    · right
      refine ⟨R, hRnorm, hRcentF, ?_⟩
      have hN' : N = ⁅R, E⁆ := hN
      rwa [← hN']
  have hkernel : E ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) =
      Subgroup.zpowers (piBar a ⟨a, hAH haA⟩) :=
    CFSG.GroupTheory.inf_centralizer_eq_zpowers_of_rank_three
      hEelem hEcard heE he2 heL hFE hFne hFcent hcase
  refine ⟨L, ?_⟩
  exact ⟨ha1, ha2, hD, hL, hFnorm, hFcent, hRnorm, hRcentF, hN1, hNR',
    hNnc', hkernel, hnb⟩

theorem exists_strong_two_obstruction_with_rank_three_centralizer
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hA8 : Nat.card ↥A = 8)
    (hnot : ¬ CFSG.GH74.GLS.IsKBal 2 A) :
    ∃ (a : G) (haA : a ∈ A)
      (hAH : A ≤ Subgroup.centralizer ({a} : Set G))
      (D : Subgroup G) (L : Subgroup (CFSG.GH74.CentralizerBar a)),
      let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
      let E : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (A.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      let F : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (D.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      let Y : Subgroup G := CFSG.GH74.GLS.AG D ⊓ H
      let R : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (Y.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      let N : Subgroup (CFSG.GH74.CentralizerBar a) := R
      a ≠ 1 ∧ orderOf a = 2 ∧
        CFSG.GH74.GLS.IsE 2 A D ∧
        CFSG.IsComponent L ∧
        F ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        F ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) = ⊥ ∧
        R ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        R ≤ Subgroup.centralizer (F : Set (CFSG.GH74.CentralizerBar a)) ∧
        N ≠ ⊥ ∧ N ≤ R ∧
        ¬ N ≤ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        E ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) =
          Subgroup.zpowers (CFSG.GH74.GLS.Th2.Bal.piBar a ⟨a, hAH haA⟩) ∧
        ¬ CFSG.GH74.GLS.Th2.Bal.IsLocallyKBalanced 2 (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold CFSG.GH74.GLS.IsKBal at hnot
  push Not at hnot
  obtain ⟨D, hD, a, haA, ha1, hnle⟩ := hnot
  obtain ⟨hAc, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hA
  have hAH : A ≤ Subgroup.centralizer ({a} : Set G) :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hAc x hx a haA)
  obtain ⟨c, hc, hcn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  set H : Subgroup G := Subgroup.centralizer ({a} : Set G) with hH
  set Y : Subgroup G := CFSG.GH74.GLS.AG D ⊓ H with hYdef
  set R : Subgroup (CFSG.GH74.CentralizerBar a) :=
    (Y.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a) with hR
  have hR1 : R ≠ ⊥ := by
    intro hbot
    apply hcn
    have hmem : piBar a ⟨c, hc.2⟩ ∈ R := by
      rw [hR]
      exact ⟨⟨c, hc.2⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
    rw [hbot, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
    exact ⟨⟨c, hc.2⟩, hmem, rfl⟩
  obtain ⟨L, hpack⟩ :=
    exists_rank_three_balance_obstruction_of_image (k := 2) hA hA8 haA ha1 hAH
      (by norm_num) hD (le_refl _) hR1 (Or.inl (le_refl 2))
  exact ⟨a, haA, hAH, D, L, hpack⟩

theorem exists_weak_one_obstruction_with_rank_three_centralizer
    {G : Type} [Group G] [Finite G] {A : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hA8 : Nat.card ↥A = 8)
    (hnot : ¬ CFSG.GH74.GLS.IsWeakKBal 1 A) :
    ∃ (a : G) (haA : a ∈ A)
      (hAH : A ≤ Subgroup.centralizer ({a} : Set G))
      (D : Subgroup G) (L : Subgroup (CFSG.GH74.CentralizerBar a)),
      let H : Subgroup G := Subgroup.centralizer ({a} : Set G)
      let E : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (A.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      let F : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (D.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      let Y : Subgroup G := CFSG.GH74.GLS.AG D ⊓ H
      let R : Subgroup (CFSG.GH74.CentralizerBar a) :=
        (Y.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a)
      let N : Subgroup (CFSG.GH74.CentralizerBar a) := ⁅R, E⁆
      a ≠ 1 ∧ orderOf a = 2 ∧
        CFSG.GH74.GLS.IsE 1 A D ∧
        CFSG.IsComponent L ∧
        F ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        F ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) = ⊥ ∧
        R ≤ Subgroup.normalizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        R ≤ Subgroup.centralizer (F : Set (CFSG.GH74.CentralizerBar a)) ∧
        N ≠ ⊥ ∧ N ≤ R ∧
        ¬ N ≤ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) ∧
        E ⊓ Subgroup.centralizer (L : Set (CFSG.GH74.CentralizerBar a)) =
          Subgroup.zpowers (CFSG.GH74.GLS.Th2.Bal.piBar a ⟨a, hAH haA⟩) ∧
        ¬ CFSG.GH74.GLS.Th2.Bal.IsLocallyKBalanced 1 (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold CFSG.GH74.GLS.IsWeakKBal at hnot
  push Not at hnot
  obtain ⟨D, hD, a, haA, ha1, c, hc, b, hbA, hcb⟩ := hnot
  have hDA : D ≤ A := hD.1
  obtain ⟨hAc, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hA
  have hAH : A ≤ Subgroup.centralizer ({a} : Set G) :=
    fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hAc x hx a haA)
  set H : Subgroup G := Subgroup.centralizer ({a} : Set G) with hH
  set Y : Subgroup G := CFSG.GH74.GLS.AG D ⊓ H with hYdef
  set E : Subgroup (CFSG.GH74.CentralizerBar a) :=
    (A.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a) with hE
  set R : Subgroup (CFSG.GH74.CentralizerBar a) :=
    (Y.subgroupOf H).map (CFSG.GH74.GLS.Th2.Bal.piBar a) with hR
  set N : Subgroup (CFSG.GH74.CentralizerBar a) := ⁅R, E⁆ with hN
  have hNR : N ≤ R := by
    rw [hN, Subgroup.commutator_le]
    rintro _ ⟨y0, hy0, rfl⟩ _ ⟨b0, hb0, rfl⟩
    have hyY : (y0 : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy0
    have hbA' : (b0 : G) ∈ A := Subgroup.mem_subgroupOf.mp hb0
    refine ⟨⁅y0, b0⁆, Subgroup.mem_subgroupOf.mpr ?_, map_commutatorElement _ _ _⟩
    have hcomm : ((⁅y0, b0⁆ : ↥H) : G) =
        (y0 : G) * ((b0 : G) * (y0 : G)⁻¹ * (b0 : G)⁻¹) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hcomm]
    refine Y.mul_mem hyY ⟨?_, ?_⟩
    · exact conj_mem_AG (fun d hd => hAc _ hbA' d (hDA hd)) ((AG D).inv_mem hyY.1)
    · exact H.mul_mem (H.mul_mem b0.2 (H.inv_mem y0.2)) (H.inv_mem b0.2)
  have hN1 : N ≠ ⊥ := by
    intro hbot
    apply hcb
    have hcH : c ∈ H := hc.2
    have hbH : b ∈ H := hAH hbA
    have hmem : piBar a ⁅(⟨c, hcH⟩ : ↥H), ⟨b, hbH⟩⁆ ∈ N := by
      rw [hN, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator
        ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
        ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hbA, rfl⟩
    rw [hbot, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
    exact ⟨_, hmem, rfl⟩
  obtain ⟨L, hpack⟩ :=
    exists_rank_three_balance_obstruction_of_image (k := 1) hA hA8 haA ha1 hAH
      (by norm_num : 1 ≤ 1) hD hNR hN1 (Or.inr rfl)
  exact ⟨a, haA, hAH, D, L, hpack⟩

end CFSG.GH74.GLS.NT44

end
