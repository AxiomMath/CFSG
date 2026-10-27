module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointTypes

import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.O1517bLayer
import CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightBridge
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Two
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.ThreePart
import CFSG.GroupTheory.SupCommute
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GH74.Uniqueness.Bender.Core

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section15

open Subgroup

variable {X : Type} [Group X] [Finite X] {p : ℕ} {P A Y : Subgroup X}

private lemma exists_sylow_eq_of_isSylowOf {Q : Subgroup X}
    (hQ : CFSG.ABGLocalTools.IsSylowOf 3 Q ⊤) :
    ∃ R : Sylow 3 X, (R : Subgroup X) = Q := by
  obtain ⟨S, hS⟩ := hQ
  refine ⟨Sylow.mapSurjective (f := (⊤ : Subgroup X).subtype)
    (fun x => ⟨⟨x, Subgroup.mem_top x⟩, rfl⟩) S, ?_⟩
  exact (Sylow.coe_mapSurjective _ _).trans hS

private lemma pCore_eq_bot_of_not_le
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    CFSG.pCore 3 ↥L = ⊥ := by
  obtain ⟨R, hR⟩ := exists_sylow_eq_of_isSylowOf h.sylow
  have hweak : CFSG.Open.GLBWeakCore 3 (R : Subgroup X) ≤ Y := by
    unfold CFSG.Open.GLBWeakCore
    refine (CFSG.RankThreeCoreUniqueness.Helpers.aschCore_le_gamma 2 3
      (R : Subgroup X)).trans ?_
    rw [hR]
    exact h.gamma
  have hnotle : ¬ L ≤ CFSG.Open.GLBWeakCore 3 (R : Subgroup X) :=
    fun hle => hLY (hle.trans hweak)
  have hrank : 3 ≤ CFSG.Open.pRank 3 (R : Subgroup X) := by
    rw [hR, h.rank]
  exact hKA X h.catalog 3 R L Nat.prime_three (by norm_num) hrank
    (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.isComponentOf_top_of_isComponent' hL) hnotle

private lemma center_eq_bot_of_pCore_eq_bot {L : Subgroup X}
    (hcore : CFSG.pPrimeCore 3 X = ⊥) (hL : CFSG.IsComponent L)
    (hp : CFSG.pCore 3 ↥L = ⊥) : Subgroup.center ↥L = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcore' : CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := X) 3 = ⊥ := hcore
  have hZ : IsPGroup 3 (Subgroup.center ↥L) :=
    CFSG.AGLEmbedding.isPGroup_center_of_isComponentOf Nat.prime_three hcore'
      (CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.isComponentOf_top_of_isComponent' hL)
  have hle : Subgroup.center ↥L ≤ CFSG.pCore 3 ↥L := le_sSup ⟨inferInstance, hZ⟩
  rw [hp] at hle
  exact le_bot_iff.mp hle

theorem O1517bRed.center_eq_bot
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    Subgroup.center ↥L = ⊥ :=
  center_eq_bot_of_pCore_eq_bot h.core hL (pCore_eq_bot_of_not_le hKA h hL hLY)

private lemma inf_A_eq_bot
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) : A ⊓ L = ⊥ := by
  have hc : L ≤ Subgroup.centralizer (A : Set X) := h.le_centralizer_A hL
  have hcent : A ≤ Subgroup.centralizer (L : Set X) := Subgroup.le_centralizer_iff.mp hc
  rw [eq_bot_iff]
  intro x hx
  have hxZ : (⟨x, hx.2⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hcent hx.1) l l.2)
  have hZ := O1517bRed.center_eq_bot hKA h hL hLY
  rw [hZ, Subgroup.mem_bot] at hxZ
  simpa using congrArg Subtype.val hxZ

private lemma eq_one_of_mem_isComponent_of_centralizes
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) {y : X} (hyL : y ∈ L)
    (hycent : y ∈ Subgroup.centralizer (L : Set X)) : y = 1 := by
  have hZ := O1517bRed.center_eq_bot hKA h hL hLY
  have hyZ : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hycent (l : X) l.2)
  rw [hZ, Subgroup.mem_bot] at hyZ
  exact congrArg Subtype.val hyZ

private lemma exists_order_three_pair
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    ∃ a x₀ : X, a ∈ A ∧ orderOf a = 3 ∧ x₀ ∈ L ∧ orderOf x₀ = 3 ∧
      x₀ ∉ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3L : 3 ∣ Nat.card L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card Nat.prime_three h.core hL
  obtain ⟨x₀L, hx₀ordL⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  let x₀ : X := (x₀L : X)
  have hx₀L : x₀ ∈ L := x₀L.2
  have hx₀ord : orderOf x₀ = 3 := by
    simpa [x₀] using (Subgroup.orderOf_coe x₀L).trans hx₀ordL
  have hx₀ne : x₀ ≠ 1 := by
    intro h1
    have : orderOf x₀ = 1 := by rw [h1, orderOf_one]
    omega
  have hAne : A ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card A = 1 := by rw [hbot, Subgroup.card_bot]
    have h3 : Nat.card A = 3 := h.card_A
    rw [h1] at h3
    norm_num at h3
  obtain ⟨⟨a, haA⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haord : orderOf a = 3 := by
    have hdiv : orderOf a ∣ 3 := by
      rw [← Nat.card_zpowers]
      exact (Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr haA)).trans
        (by rw [h.card_A])
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with h1 | h3
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1'
    · exact h3
  have hx₀_not : x₀ ∉ Subgroup.zpowers a := by
    intro hx
    have hxinf : x₀ ∈ A ⊓ L := ⟨(Subgroup.zpowers_le.mpr haA) hx, hx₀L⟩
    rw [inf_A_eq_bot hKA h hL hLY] at hxinf
    exact hx₀ne (Subgroup.mem_bot.mp hxinf)
  exact ⟨a, x₀, haA, haord, hx₀L, hx₀ord, hx₀_not⟩

private lemma moved_commutations
    (h : O1517bRed X p P A Y) {L L₁ L₂ : Subgroup X}
    (hL : CFSG.IsComponent L) (hL₁ : CFSG.IsComponent L₁) (hL₂ : CFSG.IsComponent L₂)
    (hL₁ne : L ≠ L₁) (hL₂ne : L ≠ L₂) (hL₁₂ne : L₁ ≠ L₂)
    {a x₀ x₁ x₂ : X} (haA : a ∈ A) (hx₀L : x₀ ∈ L) (hx₁L₁ : x₁ ∈ L₁)
    (hx₂L₂ : x₂ ∈ L₂) :
    a * x₀ = x₀ * a ∧ a * x₁ = x₁ * a ∧ a * x₂ = x₂ * a ∧
      x₀ * x₁ = x₁ * x₀ ∧ x₀ * x₂ = x₂ * x₀ ∧ x₁ * x₂ = x₂ * x₁ := by
  have hcomm : ∀ {K M : Subgroup X}, CFSG.IsComponent K → CFSG.IsComponent M → K ≠ M →
      ∀ y ∈ K, ∀ z ∈ M, y * z = z * y := by
    intro K M hK hM hne y hy z hz
    rcases CFSG.LocalCores.distinct_components_commute hK hM with heq | hcm
    · exact absurd heq hne
    · have hcent := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcm
      exact (Subgroup.mem_centralizer_iff.mp (hcent hy) z hz).symm
  have hcentA : ∀ (K : Subgroup X), CFSG.IsComponent K →
      A ≤ Subgroup.centralizer (K : Set X) := fun K hK =>
    Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hK)
  refine ⟨?_, ?_, ?_, hcomm hL hL₁ hL₁ne x₀ hx₀L x₁ hx₁L₁,
    hcomm hL hL₂ hL₂ne x₀ hx₀L x₂ hx₂L₂, hcomm hL₁ hL₂ hL₁₂ne x₁ hx₁L₁ x₂ hx₂L₂⟩
  · exact (Subgroup.mem_centralizer_iff.mp (hcentA L hL haA) x₀ hx₀L).symm
  · exact (Subgroup.mem_centralizer_iff.mp (hcentA L₁ hL₁ haA) x₁ hx₁L₁).symm
  · exact (Subgroup.mem_centralizer_iff.mp (hcentA L₂ hL₂ haA) x₂ hx₂L₂).symm

private lemma not_mem_sup_zpowers_of_isComponent
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L M : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hM : CFSG.IsComponent M) (hML : M ≠ L) (hMY : ¬ M ≤ Y)
    {a x₀ x₁ : X} (haA : a ∈ A) (hx₀L : x₀ ∈ L)
    (hx₁M : x₁ ∈ M) (hx₁ne : x₁ ≠ 1) :
    x₁ ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers x₀ := by
  have hcentA : A ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hL)
  have hax₀ : a * x₀ = x₀ * a :=
    (Subgroup.mem_centralizer_iff.mp (hcentA haA) x₀ hx₀L).symm
  have hcentM : M ≤ Subgroup.centralizer (L : Set X) := by
    rcases CFSG.LocalCores.distinct_components_commute hM hL with heq | hcm
    · exact absurd heq hML
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcm
  have hx₁cent : x₁ ∈ Subgroup.centralizer (L : Set X) := hcentM hx₁M
  intro hx
  have hcomm_a : ∀ p ∈ Subgroup.zpowers a, ∀ q ∈ Subgroup.zpowers x₀, Commute p q := by
    intro p hp q hq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    exact Commute.zpow_left (Commute.zpow_right hax₀ j) i
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    (CFSG.mem_sup_of_commute (A := Subgroup.zpowers a)
      (B := Subgroup.zpowers x₀) hcomm_a).mp hx
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  have hx₀j_eq : x₀ ^ j = (a ^ i)⁻¹ * x₁ := by
    rw [← hpq]
    group
  have hx₀j_cent : x₀ ^ j ∈ Subgroup.centralizer (L : Set X) := by
    rw [hx₀j_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _
      (hcentA (Subgroup.zpow_mem A haA i))) hx₁cent
  have hx₀j1 : x₀ ^ j = 1 := eq_one_of_mem_isComponent_of_centralizes hKA h hL hLY
    (Subgroup.zpow_mem L hx₀L j) hx₀j_cent
  have hx₁_eq : x₁ = a ^ i := by
    rw [← hpq, hx₀j1, mul_one]
  have hx₁A : x₁ ∈ A := by
    rw [hx₁_eq]
    exact Subgroup.zpow_mem A haA i
  have hx₁inf : x₁ ∈ A ⊓ M := ⟨hx₁A, hx₁M⟩
  rw [inf_A_eq_bot hKA h hM hMY] at hx₁inf
  exact hx₁ne (Subgroup.mem_bot.mp hx₁inf)

private lemma exists_zpow_zpow_mul_of_mem_sup_sup
    (h : O1517bRed X p P A Y) {L M : Subgroup X}
    (hL : CFSG.IsComponent L) (hM : CFSG.IsComponent M) (hML : M ≠ L)
    {a x₀ x₁ x₂ : X} (haA : a ∈ A) (hx₀L : x₀ ∈ L) (hx₁M : x₁ ∈ M)
    (hx : x₂ ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁) :
    ∃ i j k : ℤ, x₂ = (a ^ i * x₀ ^ j) * x₁ ^ k := by
  have hcentA : A ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hL)
  have hcentAM : A ≤ Subgroup.centralizer (M : Set X) :=
    Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hM)
  have hcentML : M ≤ Subgroup.centralizer (L : Set X) := by
    rcases CFSG.LocalCores.distinct_components_commute hM hL with heq | hcm
    · exact absurd heq hML
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcm
  have hx₁centL : x₁ ∈ Subgroup.centralizer (L : Set X) := hcentML hx₁M
  have hax₀ : Commute a x₀ :=
    (Subgroup.mem_centralizer_iff.mp (hcentA haA) x₀ hx₀L).symm
  have hax₁ : Commute a x₁ :=
    (Subgroup.mem_centralizer_iff.mp (hcentAM haA) x₁ hx₁M).symm
  have hx₀x₁ : Commute x₀ x₁ :=
    Subgroup.mem_centralizer_iff.mp hx₁centL x₀ hx₀L
  have hcomm_E0_x₁ : ∀ e ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀ : Subgroup X),
      ∀ z ∈ Subgroup.zpowers x₁, Commute e z := by
    have h := CFSG.le_centralizer_sup_of_commute_both (A := Subgroup.zpowers x₁)
      (B := Subgroup.zpowers a) (C := Subgroup.zpowers x₀)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hax₀ j) i)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hax₁.symm j) i)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hx₀x₁.symm j) i)
    intro e he z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_right (show Commute e x₁ from
      Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_zpowers x₁)) e he) k
  obtain ⟨u, hu, r, hr, hur⟩ :=
    (CFSG.mem_sup_of_commute (A := Subgroup.zpowers a ⊔ Subgroup.zpowers x₀)
      (B := Subgroup.zpowers x₁) hcomm_E0_x₁).mp hx
  have hcomm_a : ∀ p ∈ Subgroup.zpowers a, ∀ q ∈ Subgroup.zpowers x₀, Commute p q := by
    intro p hp q hq
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    exact Commute.zpow_left (Commute.zpow_right hax₀ j) i
  obtain ⟨p, hp, q, hq, hpq⟩ :=
    (CFSG.mem_sup_of_commute (A := Subgroup.zpowers a)
      (B := Subgroup.zpowers x₀) hcomm_a).mp hu
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hr
  exact ⟨i, j, k, by rw [hpq, hur]⟩

private lemma exists_zpow_mul_of_mem_sup_sup
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L M N : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hM : CFSG.IsComponent M) (hML : M ≠ L)
    (hN : CFSG.IsComponent N) (hNL : N ≠ L)
    {a x₀ x₁ x₂ : X} (haA : a ∈ A) (hx₀L : x₀ ∈ L)
    (hx₁M : x₁ ∈ M) (hx₂N : x₂ ∈ N)
    (hx : x₂ ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁) :
    ∃ i k : ℤ, x₂ = a ^ i * x₁ ^ k := by
  obtain ⟨i, j, k, hx₂_eq⟩ :=
    exists_zpow_zpow_mul_of_mem_sup_sup h hL hM hML haA hx₀L hx₁M hx
  have hcentA : A ≤ Subgroup.centralizer (L : Set X) :=
    Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hL)
  have hcentML : M ≤ Subgroup.centralizer (L : Set X) := by
    rcases CFSG.LocalCores.distinct_components_commute hM hL with heq | hcm
    · exact absurd heq hML
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcm
  have hcentNL : N ≤ Subgroup.centralizer (L : Set X) := by
    rcases CFSG.LocalCores.distinct_components_commute hN hL with heq | hcm
    · exact absurd heq hNL
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcm
  have hx₁centL : x₁ ∈ Subgroup.centralizer (L : Set X) := hcentML hx₁M
  have hx₂centL : x₂ ∈ Subgroup.centralizer (L : Set X) := hcentNL hx₂N
  have hx₀j_eq : x₀ ^ j = (a ^ i)⁻¹ * x₂ * (x₁ ^ k)⁻¹ := by
    rw [hx₂_eq]
    group
  have hx₀j_cent : x₀ ^ j ∈ Subgroup.centralizer (L : Set X) := by
    rw [hx₀j_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ (hcentA (Subgroup.zpow_mem A haA i))) hx₂centL)
      (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hx₁centL k))
  have hx₀j1 : x₀ ^ j = 1 := eq_one_of_mem_isComponent_of_centralizes hKA h hL hLY
    (Subgroup.zpow_mem L hx₀L j) hx₀j_cent
  refine ⟨i, k, ?_⟩
  rw [hx₂_eq, hx₀j1, mul_one]

private lemma not_mem_sup_sup_zpowers_of_isComponent
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L M N : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hM : CFSG.IsComponent M) (hML : M ≠ L) (hMY : ¬ M ≤ Y)
    (hN : CFSG.IsComponent N) (hNL : N ≠ L) (hNM : N ≠ M) (hNY : ¬ N ≤ Y)
    {a x₀ x₁ x₂ : X} (haA : a ∈ A) (hx₀L : x₀ ∈ L)
    (hx₁M : x₁ ∈ M) (hx₂N : x₂ ∈ N) (hx₂ne : x₂ ≠ 1) :
    x₂ ∉ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁ := by
  intro hx
  obtain ⟨i, k, hx₂⟩ :=
    exists_zpow_mul_of_mem_sup_sup hKA h hL hLY hM hML hN hNL haA hx₀L hx₁M hx₂N hx
  have hcentAM : A ≤ Subgroup.centralizer (M : Set X) :=
    Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hM)
  have hcentNM : N ≤ Subgroup.centralizer (M : Set X) := by
    rcases CFSG.LocalCores.distinct_components_commute hN hM with heq | hcm
    · exact absurd heq hNM
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcm
  have hx₂centM : x₂ ∈ Subgroup.centralizer (M : Set X) := hcentNM hx₂N
  have hx₁k_eq : x₁ ^ k = (a ^ i)⁻¹ * x₂ := by
    rw [hx₂]
    group
  have hx₁k_centM : x₁ ^ k ∈ Subgroup.centralizer (M : Set X) := by
    rw [hx₁k_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _
      (hcentAM (Subgroup.zpow_mem A haA i))) hx₂centM
  have hx₁k1 : x₁ ^ k = 1 := eq_one_of_mem_isComponent_of_centralizes hKA h hM hMY
    (Subgroup.zpow_mem M hx₁M k) hx₁k_centM
  have hx₂A : x₂ ∈ A := by
    rw [hx₂, hx₁k1, mul_one]
    exact Subgroup.zpow_mem A haA i
  have hx₂inf : x₂ ∈ A ⊓ N := ⟨hx₂A, hx₂N⟩
  rw [inf_A_eq_bot hKA h hN hNY] at hx₂inf
  exact hx₂ne (Subgroup.mem_bot.mp hx₂inf)

private lemma elemAbelian_card_27_of_chain
    {a x₀ x₁ : X}
    (haord : orderOf a = 3) (hx₀ord : orderOf x₀ = 3) (hx₁ord : orderOf x₁ = 3)
    (hax₀ : a * x₀ = x₀ * a) (hax₁ : a * x₁ = x₁ * a)
    (hx₀x₁ : x₀ * x₁ = x₁ * x₀)
    (hx₀_not : x₀ ∉ Subgroup.zpowers a)
    (hx₁_not : x₁ ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) :
    (∀ e ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀ : Subgroup X), e * x₁ = x₁ * e) ∧
      CFSG.Open.IsElemAbelian 3
        ((Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁) ∧
      Nat.card (((Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁ :
        Subgroup X)) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ha3 : a ^ 3 = 1 := by
    rw [← haord]
    exact pow_orderOf_eq_one a
  have hcomm_a_x₀ : ∀ e ∈ Subgroup.zpowers a, Commute e x₀ := by
    intro e he
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
    exact Commute.zpow_left hax₀ i
  have hE0 := CFSG.Quasithin.exists_elemAbelian_sup_zpowers (p := 3)
    (CFSG.Open.isElemAbelian_zpowers ha3) hx₀ord hcomm_a_x₀ hx₀_not
  have hE0card : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀ : Subgroup X) = 9 := by
    rw [hE0.2, Nat.card_zpowers, haord]
  have hE0_x₁ : ∀ e ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀ : Subgroup X),
      e * x₁ = x₁ * e := by
    have h := CFSG.le_centralizer_sup_of_commute_both (A := Subgroup.zpowers x₁)
      (B := Subgroup.zpowers a) (C := Subgroup.zpowers x₀)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hax₀ j) i)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hax₁.symm j) i)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hx₀x₁.symm j) i)
    intro e he
    exact Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_zpowers x₁)) e he
  have hE1 := CFSG.Quasithin.exists_elemAbelian_sup_zpowers (p := 3) hE0.1 hx₁ord
    hE0_x₁ hx₁_not
  have hE1card : Nat.card
      ((Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁ : Subgroup X) = 27 := by
    rw [hE1.2, hE0card]
  exact ⟨hE0_x₁, hE1.1, hE1card⟩

private lemma four_le_pRank_of_elemAbelian_chain
    {a x₀ x₁ x₂ : X}
    (haord : orderOf a = 3) (hx₀ord : orderOf x₀ = 3)
    (hx₁ord : orderOf x₁ = 3) (hx₂ord : orderOf x₂ = 3)
    (hax₀ : a * x₀ = x₀ * a) (hax₁ : a * x₁ = x₁ * a)
    (hx₀x₁ : x₀ * x₁ = x₁ * x₀) (hax₂ : a * x₂ = x₂ * a)
    (hx₀x₂ : x₀ * x₂ = x₂ * x₀) (hx₁x₂ : x₁ * x₂ = x₂ * x₁)
    (hx₀_not : x₀ ∉ Subgroup.zpowers a)
    (hx₁_not : x₁ ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers x₀)
    (hx₂_not : x₂ ∉ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hE0_x₁, hE1el, hE1card⟩ :=
    elemAbelian_card_27_of_chain haord hx₀ord hx₁ord hax₀ hax₁ hx₀x₁ hx₀_not hx₁_not
  have hE0_x₂ : ∀ e ∈ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀ : Subgroup X),
      e * x₂ = x₂ * e := by
    have h := CFSG.le_centralizer_sup_of_commute_both (A := Subgroup.zpowers x₂)
      (B := Subgroup.zpowers a) (C := Subgroup.zpowers x₀)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hax₀ j) i)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hax₂.symm j) i)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hx₀x₂.symm j) i)
    intro e he
    exact Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_zpowers x₂)) e he
  have hE1_x₂ : ∀ e ∈ ((Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔
      Subgroup.zpowers x₁ : Subgroup X), e * x₂ = x₂ * e := by
    have h := CFSG.le_centralizer_sup_of_commute_both (A := Subgroup.zpowers x₂)
      (B := Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) (C := Subgroup.zpowers x₁)
      (fun p hp q hq => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_right (show Commute p x₁ from hE0_x₁ p hp) k)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        exact Commute.zpow_left (show Commute x₂ q from (hE0_x₂ q hq).symm) i)
      (fun p hp q hq => by
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
        exact Commute.zpow_left (Commute.zpow_right hx₁x₂.symm k) i)
    intro e he
    exact Subgroup.mem_centralizer_iff.mp (h (Subgroup.mem_zpowers x₂)) e he
  have hE2 := CFSG.Quasithin.exists_elemAbelian_sup_zpowers (p := 3) hE1el hx₂ord
    hE1_x₂ hx₂_not
  have hE2card : Nat.card
      (((Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁) ⊔
        Subgroup.zpowers x₂ : Subgroup X) = 81 := by
    rw [hE2.2, hE1card]
  exact CFSG.SectionRank.le_pRank (p := 3) (H := ⊤)
    (E := ((Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁) ⊔
      Subgroup.zpowers x₂) (by norm_num) le_top hE2.1 (by rw [hE2card]; norm_num)

private lemma false_of_four_le_pRank (h : O1517bRed X p P A Y)
    (hrank : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X)) : False := by
  obtain ⟨R, hR⟩ := exists_sylow_eq_of_isSylowOf h.sylow
  have hRsyl : CFSG.Open.pRank 3 (R : Subgroup X) =
      CFSG.Open.pRank 3 (⊤ : Subgroup X) := (CFSG.SectionRank.pRank_sylow R).1
  rw [hR] at hRsyl
  rw [← hRsyl, h.rank] at hrank
  omega

private lemma false_of_moved
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) {g : X} (hgP : g ∈ P)
    (hgN : g ∉ Subgroup.normalizer (L : Set X)) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgY : g ∈ Y := h.le_Y hgP
  let L₁ : Subgroup X := L.map (MulAut.conj g).toMonoidHom
  let L₂ : Subgroup X := L.map (MulAut.conj (g * g)).toMonoidHom
  have hL₁ : CFSG.IsComponent L₁ :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
  have hL₂ : CFSG.IsComponent L₂ :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj (g * g)) hL
  have hL₁Y : ¬ L₁ ≤ Y := fun hle => hLY (CFSG.AGLEmbedding.le_of_map_conj_le hgY hle)
  have hL₂Y : ¬ L₂ ≤ Y := fun hle =>
    hLY (CFSG.AGLEmbedding.le_of_map_conj_le (Y.mul_mem hgY hgY) hle)
  have hg3 : ∃ n : ℕ, g ^ 3 ^ n = 1 := by
    obtain ⟨k, hk⟩ := h.sylow.isPGroup.exists_orderOf_eq_pow (⟨g, hgP⟩ : P)
    refine ⟨k, ?_⟩
    rw [← hk, ← Subgroup.orderOf_coe (⟨g, hgP⟩ : P)]
    exact pow_orderOf_eq_one g
  obtain ⟨hL₁_ne_L, hL₂_ne_L, hL₁₂_ne⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K3.conj_three_distinct hg3 hgN
  have hL_ne_L₁ : L ≠ L₁ := hL₁_ne_L.symm
  have hL_ne_L₂ : L ≠ L₂ := hL₂_ne_L.symm
  have hL₁_ne_L₂ : L₁ ≠ L₂ := hL₁₂_ne.symm
  obtain ⟨a, x₀, haA, haord, hx₀L, hx₀ord, hx₀_not⟩ :=
    exists_order_three_pair hKA h hL hLY
  let x₁ : X := MulAut.conj g x₀
  let x₂ : X := MulAut.conj (g * g) x₀
  have hx₁L₁ : x₁ ∈ L₁ := Subgroup.mem_map.mpr ⟨x₀, hx₀L, rfl⟩
  have hx₂L₂ : x₂ ∈ L₂ := Subgroup.mem_map.mpr ⟨x₀, hx₀L, rfl⟩
  have hx₁ord : orderOf x₁ = 3 := by
    rw [show x₁ = MulAut.conj g x₀ from rfl, MulEquiv.orderOf_eq, hx₀ord]
  have hx₂ord : orderOf x₂ = 3 := by
    rw [show x₂ = MulAut.conj (g * g) x₀ from rfl, MulEquiv.orderOf_eq, hx₀ord]
  have hx₁ne : x₁ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx₁ord
    omega
  have hx₂ne : x₂ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hx₂ord
    omega
  obtain ⟨hax₀, hax₁, hax₂, hx₀x₁, hx₀x₂, hx₁x₂⟩ :=
    moved_commutations h hL hL₁ hL₂ hL_ne_L₁ hL_ne_L₂ hL₁_ne_L₂ haA hx₀L hx₁L₁ hx₂L₂
  have hx₁_not : x₁ ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers x₀ :=
    not_mem_sup_zpowers_of_isComponent hKA h hL hLY hL₁ hL_ne_L₁.symm hL₁Y
      haA hx₀L hx₁L₁ hx₁ne
  have hx₂_not : x₂ ∉ (Subgroup.zpowers a ⊔ Subgroup.zpowers x₀) ⊔ Subgroup.zpowers x₁ :=
    not_mem_sup_sup_zpowers_of_isComponent hKA h hL hLY hL₁ hL_ne_L₁.symm hL₁Y
      hL₂ hL_ne_L₂.symm hL₁_ne_L₂.symm hL₂Y haA hx₀L hx₁L₁ hx₂L₂ hx₂ne
  have hrank4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) :=
    four_le_pRank_of_elemAbelian_chain haord hx₀ord hx₁ord hx₂ord hax₀ hax₁ hx₀x₁
      hax₂ hx₀x₂ hx₁x₂ hx₀_not hx₁_not hx₂_not
  exact false_of_four_le_pRank h hrank4

theorem O1517bRed.le_normalizer
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    P ≤ Subgroup.normalizer (L : Set X) := by
  intro g hgP
  by_contra hgN
  exact false_of_moved hKA h hL hLY hgP hgN


private lemma inf_component_ne_bot
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) : P ⊓ L ≠ ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPN : P ≤ Subgroup.normalizer (L : Set X) :=
    O1517bRed.le_normalizer hKA h hL hLY
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (L : Set X)) :=
    h.sylow.of_le hPN le_top
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (P ⊓ L) L :=
    hPsyl.inf_of_le_normalizer (Subgroup.le_normalizer) le_rfl
  have h3L : 3 ∣ Nat.card L :=
    CFSG.LocalAnalysis.RankThreeTheoremC.thc_dvd_card Nat.prime_three h.core hL
  obtain ⟨S, hS⟩ := hsyl.exists_sylow_eq_subgroupOf
  intro hbot
  have hSbot : (S : Subgroup L) = ⊥ := by
    rw [hS]
    simp [hbot]
  exact (Sylow.ne_bot_of_dvd_card S h3L) hSbot

private lemma exists_order_three_mem_inf_center
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    ∃ zP : ↥P, zP ∈ (P ⊓ L).subgroupOf P ∧ zP ∈ Subgroup.center ↥P ∧
      orderOf zP = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP3 : IsPGroup 3 ↥P := h.sylow.isPGroup
  have hPN : P ≤ Subgroup.normalizer (L : Set X) :=
    O1517bRed.le_normalizer hKA h hL hLY
  let N : Subgroup ↥P := (P ⊓ L).subgroupOf P
  have hNne : N ≠ ⊥ := by
    intro hbot
    apply inf_component_ne_bot hKA h hL hLY
    have := congrArg (fun H : Subgroup ↥P => H.map P.subtype) hbot
    rwa [show N = (P ⊓ L).subgroupOf P from rfl, Subgroup.map_bot,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr inf_le_left] at this
  have hPnorm : P ≤ Subgroup.normalizer ((P ⊓ L : Subgroup X) : Set X) := by
    have h1 : P ≤ Subgroup.normalizer (P : Set X) := Subgroup.le_normalizer
    have h2 : P ≤ Subgroup.normalizer (L : Set X) := hPN
    exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hNnorm : N.Normal := by
    rw [show N = (P ⊓ L).subgroupOf P from rfl]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hPnorm
  have hmeet : N ⊓ Subgroup.center ↥P ≠ ⊥ :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalPSubgroupMeetsCenter.inf_center_ne_bot
      hP3 N hNne
  have hP3c : IsPGroup 3 ↥(N ⊓ Subgroup.center ↥P) := hP3.to_subgroup _
  have hdiv3 : 3 ∣ Nat.card ↥(N ⊓ Subgroup.center ↥P) := by
    rcases hP3c.card_eq_or_dvd with h1 | hdvd
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hmeet
    · exact hdvd
  obtain ⟨zC, hzCord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(N ⊓ Subgroup.center ↥P)) 3 hdiv3
  exact ⟨zC.1, zC.2.1, zC.2.2, by
    simpa using (Subgroup.orderOf_coe zC).trans hzCord⟩

private lemma false_of_cyclic_center_shape
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y)
    (hcyc : IsCyclic ↥(Subgroup.center ↥P)) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAP : A ≤ P := h.le_P
  obtain ⟨zP, hzPN, hzPcenter, hzPord⟩ :=
    exists_order_three_mem_inf_center hKA h hL hLY
  have hzPPL : (zP : X) ∈ P ⊓ L := by
    have h := hzPN
    rwa [Subgroup.mem_subgroupOf] at h
  let zX : X := (zP : X)
  have hzXL : zX ∈ L := hzPPL.2
  have hzXord : orderOf zX = 3 := by
    simpa [zX] using (Subgroup.orderOf_coe zP).trans hzPord
  have hAle : A.subgroupOf P ≤ Subgroup.center ↥P := by
    haveI : Fact (IsPGroup 3 ↥P) := ⟨h.sylow.isPGroup⟩
    have hNcard : Nat.card (A.subgroupOf P) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, h.card_A]
    have hPN : P ≤ Subgroup.normalizer (A : Set X) := fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr h.normal_A]
      exact Subgroup.mem_top x
    have hNnorm : (A.subgroupOf P).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr hPN
    exact CFSG.normal_subgroup_card_eq_prime_le_center (G := ↥P) (A.subgroupOf P) hNcard
  have hzle : Subgroup.zpowers zP ≤ Subgroup.center ↥P :=
    Subgroup.zpowers_le.mpr hzPcenter
  have hcardA : Nat.card ↥(A.subgroupOf P) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv, h.card_A]
  have hcardz : Nat.card ↥(Subgroup.zpowers zP) = 3 := by
    rw [Nat.card_zpowers, hzPord]
  have heq : A.subgroupOf P = Subgroup.zpowers zP :=
    CFSG.GH74.Uniqueness.Bender.eq_of_card_eq_of_cyclic hcyc hAle hzle
      (by rw [hcardA, hcardz])
  have hzPA : zP ∈ A.subgroupOf P := by
    rw [heq]
    exact Subgroup.mem_zpowers zP
  have hzXA : zX ∈ A := Subgroup.mem_subgroupOf.mp hzPA
  have hzXinf : zX ∈ A ⊓ L := ⟨hzXA, hzXL⟩
  rw [inf_A_eq_bot hKA h hL hLY] at hzXinf
  have hzX1 : zX = 1 := Subgroup.mem_bot.mp hzXinf
  rw [hzX1, orderOf_one] at hzXord
  norm_num at hzXord

theorem O1517bRed.elem
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    CFSG.Open.IsElemAbelian 3 P ∧ Nat.card P = 27 := by
  rcases h.shape with hshape | hcyc
  · exact hshape
  · exfalso
    exact false_of_cyclic_center_shape hKA h hL hLY hcyc

theorem O1517bRed.inf_centralizer_eq
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    P ⊓ Subgroup.centralizer (L : Set X) = A := by
  apply le_antisymm ?_ ?_
  · intro x hx
    by_contra hxA
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hpcore : CFSG.Open.IsElemAbelian 3 P ∧ Nat.card P = 27 :=
      O1517bRed.elem hKA h hL hLY
    have hxP : x ∈ P := hx.1
    have hxCL : x ∈ Subgroup.centralizer (L : Set X) := hx.2
    have hx3 : x ^ 3 = 1 := hpcore.1.2 x hxP
    have hx1 : x ≠ 1 := by
      intro h1
      exact hxA (h1 ▸ A.one_mem)
    have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have hAx_comm : ∀ a ∈ A, a * x = x * a := fun a ha =>
      hpcore.1.comm (h.le_P ha) hxP
    have hE9 := CFSG.GroupTheory.isElemAbelian_sup_zpowers_of_commute
      (G := X) (r := 3) (X := A) (by rw [h.card_A]) hxord hxA hAx_comm
    have hD0el : CFSG.Open.IsElemAbelian 3 (A ⊔ Subgroup.zpowers x) := hE9.1
    have hD0card : Nat.card (A ⊔ Subgroup.zpowers x : Subgroup X) = 9 := by
      simpa using hE9.2
    have hD0P : A ⊔ Subgroup.zpowers x ≤ P :=
      sup_le h.le_P (Subgroup.zpowers_le.mpr hxP)
    have hD0rank : 2 ≤ CFSG.Open.pRank 3 (A ⊔ Subgroup.zpowers x) :=
      CFSG.SectionRank.le_pRank (p := 3)
        (H := A ⊔ Subgroup.zpowers x) (E := A ⊔ Subgroup.zpowers x)
        (by norm_num) le_rfl hD0el (by rw [hD0card]; norm_num)
    have hN : Subgroup.normalizer ((A ⊔ Subgroup.zpowers x : Subgroup X) : Set X) ≤ Y := by
      calc Subgroup.normalizer ((A ⊔ Subgroup.zpowers x : Subgroup X) : Set X)
          ≤ CFSG.Open.rankThreeGamma 2 3 P := by
            change _ ≤ CFSG.Open.GLBCore 3 2 P
            exact le_sSup ⟨_, hD0P, hD0rank, rfl⟩
        _ ≤ Y := h.gamma
    have hD0C : (A ⊔ Subgroup.zpowers x : Subgroup X) ≤
        Subgroup.centralizer (L : Set X) :=
      sup_le (Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hL))
        (Subgroup.zpowers_le.mpr hxCL)
    have hLN : L ≤ Subgroup.normalizer
        ((A ⊔ Subgroup.zpowers x : Subgroup X) : Set X) :=
      (Subgroup.le_centralizer_iff.mp hD0C).trans
        (Subgroup.centralizer_le_normalizer _)
    exact hLY (hLN.trans hN)
  · exact le_inf h.le_P (Subgroup.le_centralizer_iff.mp (h.le_centralizer_A hL))

theorem O1517bRed.eq_of_not_le
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) {L' : Subgroup X}
    (hL' : CFSG.IsComponent L') (hL'Y : ¬ L' ≤ Y) : L' = L := by
  by_contra hne
  have hcomm : L' ≤ Subgroup.centralizer (L : Set X) := by
    rcases CFSG.LocalCores.distinct_components_commute hL' hL with heq | hcomm
    · exact absurd heq hne
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hne_bot : P ⊓ L' ≠ ⊥ := inf_component_ne_bot hKA h hL' hL'Y
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne_bot
  have hxP : (x : X) ∈ P := x.2.1
  have hxL' : (x : X) ∈ L' := x.2.2
  have hxCL : (x : X) ∈ Subgroup.centralizer (L : Set X) := hcomm hxL'
  have hxD : (x : X) ∈ P ⊓ Subgroup.centralizer (L : Set X) := ⟨hxP, hxCL⟩
  rw [O1517bRed.inf_centralizer_eq hKA h hL hLY] at hxD
  have hxAL' : (x : X) ∈ A ⊓ L' := ⟨hxD, hxL'⟩
  rw [inf_A_eq_bot hKA h hL' hL'Y] at hxAL'
  exact hx1 (Subtype.ext (Subgroup.mem_bot.mp hxAL'))

theorem O1517bRed.Y_le_normalizer
    (hKA : CFSG.LocalAnalysis.RankFourTheoremC.GL83ComponentPCoreTrivial)
    (h : O1517bRed X p P A Y) {L : Subgroup X}
    (hL : CFSG.IsComponent L) (hLY : ¬ L ≤ Y) :
    Y ≤ Subgroup.normalizer (L : Set X) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hLy : CFSG.IsComponent (L.map (MulAut.conj y).toMonoidHom) :=
    CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hL
  have hLyY : ¬ L.map (MulAut.conj y).toMonoidHom ≤ Y :=
    fun hle => hLY (CFSG.AGLEmbedding.le_of_map_conj_le hy hle)
  exact O1517bRed.eq_of_not_le hKA h hL hLY hLy hLyY

end CFSG.LocalAnalysis.AGL81TheoremCD.Section15
