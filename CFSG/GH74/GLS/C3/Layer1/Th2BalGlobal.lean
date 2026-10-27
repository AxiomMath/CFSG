module

public import CFSG.GH74.GLS.C3.Layer1.Th2BalLocal
public import CFSG.GH74.GLS.Prop27.Balance
public import CFSG.GH74.GLS.C3.Layer1.BackConj
public import CFSG.GH74.GLS.C3.Layer1.St1Bal
public import CFSG.GH74.GLS.C3.Layer1.Th2Defs

public section

namespace CFSG.GH74.GLS.Th2.Bal

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.Assembly.Dichotomy
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.LocalBalance
open scoped commutatorElement

section Setup

variable {G : Type} [Group G] [Finite G]

noncomputable abbrev piBar (a : G) : ↥(centralizer ({a} : Set G)) →* CentralizerBar a :=
  barMk ↥(centralizer ({a} : Set G))

theorem eq_one_of_sq_of_mem_pPrimeCore {X : Type*} [Group X] [Finite X] {h : X} (h2 : h * h = 1)
    (hO : h ∈ pPrimeCore 2 X) : h = 1 := by
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 X)) := pPrimeCore_coprime_card
  have hdvd : orderOf (⟨h, hO⟩ : pPrimeCore 2 X) ∣ Nat.card (pPrimeCore 2 X) :=
    orderOf_dvd_natCard _
  have h2' : orderOf (⟨h, hO⟩ : pPrimeCore 2 X) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    apply Subtype.ext
    simpa [sq] using h2
  have h1 : orderOf (⟨h, hO⟩ : pPrimeCore 2 X) = 1 := by
    have : Nat.Coprime (orderOf (⟨h, hO⟩ : pPrimeCore 2 X)) (Nat.card (pPrimeCore 2 X)) := by
      refine Nat.Coprime.coprime_dvd_left h2' hcop
    exact Nat.Coprime.eq_one_of_dvd this hdvd
  have := orderOf_eq_one_iff.mp h1
  exact congrArg Subtype.val this

omit [Finite G] in
theorem piBar_eq_one_iff {a : G} {h : ↥(centralizer ({a} : Set G))} :
    piBar a h = 1 ↔ h ∈ pPrimeCore 2 ↥(centralizer ({a} : Set G)) :=
  QuotientGroup.eq_one_iff h

theorem piBar_injOn {a : G} {D : Subgroup G} (hD2 : ∀ d ∈ D, d * d = 1) :
    Set.InjOn (piBar a) ((D.subgroupOf (centralizer ({a} : Set G)) : Subgroup _) : Set _) := by
  intro x hx y hy hxy
  have hxD : (x : G) ∈ D := Subgroup.mem_subgroupOf.mp hx
  have hyD : (y : G) ∈ D := Subgroup.mem_subgroupOf.mp hy
  have h1 : x⁻¹ * y ∈ pPrimeCore 2 ↥(centralizer ({a} : Set G)) := by
    rw [← piBar_eq_one_iff, map_mul, map_inv, hxy, inv_mul_cancel]
  have hsq : (x⁻¹ * y) * (x⁻¹ * y) = 1 := by
    apply Subtype.ext
    have hmem : ((x⁻¹ * y : ↥(centralizer ({a} : Set G))) : G) ∈ D := by
      have : ((x⁻¹ * y : ↥(centralizer ({a} : Set G))) : G) = (x : G)⁻¹ * y := rfl
      rw [this]
      exact D.mul_mem (D.inv_mem hxD) hyD
    exact hD2 _ hmem
  have := eq_one_of_sq_of_mem_pPrimeCore hsq h1
  exact inv_mul_eq_one.mp this

theorem card_map_piBar {a : G} {D : Subgroup G} (hD2 : ∀ d ∈ D, d * d = 1)
    (hDH : D ≤ centralizer ({a} : Set G)) :
    Nat.card ((D.subgroupOf (centralizer ({a} : Set G))).map (piBar a)) = Nat.card D := by
  set K : Subgroup ↥(centralizer ({a} : Set G)) := D.subgroupOf (centralizer ({a} : Set G)) with hK
  have hinj : Function.Injective ((piBar a).comp K.subtype) := by
    intro x y hxy
    apply Subtype.ext
    exact piBar_injOn hD2 x.2 y.2 hxy
  have hr : ((piBar a).comp K.subtype).range = K.map (piBar a) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv

theorem map_le_deltaCore_of_le {H : Subgroup G} {D Y : Subgroup G}
    (hD2 : ∀ d ∈ D, d * d = 1)
    (hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G))) :
    (Y.subgroupOf H).map (barMk H) ≤
      deltaCore ((D.subgroupOf H).map (barMk H)) := by
  classical
  refine le_deltaCore fun f hf hf1 => ?_
  obtain ⟨d₀, hd₀, rfl⟩ := hf
  have hdD : (d₀ : G) ∈ D := Subgroup.mem_subgroupOf.mp hd₀
  have hd₁ : (d₀ : G) ≠ 1 := fun h => hf1 (by
    have h' : d₀ = 1 := Subtype.ext h
    rw [h', map_one])
  have hsq : d₀ * d₀ = 1 := Subtype.ext (hD2 _ hdD)
  set W : Subgroup ↥H :=
    (pPrimeCoreOf 2 (centralizer ({(d₀ : G)} : Set G)) ⊓ H).subgroupOf H with hW
  have hWC : W ≤ centralizer ({d₀} : Set ↥H) := by
    intro w hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    have hw1 : (w : G) ∈ pPrimeCoreOf 2 (centralizer ({(d₀ : G)} : Set G)) :=
      (Subgroup.mem_subgroupOf.mp hw).1
    exact mem_centralizer_singleton_iff.mp (pPrimeCoreOf_le_self _ hw1)
  have hWn : ∀ c ∈ centralizer ({d₀} : Set ↥H), ∀ w ∈ W, c * w * c⁻¹ ∈ W := by
    intro c hc w hw
    have hcd : (c : G) ∈ centralizer ({(d₀ : G)} : Set G) := by
      have := Subgroup.mem_centralizer_singleton_iff.mp hc
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val this
    have hw1 : (w : G) ∈ pPrimeCoreOf 2 (centralizer ({(d₀ : G)} : Set G)) :=
      (Subgroup.mem_subgroupOf.mp hw).1
    rw [hW, Subgroup.mem_subgroupOf]
    exact ⟨CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore hcd hw1,
      H.mul_mem (H.mul_mem c.2 w.2) (H.inv_mem c.2)⟩
  have hWodd : Odd (Nat.card W) := by
    have h1 : Nat.card W = Nat.card ↥(pPrimeCoreOf 2 (centralizer ({(d₀ : G)} : Set G)) ⊓ H) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
    rw [h1]
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (coprime_card_pPrimeCoreOf _))
      (Subgroup.card_dvd_of_le inf_le_left)
  have hW1 : W ≤ involutionOddCore d₀ :=
    CFSG.GH74.GLS.Prop27.le_involutionOddCore_of_normalized hWC hWn hWodd
  have hYW : Y.subgroupOf H ≤ W := by
    intro y hy
    rw [hW, Subgroup.mem_subgroupOf]
    exact ⟨hY _ hdD hd₁ (Subgroup.mem_subgroupOf.mp hy), y.2⟩
  exact (Subgroup.map_mono (hYW.trans hW1)).trans
    (map_involutionOddCore_le (barMk H) (QuotientGroup.mk'_surjective _)
      (isPGroup_zpowers_of_mul_self_eq_one hsq))

theorem map_le_deltaCore {a : G} {D Y : Subgroup G} (hD2 : ∀ d ∈ D, d * d = 1)
    (hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G))) :
    (Y.subgroupOf (centralizer ({a} : Set G))).map (piBar a) ≤
      deltaCore ((D.subgroupOf (centralizer ({a} : Set G))).map (piBar a)) :=
  map_le_deltaCore_of_le (H := centralizer ({a} : Set G)) hD2 hY

theorem exists_component_of_image {a : G} {k : ℕ} (hk : 1 ≤ k) {D Y : Subgroup G}
    (hDH : D ≤ centralizer ({a} : Set G)) (hDk : 2 ^ k ≤ Nat.card D) (hD2 : ∀ d ∈ D, d * d = 1)
    (hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)))
    {N : Subgroup (CentralizerBar a)}
    (hNY : N ≤ (Y.subgroupOf (centralizer ({a} : Set G))).map (piBar a)) (hN1 : N ≠ ⊥) :
    ∃ L : Subgroup (CentralizerBar a), IsComponent L ∧
      (∀ f ∈ (D.subgroupOf (centralizer ({a} : Set G))).map (piBar a), conjSub f L = L) ∧
      (∀ f ∈ (D.subgroupOf (centralizer ({a} : Set G))).map (piBar a), f ≠ 1 →
        ¬ ∀ x ∈ L, f * x = x * f) ∧
      (∀ n ∈ N, conjSub n L = L) ∧ (¬ ∀ n ∈ N, ∀ x ∈ L, n * x = x * n) ∧
      ¬ IsLocallyKBalanced k (↥L ⧸ Subgroup.center ↥L) := by
  classical
  set F : Subgroup (CentralizerBar a) := (D.subgroupOf (centralizer ({a} : Set G))).map (piBar a)
    with hF
  have hFk : 2 ^ k ≤ Nat.card F := by
    rw [hF, card_map_piBar hD2 hDH]
    exact hDk
  have hF2 : ∀ f ∈ F, f * f = 1 := by
    rintro _ ⟨d₀, hd₀, rfl⟩
    have hdD : (d₀ : G) ∈ D := Subgroup.mem_subgroupOf.mp hd₀
    have : d₀ * d₀ = 1 := Subtype.ext (hD2 _ hdD)
    rw [← map_mul, this, map_one]
  obtain ⟨f₀, hf₀F, hf₀1⟩ := exists_ne_one_of_two_pow_le hk hFk
  exact exists_component_not_locallyKBalanced (CFSG.GH74.GLS.pPrimeCore_quotient_eq_bot _)
    hFk hF2 hf₀F hf₀1 (hNY.trans (map_le_deltaCore hD2 hY)) hN1

omit [Finite G] in
theorem conj_mem_AG {D : Subgroup G} {b y : G} (hb : ∀ d ∈ D, b * d = d * b) (hy : y ∈ AG D) :
    b * y * b⁻¹ ∈ AG D := by
  unfold AG at hy ⊢
  simp only [Subgroup.mem_iInf] at hy ⊢
  intro d hd
  exact CFSG.ComponentClassification.UnbalancedLayer.conj_mem_map_pPrimeCore
    (mem_centralizer_singleton_iff.mpr (hb d hd.1)) (hy d hd)

theorem isKBal_of_local_on_components {k : ℕ} (hk : 1 ≤ k) {A : Subgroup G}
    (hA : CFSG.IsElementaryAbelian 2 ↥A)
    (hloc : ∀ (D : Subgroup G), IsE k A D → ∀ a ∈ A, orderOf a = 2 →
      ∀ L : Subgroup (CentralizerBar a), IsComponent L →
      (∀ f ∈ (D.subgroupOf (centralizer ({a} : Set G))).map (piBar a), conjSub f L = L) →
      (∀ f ∈ (D.subgroupOf (centralizer ({a} : Set G))).map (piBar a), f ≠ 1 →
        ¬ ∀ x ∈ L, f * x = x * f) →
      IsLocallyKBalanced k (↥L ⧸ Subgroup.center ↥L)) :
    IsKBal k A := by
  classical
  intro D hD a ha ha1
  obtain ⟨hDA, hDel, hDrk⟩ := hD
  obtain ⟨hAc, hAsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hA
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hAsq a ha) ha1
  set H := centralizer ({a} : Set G) with hH
  have hDH : D ≤ H := fun d hd => mem_centralizer_singleton_iff.mpr (hAc d (hDA hd) a ha)
  have hDk : 2 ^ k ≤ Nat.card D := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel]
    exact Nat.pow_le_pow_right (by norm_num) hDrk
  by_contra hnle
  obtain ⟨c, hc, hcn⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  set Y : Subgroup G := AG D ⊓ H with hYdef
  have hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
    fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
  have hN1 : (Y.subgroupOf H).map (piBar a) ≠ ⊥ := by
    intro h
    apply hcn
    have hmem : piBar a ⟨c, hc.2⟩ ∈ (Y.subgroupOf H).map (piBar a) :=
      ⟨⟨c, hc.2⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
    rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
    exact ⟨⟨c, hc.2⟩, hmem, rfl⟩
  obtain ⟨L, hL, hFL, hFfaith, -, -, hnb⟩ :=
    exists_component_of_image hk hDH hDk hDsq hY (le_refl _) hN1
  exact hnb (hloc D ⟨hDA, hDel, hDrk⟩ a ha ha2 L hL hFL hFfaith)

theorem isKBal_of_local {k : ℕ} (hk : 1 ≤ k)
    (hloc : ∀ a : G, orderOf a = 2 → ∀ L : Subgroup (CentralizerBar a), IsComponent L →
      IsLocallyKBalanced k (↥L ⧸ Subgroup.center ↥L))
    {A : Subgroup G} (hA : CFSG.IsElementaryAbelian 2 ↥A) : IsKBal k A := by
  refine isKBal_of_local_on_components hk hA ?_
  intro D hD a ha ha2 L hL _ _
  exact hloc a ha2 L hL

theorem pPrimeCoreOf_le_of_pCompIn {C J : Subgroup G} (hJ : IsPCompIn 2 C J) :
    pPrimeCoreOf 2 J ≤ pPrimeCoreOf 2 C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJC, K', -, hsub, -⟩ := hJ
  have h1 := CFSG.GH74.GLS.pPrimeCoreOf_le_of_subnormal (X := ↥C) 2 hsub
  rw [TwoThin.pPrimeCoreOf_eq_map_subgroupOf hJC]
  exact Subgroup.map_mono h1

theorem exists_unbalancing_of_not_weak {B : Subgroup G} (hB : CFSG.IsElementaryAbelian 2 ↥B)
    (hnot : ¬ IsWeakKBal 2 B) :
    ∃ (a d : G) (J : Subgroup G), a ∈ B ∧ d ∈ B ∧ a ≠ 1 ∧ d ≠ 1 ∧ IsUnbalancingTriple a d J ∧
      ∃ L : Subgroup (CentralizerBar a), IsComponent L ∧
        L = (J.subgroupOf (centralizer ({a} : Set G))).map (piBar a) ∧
        ¬ IsLocallyKBalanced 2 (↥L ⧸ Subgroup.center ↥L) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hBc, hBsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hB
  unfold IsWeakKBal at hnot
  push Not at hnot
  obtain ⟨D, hD, a, haB, ha1, c, hc, b, hbB, hcb⟩ := hnot
  obtain ⟨hDB, hDel, hDrk⟩ := hD
  obtain ⟨-, hDsq⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hDel
  have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq a haB) ha1
  set H := centralizer ({a} : Set G) with hH
  have hBH : B ≤ H := fun x hx => mem_centralizer_singleton_iff.mpr (hBc x hx a haB)
  have hDH : D ≤ H := fun d hd => hBH (hDB hd)
  have hDk : 2 ^ 2 ≤ Nat.card D := by
    rw [C3.Layer1.Back.card_eq_two_pow_pRank hDel]
    exact Nat.pow_le_pow_right (by norm_num) hDrk
  set Y : Subgroup G := AG D ⊓ H with hYdef
  have hY : ∀ d ∈ D, d ≠ 1 → Y ≤ pPrimeCoreOf 2 (centralizer ({d} : Set G)) :=
    fun d hd hd1 => inf_le_left.trans (iInf₂_le d ⟨hd, hd1⟩)
  set W : Subgroup (CentralizerBar a) := (Y.subgroupOf H).map (piBar a) with hW
  set E : Subgroup (CentralizerBar a) := (B.subgroupOf H).map (piBar a) with hE
  set N : Subgroup (CentralizerBar a) := ⁅W, E⁆ with hN
  have hNW : N ≤ W := by
    rw [hN, Subgroup.commutator_le]
    rintro _ ⟨y₀, hy₀, rfl⟩ _ ⟨b₀, hb₀, rfl⟩
    have hyY : (y₀ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy₀
    have hbB' : (b₀ : G) ∈ B := Subgroup.mem_subgroupOf.mp hb₀
    refine ⟨⁅y₀, b₀⁆, Subgroup.mem_subgroupOf.mpr ?_, map_commutatorElement _ _ _⟩
    have hcomm : ((⁅y₀, b₀⁆ : ↥H) : G) =
        (y₀ : G) * ((b₀ : G) * (y₀ : G)⁻¹ * (b₀ : G)⁻¹) := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hcomm]
    refine Y.mul_mem hyY ⟨?_, ?_⟩
    · exact conj_mem_AG (fun d hd => hBc _ hbB' d (hDB hd)) ((AG D).inv_mem hyY.1)
    · exact H.mul_mem (H.mul_mem b₀.2 (H.inv_mem y₀.2)) (H.inv_mem b₀.2)
  have hN1 : N ≠ ⊥ := by
    intro h
    apply hcb
    have hcH : c ∈ H := hc.2
    have hbH : b ∈ H := hBH hbB
    have hmem : piBar a ⁅(⟨c, hcH⟩ : ↥H), ⟨b, hbH⟩⁆ ∈ N := by
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ⟨⟨c, hcH⟩, Subgroup.mem_subgroupOf.mpr hc, rfl⟩
        ⟨⟨b, hbH⟩, Subgroup.mem_subgroupOf.mpr hbB, rfl⟩
    rw [h, Subgroup.mem_bot, piBar_eq_one_iff] at hmem
    exact ⟨_, hmem, rfl⟩
  obtain ⟨L, hL, hFL, hFfaith, hNL, hNnc, hnb⟩ :=
    exists_component_of_image (k := 2) (by norm_num) hDH hDk hDsq hY hNW hN1
  obtain ⟨J₀, hJ₀, hJ₀map⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_isPComponent_of_isComponent 2 hL
  set J : Subgroup G := J₀.map H.subtype with hJdef
  have hJH : J ≤ H := Subgroup.map_subtype_le J₀
  have hJsub : J.subgroupOf H = J₀ :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective H) J₀
  have hJc : IsPCompIn 2 H J := ⟨hJH, by rw [hJsub]; exact hJ₀⟩
  obtain ⟨d, hdD, hd1⟩ := exists_ne_one_of_two_pow_le (F := D) (k := 2) (by norm_num) hDk
  have hdB : d ∈ B := hDB hdD
  have hdH : d ∈ H := hDH hdD
  have hd2 : orderOf d = 2 := orderOf_eq_prime (by rw [sq]; exact hBsq d hdB) hd1
  have hdN : d ∈ normalizer (J : Set G) := by
    set d₀ : ↥H := ⟨d, hdH⟩ with hd₀
    have hF : piBar a d₀ ∈ (D.subgroupOf H).map (piBar a) :=
      ⟨d₀, Subgroup.mem_subgroupOf.mpr hdD, rfl⟩
    have hLd := hFL _ hF
    have hnorm : piBar a d₀ ∈
        normalizer ((J₀.map (QuotientGroup.mk' (pPrimeCore 2 ↥H)) : Subgroup _) : Set _) := by
      rw [hJ₀map]
      exact mem_normalizer_of_conjSub_eq hLd
    have hn' := CFSG.ComponentClassification.UnbalancedLayer.mem_normalizer_of_map hJ₀ hnorm
    have h2 : d₀ ∈ normalizer ((J.subgroupOf H : Subgroup ↥H) : Set ↥H) ↔
        d ∈ normalizer (J : Set G) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hJH]
      rfl
    exact h2.mp (hJsub ▸ hn')
  have hnotle : ¬ (pPrimeCoreOf 2 (centralizer ({d} : Set G)) ⊓ centralizer ({a} : Set G) ≤
      centralizerSection J (pPrimeCoreOf 2 J)) := by
    intro hle
    apply hNnc
    intro n hn x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hNW hn
    rw [← hJ₀map] at hx
    obtain ⟨j₀, hj₀, rfl⟩ := hx
    have hyY : (y₀ : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy₀
    have hyd : (y₀ : G) ∈ pPrimeCoreOf 2 (centralizer ({d} : Set G)) := hY d hdD hd1 hyY
    have hsec : (y₀ : G) ∈ centralizerSection J (pPrimeCoreOf 2 J) := hle ⟨hyd, y₀.2⟩
    have hjJ : (j₀ : G) ∈ J := ⟨j₀, hj₀, rfl⟩
    have hcomm : ⁅(j₀ : G), (y₀ : G)⁆ ∈ pPrimeCoreOf 2 J := hsec.2.2 _ hjJ
    have hO : ⁅(j₀ : G), (y₀ : G)⁆ ∈ pPrimeCoreOf 2 H := pPrimeCoreOf_le_of_pCompIn hJc hcomm
    obtain ⟨o, ho, hoe⟩ := hO
    have hoeq : o = ⁅j₀, y₀⁆ := Subtype.ext hoe
    have h1 : piBar a ⁅j₀, y₀⁆ = 1 := by
      rw [piBar_eq_one_iff, ← hoeq]
      exact ho
    rw [map_commutatorElement] at h1
    exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
  exact ⟨a, d, J, haB, hdB, ha1, hd1, ⟨⟨ha2, hJc⟩, hd2, hdH, hdN, hnotle⟩, L, hL,
    by rw [hJsub]; exact hJ₀map.symm, hnb⟩

end Setup

end CFSG.GH74.GLS.Th2.Bal
