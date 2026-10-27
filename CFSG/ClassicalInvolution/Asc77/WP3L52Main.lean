module

public import CFSG.ClassicalInvolution.Asc77.WP3L52Core

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.LocalBalance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Assembly.Dichotomy (involutionOddCore)
open scoped commutatorElement

namespace Lemma52Proof

section Transport

variable {G : Type} [Group G]

theorem self_mem_centralizer_singleton (c : G) : c ∈ Subgroup.centralizer ({c} : Set G) :=
  Subgroup.mem_centralizer_singleton_iff.mpr rfl

theorem hyp51In_of_hyp51At {B : Subgroup G} {c : G} (h : Hyp51At B c) :
    Hyp51In (modOdd c B) (modOdd c (Subgroup.zpowers c)) :=
  ⟨h.1, h.2⟩

theorem hyp51At_of_hyp51In {B : Subgroup G} {c : G}
    (h : Hyp51In (modOdd c B) (modOdd c (Subgroup.zpowers c))) : Hyp51At B c :=
  ⟨h.uniq, h.alpha⟩

theorem le_centralizer_of_mem {B : Subgroup G} (hB : IsElemAbelian 2 B) {c : G} (hcB : c ∈ B) :
    B ≤ Subgroup.centralizer ({c} : Set G) := fun b hb =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hB.1.is_comm.comm (⟨b, hb⟩ : B) ⟨c, hcB⟩))

theorem mul_self_eq_one_of_mem {B : Subgroup G} (hB : IsElemAbelian 2 B) {x : G} (hx : x ∈ B) :
    x * x = 1 := by
  have := hB.2 x hx
  rwa [sq] at this

theorem modOdd_comm {B : Subgroup G} (hB : IsElemAbelian 2 B) {c : G} :
    ∀ x ∈ modOdd c B, ∀ y ∈ modOdd c B, x * y = y * x := by
  intro x hx y hy
  obtain ⟨k₁, hk₁, rfl⟩ := mem_modOdd_iff.mp hx
  obtain ⟨k₂, hk₂, rfl⟩ := mem_modOdd_iff.mp hy
  rw [← map_mul, ← map_mul]
  congr 1
  have hc : (k₁ : G) * k₂ = k₂ * k₁ :=
    congrArg Subtype.val (hB.1.is_comm.comm (⟨(k₁ : G), hk₁⟩ : B) ⟨(k₂ : G), hk₂⟩)
  exact Subtype.ext hc

theorem modOdd_sq {B : Subgroup G} (hB : IsElemAbelian 2 B) {c : G} :
    ∀ x ∈ modOdd c B, x * x = 1 := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
  rw [← map_mul]
  have : k * k = 1 := Subtype.ext (mul_self_eq_one_of_mem hB hk)
  rw [this, map_one]

@[expose] def oddQuotSelf (c : G) : OddQuot c :=
  oddQuotMk c ⟨c, self_mem_centralizer_singleton c⟩

theorem oddQuotSelf_mem {B : Subgroup G} {c : G} (hcB : c ∈ B) : oddQuotSelf c ∈ modOdd c B :=
  oddQuotMk_mem_modOdd hcB (self_mem_centralizer_singleton c)

theorem commutatorElement_mem_centralizer {c r b : G}
    (hr : r ∈ Subgroup.centralizer ({c} : Set G)) (hb : b ∈ Subgroup.centralizer ({c} : Set G)) :
    ⁅r, b⁆ ∈ Subgroup.centralizer ({c} : Set G) := by
  simp only [commutatorElement_def]
  exact (Subgroup.centralizer ({c} : Set G)).mul_mem
    ((Subgroup.centralizer ({c} : Set G)).mul_mem
      ((Subgroup.centralizer ({c} : Set G)).mul_mem hr hb)
      ((Subgroup.centralizer ({c} : Set G)).inv_mem hr))
    ((Subgroup.centralizer ({c} : Set G)).inv_mem hb)

theorem oddQuotSelf_central (c : G) (y : OddQuot c) : y * oddQuotSelf c = oddQuotSelf c * y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ y
  change oddQuotMk c g * oddQuotMk c ⟨c, self_mem_centralizer_singleton c⟩ =
    oddQuotMk c ⟨c, self_mem_centralizer_singleton c⟩ * oddQuotMk c g
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)

theorem mem_modOdd_zpowers_iff {B : Subgroup G} (hB : IsElemAbelian 2 B) {c : G} (hcB : c ∈ B)
    (hc1 : c ≠ 1) (x : OddQuot c) :
    x ∈ modOdd c (Subgroup.zpowers c) ↔ x = 1 ∨ x = oddQuotSelf c := by
  have hcc : c * c = 1 := mul_self_eq_one_of_mem hB hcB
  have hord : orderOf c = 2 := orderOf_eq_prime (by rw [sq]; exact hcc) hc1
  constructor
  · intro hx
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hk
    have h1 : c ^ n = c ^ (n % 2) := by
      have := zpow_mod_orderOf c n
      rw [hord] at this
      simpa using this.symm
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [h, zpow_zero] at h1
      have : k = 1 := Subtype.ext (by rw [← hn]; exact h1)
      rw [this, map_one]
    · right
      rw [h, zpow_one] at h1
      have : k = ⟨c, self_mem_centralizer_singleton c⟩ := Subtype.ext (by rw [← hn]; exact h1)
      rw [this]
      rfl
  · rintro (rfl | rfl)
    · exact (modOdd c (Subgroup.zpowers c)).one_mem
    · exact oddQuotMk_mem_modOdd (Subgroup.mem_zpowers c) (self_mem_centralizer_singleton c)

variable [Finite G]

theorem oddQuotSelf_ne_one {B : Subgroup G} (hB : IsElemAbelian 2 B) {c : G} (hcB : c ∈ B)
    (hc1 : c ≠ 1) : oddQuotSelf c ≠ 1 := by
  intro h
  have hcc : (⟨c, self_mem_centralizer_singleton c⟩ : ↥(Subgroup.centralizer ({c} : Set G))) *
      ⟨c, self_mem_centralizer_singleton c⟩ = 1 :=
    Subtype.ext (mul_self_eq_one_of_mem hB hcB)
  exact hc1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hcc h))

theorem oddQuotMk_not_mem_zpowers {B : Subgroup G} (hB : IsElemAbelian 2 B) {c d : G}
    (hcB : c ∈ B) (hc1 : c ≠ 1) (hdB : d ∈ B) (hd1 : d ≠ 1) (hdc : d ≠ c)
    (hdC : d ∈ Subgroup.centralizer ({c} : Set G)) :
    oddQuotMk c ⟨d, hdC⟩ ∉ modOdd c (Subgroup.zpowers c) := by
  rw [mem_modOdd_zpowers_iff hB hcB hc1]
  have hcc : c * c = 1 := mul_self_eq_one_of_mem hB hcB
  have hdd : d * d = 1 := mul_self_eq_one_of_mem hB hdB
  rintro (h | h)
  · have hsq : (⟨d, hdC⟩ : ↥(Subgroup.centralizer ({c} : Set G))) * ⟨d, hdC⟩ = 1 :=
      Subtype.ext hdd
    exact hd1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  · have hcomm : d * c = c * d :=
      congrArg Subtype.val (hB.1.is_comm.comm (⟨d, hdB⟩ : B) ⟨c, hcB⟩)
    have hsq : (⟨d, hdC⟩ * ⟨c, self_mem_centralizer_singleton c⟩ :
        ↥(Subgroup.centralizer ({c} : Set G))) *
          (⟨d, hdC⟩ * ⟨c, self_mem_centralizer_singleton c⟩) = 1 := by
      apply Subtype.ext
      change d * c * (d * c) = 1
      calc d * c * (d * c) = d * (c * d) * c := by group
        _ = d * (d * c) * c := by rw [hcomm]
        _ = (d * d) * (c * c) := by group
        _ = 1 := by rw [hdd, hcc, one_mul]
    have hsq' : (⟨c, self_mem_centralizer_singleton c⟩ :
        ↥(Subgroup.centralizer ({c} : Set G))) * ⟨c, self_mem_centralizer_singleton c⟩ = 1 :=
      Subtype.ext hcc
    have h1 : oddQuotMk c (⟨d, hdC⟩ * ⟨c, self_mem_centralizer_singleton c⟩) = 1 := by
      rw [map_mul]
      change oddQuotMk c ⟨d, hdC⟩ * oddQuotSelf c = 1
      rw [h]
      change oddQuotMk c ⟨c, self_mem_centralizer_singleton c⟩ *
        oddQuotMk c ⟨c, self_mem_centralizer_singleton c⟩ = 1
      rw [← map_mul, hsq', map_one]
    have h3 : d * c = 1 := congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h1)
    apply hdc
    rw [eq_inv_of_mul_eq_one_left h3]
    exact inv_eq_of_mul_eq_one_right hcc

theorem oddQuotMk_mem_involutionOddCore {c f y : G} (hf : f ∈ Subgroup.centralizer ({c} : Set G))
    (hy : y ∈ Subgroup.centralizer ({c} : Set G)) (hf2 : f * f = 1)
    (hyf : y ∈ involutionOddCore f) :
    oddQuotMk c ⟨y, hy⟩ ∈ involutionOddCore (oddQuotMk c ⟨f, hf⟩) := by
  have h1 : (⟨y, hy⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
      involutionOddCore (⟨f, hf⟩ : ↥(Subgroup.centralizer ({c} : Set G))) :=
    subgroupOf_involutionOddCore_le (⟨f, hf⟩ : ↥(Subgroup.centralizer ({c} : Set G)))
      (Subgroup.mem_subgroupOf.mpr hyf)
  have h2 : IsPGroup 2 (Subgroup.zpowers
      (⟨f, hf⟩ : ↥(Subgroup.centralizer ({c} : Set G)))) :=
    CFSG.ClassicalInvolution.Balance.isPGroup_zpowers_of_mul_self_eq_one (Subtype.ext hf2)
  exact map_involutionOddCore_le (oddQuotMk c) (QuotientGroup.mk'_surjective _) h2 ⟨_, h1, rfl⟩

omit [Finite G] in
theorem mem_involutionOddCore_of_oddQuotMk_eq_one {c g : G}
    (hg : g ∈ Subgroup.centralizer ({c} : Set G)) (h : oddQuotMk c ⟨g, hg⟩ = 1) :
    g ∈ involutionOddCore c :=
  ⟨_, oddQuotMk_eq_one_iff.mp h, rfl⟩

theorem card_modOdd_eq_eight {B : Subgroup G} (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8)
    {c : G} (hcB : c ∈ B) : Nat.card (modOdd c B) = 8 :=
  (card_modOdd_of_exponent_two (le_centralizer_of_mem hB hcB)
    (fun _ hf => mul_self_eq_one_of_mem hB hf)).trans hB8

theorem not_isComponent_of_comm {Q : Type} [Group Q] (hQ : ∀ x y : Q, x * y = y * x)
    {L : Subgroup Q} : ¬ IsComponent L := by
  rintro ⟨⟨-, -, a, b, hab⟩, -⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  exact congrArg _ (Subtype.ext (hQ x y))

end Transport

end Lemma52Proof

open Lemma52Proof

section Assembly

variable {G : Type} [Group G] [Finite G]

theorem weakBalanced_of_hyp51 {B : Subgroup G} (hB : Hyp51 B) : WeakBalanced B := by
  obtain ⟨hBel, hB8, hBc⟩ := hB
  intro d hdB hd1 c hcB hc1
  have hBle := le_centralizer_of_mem hBel hcB
  by_cases hdc : d = c
  · subst hdc
    rw [Subgroup.commutator_le]
    intro r hr b hb
    have e : ⁅r, b⁆ = r * (b * r⁻¹ * b⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (involutionOddCore d).mul_mem hr.1 (conj_mem_involutionOddCore
      (le_centralizer_of_mem hBel hdB hb) ((involutionOddCore d).inv_mem hr.1))
  · have H := hyp51In_of_hyp51At (hBc c hcB hc1)
    have hdC : d ∈ Subgroup.centralizer ({c} : Set G) := hBle hdB
    have hmain := commutator_involutionOddCore_eq_bot_of_hyp51In (pPrimeCore_oddQuot_eq_bot c)
      (modOdd_comm hBel) (modOdd_sq hBel) (card_modOdd_eq_eight hBel hB8 hcB)
      (oddQuotSelf_mem hcB) (oddQuotSelf_ne_one hBel hcB hc1) (oddQuotSelf_central c)
      (mem_modOdd_zpowers_iff hBel hcB hc1) H (oddQuotMk_mem_modOdd hdB hdC)
      (oddQuotMk_not_mem_zpowers hBel hcB hc1 hdB hd1 hdc hdC)
    rw [Subgroup.commutator_le]
    intro r hr b hb
    obtain ⟨hrd, hrC⟩ := Subgroup.mem_inf.mp hr
    have hbC := hBle hb
    have h1 : oddQuotMk c ⟨r, hrC⟩ ∈ involutionOddCore (oddQuotMk c ⟨d, hdC⟩) :=
      oddQuotMk_mem_involutionOddCore hdC hrC (mul_self_eq_one_of_mem hBel hdB) hrd
    have h3 := Subgroup.commutator_mem_commutator h1 (oddQuotMk_mem_modOdd hb hbC)
    rw [hmain, Subgroup.mem_bot] at h3
    have hcom := commutatorElement_mem_centralizer hrC hbC
    refine mem_involutionOddCore_of_oddQuotMk_eq_one hcom ?_
    have e : (⟨⁅r, b⁆, hcom⟩ : ↥(Subgroup.centralizer ({c} : Set G))) =
        ⁅(⟨r, hrC⟩ : ↥(Subgroup.centralizer ({c} : Set G))), ⟨b, hbC⟩⁆ := rfl
    rw [e, map_commutatorElement]
    exact h3

theorem twoBalancedWrt_of_hyp51 {B : Subgroup G} (hB : Hyp51 B) : TwoBalancedWrt B := by
  obtain ⟨hBel, hB8, hBc⟩ := hB
  intro F hF a ha ha1
  obtain ⟨hFB, hF4⟩ := hF
  have hBle := le_centralizer_of_mem hBel ha
  have hF4' : Nat.card F = 4 := by simpa using hF4
  have hFsq : ∀ f ∈ F, f * f = 1 := fun f hf => mul_self_eq_one_of_mem hBel (hFB hf)
  have hFt : Nat.card (modOdd a F) = 4 :=
    (card_modOdd_of_exponent_two (hFB.trans hBle) hFsq).trans hF4'
  have hFtB : modOdd a F ≤ modOdd a B := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hFB hk, rfl⟩
  have hdelta := deltaCore_eq_bot_of_hyp51In (pPrimeCore_oddQuot_eq_bot a) (modOdd_comm hBel)
    (modOdd_sq hBel) (card_modOdd_eq_eight hBel hB8 ha) (oddQuotSelf_mem ha)
    (oddQuotSelf_ne_one hBel ha ha1) (oddQuotSelf_central a)
    (mem_modOdd_zpowers_iff hBel ha ha1) (hyp51In_of_hyp51At (hBc a ha ha1)) hFtB hFt
  intro y hy
  obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.mp hy
  refine mem_involutionOddCore_of_oddQuotMk_eq_one hyC ?_
  have hmem : oddQuotMk a ⟨y, hyC⟩ ∈ deltaCore (modOdd a F) := by
    rw [mem_deltaCore_iff]
    intro ft hft hft1
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hft
    have hk1 : (k : G) ≠ 1 := fun h => hft1 (by
      have : k = 1 := Subtype.ext h
      rw [this, map_one])
    exact oddQuotMk_mem_involutionOddCore k.2 hyC (hFsq _ hk)
      (mem_deltaCore_iff.mp hyD _ hk hk1)
  rw [hdelta, Subgroup.mem_bot] at hmem
  exact hmem

theorem lemma52 : Lemma52 := fun _ _ _ _ hB =>
  ⟨hB.1, hB.2.1, weakBalanced_of_hyp51 hB, twoBalancedWrt_of_hyp51 hB⟩

omit [Finite G] in
theorem hyp51_of_forall_commute (hG : ∀ x y : G, x * y = y * x) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hB8 : Nat.card B = 8) : Hyp51 B := by
  refine ⟨hB, hB8, fun c _ _ => ?_⟩
  have hQ : ∀ x y : OddQuot c, x * y = y * x := by
    intro x y
    obtain ⟨k₁, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k₂, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (Subtype.ext (hG k₁ k₂))
  exact ⟨fun L₁ _ h₁ => (not_isComponent_of_comm hQ h₁).elim,
    fun L hL => (not_isComponent_of_comm hQ hL).elim⟩

end Assembly

end CFSG.ClassicalInvolution.Asc77
