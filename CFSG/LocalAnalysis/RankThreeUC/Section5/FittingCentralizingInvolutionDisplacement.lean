module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.BinaryActionRankAlternatives
public import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.RankThreeUC.Section5.ComponentInNormalKernel
import CFSG.LocalAnalysis.RankThreeUC.Section5.OddOrderNormalizerOfFewConjugates
import CFSG.LocalAnalysis.RankThreeUC.Section5.PCoreEqBotOfFaithfulIrreducible
import CFSG.LocalAnalysis.RankThreeUC.Section5.DeltaTransitivity
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CommRankDef

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_component_not_centralized (hO2 : CFSG.pCore 2 G = ⊥) {t : G}
    (ht : orderOf t = 2) (htF : ∀ x ∈ CFSG.fittingSubgroup G, t * x = x * t) :
    ∃ L : Subgroup G, IsComponent L ∧ ∃ l ∈ L, t * l ≠ l * t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hno
  push_neg at hno
  have hle : CFSG.generalizedFitting G ≤ Subgroup.centralizer ({t} : Set G) := by
    rw [CFSG.generalizedFitting.eq_sup, CFSG.layer.eq_sSup]
    refine sup_le (fun x hx => ?_) (sSup_le fun K hK x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact htF x hx
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hno K hK x hx
  have htc : t ∈ Subgroup.centralizer (CFSG.generalizedFitting G : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) t (Set.mem_singleton t)).symm
  have hbender :
      Subgroup.centralizer (CFSG.generalizedFitting G : Set G) ≤ CFSG.fittingSubgroup G := by
    rw [CFSG.generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting G
  have htF' : t ∈ CFSG.fittingSubgroup G := hbender htc
  have hP : IsPGroup 2 (Subgroup.zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, ht]
    simp
  have hle2 :=
    CFSG.ABGLocalTools.le_pCore_of_isPGroup_of_le_fitting hP (Subgroup.zpowers_le.2 htF')
  rw [hO2] at hle2
  have ht1 : t = 1 := Subgroup.mem_bot.1 (hle2 (Subgroup.mem_zpowers t))
  rw [ht1, orderOf_one] at ht
  exact absurd ht (by norm_num)

private theorem apply_mem_fixedSubmodule_of_commute {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (E : Subgroup G) {x : G} (hx : ∀ d ∈ E, x * d = d * x)
    {u : V} (hu : u ∈ fixedSubmodule ρ E) : ρ x u ∈ fixedSubmodule ρ E := by
  rw [QuadraticSetConjugationTransport.mem_fixedSubmodule_iff] at hu ⊢
  intro d hd
  have h1 : ρ d (ρ x u) = ρ x (ρ d u) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← hx d hd]
  rw [h1, hu d hd]

theorem lt_commRank_of_centralizes_fittingSubgroup {p : ℕ} {P T B : Subgroup G} {e : ℕ}
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
    (hc : BinaryActionRankCounterexample G p P T B e ρ) (hΔ : e + 1 < Nat.card ↥(Delta p P ρ))
    {t : G} (ht : orderOf t = 2) (htF : ∀ x ∈ CFSG.fittingSubgroup G, t * x = x * t) :
    e + 1 < commRank ρ t := by
  classical
  have hS : Setting G p P T B := hc.oddPrimeClassTwoAction.setting
  have hF := hc.faithfulBinaryIrreducibleAction
  haveI : FiniteDimensional (ZMod 2) V :=
    CFSG.LinearAlgebra.CoprimeActions.IrreducibleFiniteGroupFiniteDimensional.finiteDimensional_of_irreducible
      ρ hF.irreducible
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hmul : ∀ (a b : G) (w : V), ρ (a * b) w = ρ a (ρ b w) := fun a b w => by rw [map_mul]; rfl
  have hone : ∀ w : V, ρ 1 w = w := fun w => by rw [map_one]; rfl
  have hinv' : ∀ (a : G) (w : V), ρ a⁻¹ (ρ a w) = w := fun a w => by
    rw [← hmul, inv_mul_cancel, hone]
  have hO2 : CFSG.pCore 2 G = ⊥ :=
    pCore_eq_bot_of_faithful_irreducible 2 ρ hF.faithful hF.irreducible
  obtain ⟨L, hL, l₀, hl₀, hnc⟩ := exists_component_not_centralized hO2 ht htF
  have hPF : P ≤ CFSG.fittingSubgroup G := le_sSup ⟨hF.normal, hS.pGroup.isNilpotent⟩
  have hLlayer : L ≤ CFSG.layer G := by
    rw [CFSG.layer.eq_sSup]
    exact le_sSup hL
  have hLP : ∀ l ∈ L, ∀ d ∈ P, l * d = d * l := by
    intro l hl d hd
    have h1 : ⁅d, l⁆ ∈ (⁅CFSG.fittingSubgroup G, CFSG.layer G⁆ : Subgroup G) :=
      Subgroup.commutator_mem_commutator (hPF hd) (hLlayer hl)
    rw [CFSG.LocalCores.fitting_layer_commute, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have htP : ∀ d ∈ P, t * d = d * t := fun d hd => htF d (hPF hd)
  have hBodd : ∀ b ∈ B, Odd (orderOf b) := fun b hb => by
    have h1 : orderOf b ∣ Nat.card B := by
      have := orderOf_dvd_natCard (⟨b, hb⟩ : B)
      rwa [← Subgroup.orderOf_coe (⟨b, hb⟩ : B)] at this
    exact Odd.of_dvd_nat hS.oddOrder h1
  have hodd : ∀ y : G, Odd (orderOf y) → y ∈ Subgroup.normalizer (L : Set G) := fun y hy =>
    mem_normalizer_of_odd_orderOf_of_ncard_conjugates_le_two
      (hc.cyclicCentralizersAndFewComponentConjugates.few_conjugates L
        ((CFSG.isComponent_iff_open L).1 hL)) hy
  have hSL : twoCoreCommutator T B ≤ Subgroup.normalizer (L : Set G) := by
    unfold twoCoreCommutator
    rw [Subgroup.commutator_le]
    intro r _ b hb
    have hob : Odd (orderOf (r * b * r⁻¹)) := by
      have := (MulAut.conj r).orderOf_eq b
      simp only [MulAut.conj_apply] at this
      rw [this]
      exact hBodd b hb
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (hodd _ hob) (Subgroup.inv_mem _ (hodd b (hBodd b hb)))
  have hdec := isInternal_hyperplane_fixedSubmodule_of_binary_rank_counterexample hc
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at hdec
  obtain ⟨hind, hsup⟩ := hdec
  have hl₀ρ : ∃ D₀ : ↥(Delta p P ρ), ∃ w ∈ fixedSubmodule ρ (D₀ : Subgroup G), ρ l₀ w ≠ w := by
    by_contra hno
    push_neg at hno
    have hker : (⨆ D : ↥(Delta p P ρ), fixedSubmodule ρ (D : Subgroup G)) ≤
        LinearMap.ker (ρ l₀ - 1) := iSup_le fun D w hw => by
      simpa [sub_eq_zero] using hno D w hw
    rw [hsup, top_le_iff, LinearMap.ker_eq_top, sub_eq_zero] at hker
    have h1 : l₀ = 1 := hF.faithful (hker.trans (map_one ρ).symm)
    apply hnc
    rw [h1]
    simp
  have hLact : ∀ E : ↥(Delta p P ρ),
      ∃ l ∈ L, ∃ w ∈ fixedSubmodule ρ (E : Subgroup G), ρ l w ≠ w := by
    intro E
    obtain ⟨D₀, w₀, hw₀, hne⟩ := hl₀ρ
    obtain ⟨s, hs, hsE⟩ := DeltaTransitivity.transitive hc D₀.1 D₀.2 E.1 E.2
    refine ⟨s * l₀ * s⁻¹, (Subgroup.mem_normalizer_iff.1 (hSL hs) l₀).1 hl₀, ρ s w₀, ?_, ?_⟩
    · rw [hsE, QuadraticSetConjugationTransport.fixedSubmodule_map_conj]
      exact Submodule.mem_map_of_mem hw₀
    · intro h
      apply hne
      have e1 : ρ (s * l₀ * s⁻¹) (ρ s w₀) = ρ s (ρ l₀ w₀) := by
        rw [hmul, hmul, hinv']
      rw [e1] at h
      have h2 := congrArg (ρ s⁻¹) h
      rwa [hinv', hinv'] at h2
  have htact : ∀ E : ↥(Delta p P ρ),
      ∃ u ∈ fixedSubmodule ρ (E : Subgroup G), ρ t u ≠ u := by
    intro E
    by_contra hno
    push_neg at hno
    obtain ⟨l, hl, w, hw, hne⟩ := hLact E
    have hEP : (E : Subgroup G) ≤ P := ((mem_Delta_iff p P ρ E).1 E.2).1
    have hpres : ∀ x : G, (∀ d ∈ P, x * d = d * x) → ∀ u ∈ fixedSubmodule ρ (E : Subgroup G),
        ρ x u ∈ fixedSubmodule ρ (E : Subgroup G) ∧
          ρ x⁻¹ u ∈ fixedSubmodule ρ (E : Subgroup G) := by
      intro x hx u hu
      refine ⟨apply_mem_fixedSubmodule_of_commute ρ E (fun d hd => hx d (hEP hd)) hu,
        apply_mem_fixedSubmodule_of_commute ρ E (fun d hd => ?_) hu⟩
      exact (Commute.inv_left (show Commute x d from hx d (hEP hd))).eq
    have key := component_acts_trivially_of_not_commute ρ
      (W := fixedSubmodule ρ (E : Subgroup G)) hL (t := t)
      (fun x hx => hpres x (by
        rcases hx with hx | rfl
        · exact hLP x hx
        · exact htP)) hno ⟨l₀, hl₀, hnc⟩
    exact hne (key l hl w hw)
  choose u hu hu' using htact
  have hy_mem : ∀ E : ↥(Delta p P ρ), (ρ t - 1) (u E) ∈ fixedSubmodule ρ (E : Subgroup G) := by
    intro E
    have h1 := apply_mem_fixedSubmodule_of_commute ρ (E : Subgroup G) (x := t)
      (fun d hd => htP d (((mem_Delta_iff p P ρ E).1 E.2).1 hd)) (hu E)
    simpa using Submodule.sub_mem _ h1 (hu E)
  have hy_ne : ∀ E : ↥(Delta p P ρ), (ρ t - 1) (u E) ≠ 0 := fun E h =>
    hu' E (by simpa [sub_eq_zero] using h)
  have hli : LinearIndependent (ZMod 2) (fun E : ↥(Delta p P ρ) => (ρ t - 1) (u E)) :=
    hind.linearIndependent _ hy_mem hy_ne
  have hli' : LinearIndependent (ZMod 2)
      (fun E : ↥(Delta p P ρ) => (⟨(ρ t - 1) (u E), LinearMap.mem_range_self _ _⟩ :
        ↥(LinearMap.range (ρ t - 1)))) :=
    LinearIndependent.of_comp (LinearMap.range (ρ t - 1)).subtype hli
  haveI : Fintype ↥(Delta p P ρ) := Fintype.ofFinite _
  calc e + 1 < Nat.card ↥(Delta p P ρ) := hΔ
    _ = Fintype.card ↥(Delta p P ρ) := Nat.card_eq_fintype_card
    _ ≤ commRank ρ t := hli'.fintype_card_le_finrank

end CFSG.LocalAnalysis.RankThreeUC.Section5
