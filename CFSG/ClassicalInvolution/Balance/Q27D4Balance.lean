module

public import CFSG.ClassicalInvolution.Balance.BootstrapQ27Decomp
public import CFSG.ClassicalInvolution.Balance.LayerGenerationTorusModels
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureBasic

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.Assembly.Dichotomy CFSG.Assembly.LowTwoRank CFSG.ComponentClassification
  CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.Open (IsComponentOf)
open CFSG.ClassicalInvolution.Balance.LocalBalance (subgroupOf_involutionOddCore_le)

section Statement

@[expose] def DeltaBalanceD4Three : Prop :=
  ∀ (n p e : ℕ) (hp : p.Prime), StatedLieAdmissible .trialityD4 n p e → p ^ e = 3 →
    ∀ (X : Type) [Group X] [Finite X] (ψ : (modelUniv .trialityD4 n p e hp).K →* X),
      ψ.ker ≤ Subgroup.center (modelUniv .trialityD4 n p e hp).K → ψ.range.Normal →
      ∀ F : Subgroup X, Nat.card F = 4 → (∀ f ∈ F, f * f = 1) →
        (∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f) →
          ∀ d ∈ deltaCore F, ∀ x ∈ ψ.range, d * x = x * d

end Statement

section Glue

theorem commute_of_deltaBalance_normalizer {K : Type} [Group K] {X : Type} [Group X] [Finite X]
    (hSB : ∀ (Y : Type) [Group Y] [Finite Y] (ψ' : K →* Y), ψ'.ker ≤ Subgroup.center K →
      ψ'.range.Normal → ∀ F' : Subgroup Y, Nat.card F' = 4 → (∀ f ∈ F', f * f = 1) →
        (∀ f ∈ F', f ≠ 1 → ¬ ∀ x ∈ ψ'.range, f * x = x * f) →
          ∀ d ∈ deltaCore F', ∀ x ∈ ψ'.range, d * x = x * d)
    (ψ : K →* X) (hker : ψ.ker ≤ Subgroup.center K) {F : Subgroup X} (hcard : Nat.card F = 4)
    (hF2 : ∀ f ∈ F, f * f = 1) (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (hFN : F ≤ Subgroup.normalizer (ψ.range : Set X)) :
    ∀ d ∈ deltaCore F, d ∈ Subgroup.normalizer (ψ.range : Set X) →
      ∀ x ∈ ψ.range, d * x = x * d := by
  set N : Subgroup X := Subgroup.normalizer (ψ.range : Set X) with hN
  have hrN : ψ.range ≤ N := Subgroup.le_normalizer
  set ψ' : K →* ↥N := ψ.codRestrict N fun k => hrN ⟨k, rfl⟩ with hψ'
  have hker' : ψ'.ker ≤ Subgroup.center K := fun y hy =>
    hker (MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hy)))
  have hrange : ψ'.range = ψ.range.subgroupOf N := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, Subtype.ext hx⟩
  have hnorm' : ψ'.range.Normal := by
    rw [hrange, Subgroup.normal_subgroupOf_iff_le_normalizer hrN]
  set F' : Subgroup ↥N := F.subgroupOf N with hF'
  have hF'4 : Nat.card F' = 4 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFN).toEquiv
  have hF'2 : ∀ f ∈ F', f * f = 1 := fun f hf => Subtype.ext (hF2 f.1 hf)
  have hfaith' : ∀ f ∈ F', f ≠ 1 → ¬ ∀ x ∈ ψ'.range, f * x = x * f := by
    intro f hf hf1 hc
    refine hfaith f.1 hf (fun h => hf1 (Subtype.ext h)) fun x hx => ?_
    have hx' : (⟨x, hrN hx⟩ : ↥N) ∈ ψ'.range := by
      rw [hrange]
      exact hx
    exact congrArg Subtype.val (hc _ hx')
  have hSC := hSB ↥N ψ' hker' hnorm' F' hF'4 hF'2 hfaith'
  have hxmem : ∀ x (hx : x ∈ ψ.range), (⟨x, hrN hx⟩ : ↥N) ∈ ψ'.range := fun x hx => by
    rw [hrange]
    exact hx
  intro d hd hdN x hx
  have hd' : (⟨d, hdN⟩ : ↥N) ∈ deltaCore F' := by
    rw [mem_deltaCore_iff]
    intro f' hf' hf'1
    have hf1 : (f' : X) ≠ 1 := fun h => hf'1 (Subtype.ext h)
    exact subgroupOf_involutionOddCore_le f' (Subgroup.mem_subgroupOf.mpr
      (mem_deltaCore_iff.mp hd (f' : X) hf' hf1))
  exact congrArg Subtype.val (hSC _ hd' _ (hxmem x hx))

end Glue

section Components

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def D4ThreeAt (hΩ : InClass p f Ω) {a : G} (L : Subgroup (OddQuot a)) : Prop :=
  ∃ (D : LocalLieSystemAt p f Ω a) (j : Fin D.card), p ^ D.exp j = 3 ∧
    L = (componentHom hΩ D j).range

theorem omegaFreeAt_or_rankOneAt_or_big_or_d4Three (hp2 : p ≠ 2) (h0 : ModelClauseZero)
    (hA1 : FundamentalWholeA1) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hIH : LocalLieSystems p f Ω) {a : G} (ha : ¬ ({a} : Set G) ⊆ Subgroup.center G)
    {L : Subgroup (OddQuot a)} (hL : CFSG.IsComponent L) :
    OmegaFreeAt Ω a L ∨ RankOneAt Ω a L ∨
      ((IsOddLieComponentBig L ∨ D4ThreeAt hΩ L) ∧ L ≤ memberJoin Ω a) := by
  obtain ⟨D⟩ := hIH {a} ha
  obtain ⟨D', κ, hQ, hD⟩ := lieDecomposition_localSystem_idx hp2 h0 hA1 hq hΩ D
  have := memberJoin_normal (a := a) hΩ.conjInvariant
  have hL' : IsComponentOf L ⊤ := (CFSG.isComponent_iff_open L).mp hL
  rcases D'.eq_or_commutes_of_isComponentOf hL' with ⟨i, rfl⟩ | hcomm
  · by_cases h3 : p ^ D.exp (κ i) = 3
    · exact Or.inr (Or.inr ⟨Or.inr ⟨D, κ i, h3, hQ i⟩, D'.le_join i⟩)
    · rcases hD i h3 with ⟨⟨_, ⟨K, hK, rfl⟩, hKQ⟩, hmin⟩ | hbig
      · right
        left
        refine ⟨⟨K, hK.1, hK.2, hKQ⟩, fun K' hK'Ω hK'C => ?_⟩
        obtain ⟨j, hj⟩ := D'.exists_le (modOdd a K') ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩
        by_cases hji : j = i
        · subst hji
          exact Or.inl (hmin _ ⟨K', ⟨hK'Ω, hK'C⟩, rfl⟩ hj)
        · exact Or.inr fun x hx y hy => D'.commute j i hji x (hj hx) y hy
      · exact Or.inr (Or.inr ⟨Or.inl hbig, D'.le_join i⟩)
  · left
    intro K hKΩ hKC x hx y hy
    have hxY : x ∈ memberJoin Ω a :=
      le_iSup₂ (f := fun (K : Subgroup G) (_ : K ∈ centMembers Ω a) => modOdd a K) K
        ⟨hKΩ, hKC⟩ hx
    exact (hcomm y hy x hxY).symm

end Components

section Delta

variable {p f : ℕ} [hp : Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem commute_of_deltaBalanceD4Three {t : StatedLieTag} (ht : t = .trialityD4) {n e : ℕ}
    (hD4 : DeltaBalanceD4Three) (hadm : StatedLieAdmissible t n p e) (he3 : p ^ e = 3) {X : Type}
    [Group X] [Finite X] (ψ : (modelUniv t n p e hp.out).K →* X)
    (hker : ψ.ker ≤ Subgroup.center (modelUniv t n p e hp.out).K) {F : Subgroup X}
    (hcard : Nat.card F = 4) (hF2 : ∀ f ∈ F, f * f = 1)
    (hfaith : ∀ f ∈ F, f ≠ 1 → ¬ ∀ x ∈ ψ.range, f * x = x * f)
    (hFN : F ≤ Subgroup.normalizer (ψ.range : Set X)) :
    ∀ d ∈ deltaCore F, d ∈ Subgroup.normalizer (ψ.range : Set X) →
      ∀ x ∈ ψ.range, d * x = x * d := by
  subst ht
  exact commute_of_deltaBalance_normalizer
    (fun Y _ _ ψ' hker' hnorm' F' hF'4 hF'2 hfaith' =>
      hD4 n p e hp.out hadm he3 Y ψ' hker' hnorm' F' hF'4 hF'2 hfaith')
    ψ hker hcard hF2 hfaith hFN

theorem delta_centralizes_of_d4three (hD4 : DeltaBalanceD4Three) (hq : 5 ≤ p ^ f)
    (hΩ : InClass p f Ω) {A : Subgroup G} (hA2 : ∀ x ∈ A, x * x = 1) {a : G} (ha : a ∈ A)
    {L : Subgroup (OddQuot a)} (hL : D4ThreeAt hΩ L) {F₀ : Subgroup G}
    (hF : IsFaithfulFourGroupAt A a L F₀) :
    ∀ d ∈ deltaCore (modOdd a F₀), conjSub d L = L → ∀ x ∈ L, d * x = x * d := by
  obtain ⟨D, j, h3, rfl⟩ := hL
  obtain ⟨hF₀A, h4, hFn, hfaith⟩ := hF
  have hFC : F₀ ≤ Subgroup.centralizer ({a} : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (comm_of_sq_eq_one hA2 ha (hF₀A hg)).symm
  have hF2 : ∀ g ∈ F₀, g * g = 1 := fun g hg => hA2 g (hF₀A hg)
  have hcard : Nat.card (modOdd a F₀) = 4 := by rw [card_modOdd_of_exponent_two hFC hF2, h4]
  have hF2bar := modOdd_sq_eq_one (a := a) hA2 hF₀A
  have hexp : D.tag j = .trialityD4 ∧ 3 * D.exp j = f := by
    rcases D.exp_eq j with h | h
    · exfalso
      rw [h] at h3
      omega
    · exact h
  intro d hd hdL
  exact commute_of_deltaBalanceD4Three hexp.1 hD4 (D.admissible j) h3 (componentHom hΩ D j)
    (componentHom_ker_le_center hΩ D j) hcard hF2bar hfaith hFn d hd
    (mem_normalizer_of_conjSub_eq hdL)

end Delta

end CFSG.ClassicalInvolution.Balance.Q27
