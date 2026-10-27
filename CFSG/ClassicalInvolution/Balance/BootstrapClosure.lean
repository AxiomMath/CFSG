module

import CFSG.ClassicalInvolution.Generic.InductionLocal
import CFSG.ClassicalInvolution.Generic.StepMember
public import CFSG.ClassicalInvolution.Generic.Generation.DeltaClosureStep
public import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.ClassicalInvolution.Balance.Bootstrap

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Generic.DeltaClosure
open CFSG.ClassicalInvolution.Balance (oddCoreIn odd_card_oddCoreIn)

section Defs

variable {G : Type} [Group G]

@[expose] def rankTwoSpan (A : Subgroup G) : Subgroup G :=
  ⨆ F ∈ signalizerFunctorEk 2 2 A, Subgroup.centralizer (F : Set G)

@[expose] def CentralizerGenerationModOTwo (Ω : Set (Subgroup G)) (A : Subgroup G) (a : G) : Prop :=
  centralizingLayer Ω {a} ≤ oddCoreIn (centralizingLayer Ω {a}) ⊔
    ⨆ F ∈ signalizerFunctorEk 2 2 A, (Subgroup.centralizer (F : Set G) ⊓ centralizingLayer Ω {a})

variable (p f : ℕ) [Fact p.Prime]

structure FrameSideTwo (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) : Prop where
  elem : IsElemAbelian 2 A
  card : 8 ≤ Nat.card A
  subset : S ⊆ Ω
  nonempty : S.Nonempty
  involution : ∀ K ∈ S, ∃ z ∈ A, IsClassicalMember p f K z
  generation : ∀ a ∈ A, IsFrameInvolution p f S a → CentralizerGenerationModOTwo Ω A a
  link : ∀ a ∈ A, IsFrameInvolution p f S a → InvolutionLink p f Ω A S a

@[expose] def omegaStarTwo (Ω : Set (Subgroup G)) (A : Subgroup G) (S : Set (Subgroup G)) :
    Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ h ∈ rankTwoSpan A, ∃ K ∈ S, ∃ z ∈ A,
    IsClassicalMember p f K z ∧ IsClassicalMember p f L (h * z * h⁻¹)}

end Defs

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

omit [Finite G] in
theorem le_rankTwoSpan_of_le_centralizer {K F : Subgroup G} (hF : F ∈ signalizerFunctorEk 2 2 A)
    (hK : K ≤ Subgroup.centralizer (F : Set G)) : K ≤ rankTwoSpan A :=
  hK.trans (le_iSup₂ (f := fun (E : Subgroup G) (_ : E ∈ signalizerFunctorEk 2 2 A) =>
    Subgroup.centralizer (E : Set G)) F hF)

theorem oddCoreIn_centralizingLayer_le_rankTwoSpan (hΩ : ConjInvariant Ω)
    (hA : IsElemAbelian 2 A) (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A) :
    oddCoreIn (centralizingLayer Ω {a}) ≤ rankTwoSpan A := by
  have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 2 2
    Nat.prime_two A (oddCoreIn (centralizingLayer Ω {a})) hA (by simpa using h8)
    (le_normalizer_oddCoreIn_centralizingLayer hΩ hA ha)
    (Nat.coprime_two_left.mpr (odd_card_oddCoreIn _))
  conv_lhs => rw [← hgen]
  exact iSup₂_le fun F hF => le_rankTwoSpan_of_le_centralizer hF inf_le_right

theorem centralizingLayer_le_rankTwoSpan (hΩ : ConjInvariant Ω) (hA : IsElemAbelian 2 A)
    (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A) (hgen : CentralizerGenerationModOTwo Ω A a) :
    centralizingLayer Ω {a} ≤ rankTwoSpan A :=
  hgen.trans (sup_le (oddCoreIn_centralizingLayer_le_rankTwoSpan hΩ hA h8 ha)
    (iSup₂_le fun _ hF => le_rankTwoSpan_of_le_centralizer hF inf_le_left))

theorem mem_omegaStarTwo_of_commutes (hΩ : InClass p f Ω) (hF : FrameSideTwo p f Ω A S)
    {L L' : Subgroup G} (hLs : L ∈ omegaStarTwo p f Ω A S) (hL' : L' ∈ Ω) (hc : Commutes L L') :
    L' ∈ omegaStarTwo p f Ω A S := by
  obtain ⟨hLΩ, h₀, hh₀, K, hKS, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember_conj_inv hLa
  have hc' : Commutes (conjSub h₀⁻¹ L) (conjSub h₀⁻¹ L') := hc.conjSub h₀⁻¹
  set M := conjSub h₀⁻¹ L' with hM
  have hMΩ : M ∈ Ω := hconj _ _ hL'
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc' a hLa'.mem x hx).symm
  have hMmem : M ∈ centralizingMembers Ω {a} := ⟨hMΩ, hMa⟩
  obtain ⟨z₀, hz₀⟩ := hΩ.classical M hMΩ
  obtain ⟨K', hK'S, z', hz'A, hK'z', h₁, hh₁Y, hz₀h₁⟩ :=
    hF.link a haA ⟨K, hKS, hKa⟩ M hMmem z₀ hz₀
  have hYH := centralizingLayer_le_rankTwoSpan hconj hF.elem hF.card haA
    (hF.generation a haA ⟨K, hKS, hKa⟩)
  have hz₀' : IsClassicalMember p f M (h₁ * z' * h₁⁻¹) := by rwa [← hz₀h₁]
  have hL'z : IsClassicalMember p f L' (h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹) := by
    have := hz₀'.conj h₀
    rwa [hM, conjSub_conjSub_inv] at this
  refine ⟨hL', h₀ * h₁, mul_mem hh₀ (hYH hh₁Y), K', hK'S, z', hz'A, hK'z', ?_⟩
  have e : h₀ * h₁ * z' * (h₀ * h₁)⁻¹ = h₀ * (h₁ * z' * h₁⁻¹) * h₀⁻¹ := by group
  rwa [e]

theorem le_rankTwoSpan_of_mem_omegaStarTwo (hΩ : InClass p f Ω) (hF : FrameSideTwo p f Ω A S)
    {L : Subgroup G} (hLs : L ∈ omegaStarTwo p f Ω A S) : L ≤ rankTwoSpan A := by
  obtain ⟨hLΩ, h, hh, K, hK, a, haA, hKa, hLa⟩ := hLs
  have hconj := hΩ.conjInvariant
  have hLa' := isClassicalMember_conj_inv hLa
  have hmem : conjSub h⁻¹ L ∈ centralizingMembers Ω {a} := ⟨hconj _ _ hLΩ, le_centralizer hLa'⟩
  have hY : conjSub h⁻¹ L ≤ rankTwoSpan A :=
    (le_centralizingLayer hmem).trans (centralizingLayer_le_rankTwoSpan hconj hF.elem hF.card haA
      (hF.generation a haA ⟨K, hK, hKa⟩))
  intro x hx
  have h1 : h⁻¹ * x * h ∈ conjSub h⁻¹ L := by
    rw [mem_conjSub_iff]
    simpa [mul_assoc] using hx
  have h2 := hY h1
  have h3 : x = h * (h⁻¹ * x * h) * h⁻¹ := by group
  rw [h3]
  exact mul_mem (mul_mem hh h2) (inv_mem hh)

theorem mem_omegaStarTwo_of_omegaConnected (hΩ : InClass p f Ω) (hF : FrameSideTwo p f Ω A S)
    (hconn : OmegaConnected Ω) {L : Subgroup G} (hLΩ : L ∈ Ω) : L ∈ omegaStarTwo p f Ω A S := by
  obtain ⟨K₀, hK₀⟩ := hF.nonempty
  obtain ⟨z, hzA, hz⟩ := hF.involution K₀ hK₀
  have hK₀s : K₀ ∈ omegaStarTwo p f Ω A S :=
    ⟨hF.subset hK₀, 1, one_mem _, K₀, hK₀, z, hzA, hz, by simpa using hz⟩
  have key : ∀ L', Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) K₀ L' →
      L' ∈ omegaStarTwo p f Ω A S := by
    intro L' hpath
    induction hpath with
    | refl => exact hK₀s
    | tail _ hbc ih => exact mem_omegaStarTwo_of_commutes hΩ hF ih hbc.1 hbc.2
  exact key L (hconn K₀ (hF.subset hK₀) L hLΩ)

theorem rankTwoSpan_eq_top (hΩ : InClass p f Ω) (hF : FrameSideTwo p f Ω A S)
    (hconn : OmegaConnected Ω) : rankTwoSpan A = ⊤ := by
  refine top_unique ?_
  rw [← hΩ.generated]
  exact iSup₂_le fun _ hLΩ => le_rankTwoSpan_of_mem_omegaStarTwo hΩ hF
    (mem_omegaStarTwo_of_omegaConnected hΩ hF hconn hLΩ)

end CFSG.ClassicalInvolution.Balance.Bootstrap
