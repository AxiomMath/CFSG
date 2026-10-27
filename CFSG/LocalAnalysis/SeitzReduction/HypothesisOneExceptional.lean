module

public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneExceptionalOuter
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6OuterInvolutionOddCore
public import CFSG.RankThree.Chevalley.SteinbergCFExceptionalModelCover
public import CFSG.LocalAnalysis.EvenSmallLie.CyclicKernelSylow
public import CFSG.LieType.Chevalley.EvenOuterInvolutionOddCoreE7E8
public import CFSG.LieType.Chevalley.EvenOuterInvolutionOddCoreF4

public section

namespace CFSG.SeitzReduction

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977 (HypothesisOne)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

@[expose] def InnerInvolutionInput (C : Type*) [Group C] : Prop :=
  ∀ H : Subgroup (MulAut C), inner C ≤ H → ∀ α ∈ inner C, orderOf α = 2 →
    NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({α} : Set (MulAut C)))

@[expose] def OuterInvolutionInput (C : Type*) [Group C] : Prop :=
  ∀ H : Subgroup (MulAut C), inner C ≤ H → ∀ α ∈ H, α ∉ inner C → orderOf α = 2 →
    NoNormalZ4OrZ2xZ4 ↥(H ⊓ centralizer ({α} : Set (MulAut C)))

theorem hypothesisOne_of_inputs {C : Type*} [Group C]
    (hcore : ∀ H : Subgroup (MulAut C), inner C ≤ H → ∀ α ∈ H, orderOf α = 2 →
      CFSG.oddCore ↥(H ⊓ centralizer ({α} : Set (MulAut C))) = ⊥)
    (hin : InnerInvolutionInput C) (hout : OuterInvolutionInput C) : HypothesisOne C :=
  hypothesisOne_of_centralizers fun M hM x hxM hx2 => ⟨hcore M hM x hxM hx2, by
    by_cases hx : x ∈ inner C
    · exact hin M hM x hx hx2
    · exact hout M hM x hxM hx hx2⟩

theorem outerInvolutionInput_E7_E8
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) : OuterInvolutionInput (adjointGroup τ K) :=
  fun H hIH _ _ hαI hα =>
    (even_E7_E8_outer_involution_abelianNormalCardLeTwo τ hτ hf K hK H hIH hαI hα).noNormalZ4OrZ2xZ4

theorem outerInvolutionInput_F4
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) :
    OuterInvolutionInput (adjointGroup .F4 K) :=
  fun H hIH _ _ hαI hα =>
    (even_F4_outer_involution_abelianNormalCardLeTwo hf K hK H hIH hαI hα).noNormalZ4OrZ2xZ4

theorem hypothesisOne_E7_E8_of_inner
    (τ : Tag) (hτ : τ = .E7 ∨ τ = .E8) {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = 2 ^ f) (hin : InnerInvolutionInput (adjointGroup τ K)) :
    HypothesisOne (adjointGroup τ K) := by
  refine hypothesisOne_of_inputs (fun H hIH α _ hα => ?_) hin
    (outerInvolutionInput_E7_E8 τ hτ hf K hK)
  by_cases hαI : α ∈ inner (adjointGroup τ K)
  · have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ (τ = .G2 ∧ 2 ≤ f) := by
      rcases hτ with h | h
      · exact .inr (.inr (.inl h))
      · exact .inr (.inr (.inr (.inl h)))
    exact (CFSG.RankThree.Chevalley.oddCore_eq_pPrimeCore_two' _).trans
      (even_exceptional_inner_involution_full_centralizer_odd_core.1 τ f K hf hK hτ' H hIH α hαI hα)
  · exact even_E7_E8_outer_involution_full_centralizer_odd_core τ hτ hf K hK H hIH hαI hα

theorem hypothesisOne_F4_of_inner
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (hin : InnerInvolutionInput (adjointGroup .F4 K)) : HypothesisOne (adjointGroup .F4 K) := by
  refine hypothesisOne_of_inputs (fun H hIH α _ hα => ?_) hin (outerInvolutionInput_F4 hf K hK)
  by_cases hαI : α ∈ inner (adjointGroup .F4 K)
  · exact (CFSG.RankThree.Chevalley.oddCore_eq_pPrimeCore_two' _).trans
      (even_exceptional_inner_involution_full_centralizer_odd_core.1 .F4 f K hf hK (.inl rfl) H
        hIH α hαI hα)
  · exact even_F4_outer_involution_full_centralizer_odd_core hf K hK H hIH hαI hα

theorem hypothesisOne_E6_of_inputs
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = 2 ^ f)
    (hin : InnerInvolutionInput (adjointGroup .E6 K))
    (hout : OuterInvolutionInput (adjointGroup .E6 K)) : HypothesisOne (adjointGroup .E6 K) := by
  refine hypothesisOne_of_inputs (fun H hIH α hαH hα => ?_) hin hout
  by_cases hαI : α ∈ inner (adjointGroup .E6 K)
  · exact (CFSG.RankThree.Chevalley.oddCore_eq_pPrimeCore_two' _).trans
      (even_exceptional_inner_involution_full_centralizer_odd_core.1 .E6 f K hf hK (.inr (.inl rfl))
        H hIH α hαI hα)
  · exact (CFSG.RankThree.Chevalley.even_E6_twisted_E6_outer_involution_full_centralizer_odd_core
      hf).1 K hK H hIH α hαH hαI hα

theorem hypothesisOne_twistedE6_of_inputs
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (hin : InnerInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom))
    (hout : OuterInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom)) :
    HypothesisOne (graphFixedRootGroup .E6 K σ.toRingHom) := by
  refine hypothesisOne_of_inputs (fun H hIH α hαH hα => ?_) hin hout
  by_cases hαI : α ∈ inner (graphFixedRootGroup .E6 K σ.toRingHom)
  · exact (CFSG.RankThree.Chevalley.oddCore_eq_pPrimeCore_two' _).trans
      (even_exceptional_inner_involution_full_centralizer_odd_core.2 .E6 f K σ hf hK hσ H hIH α
        hαI hα)
  · exact (CFSG.RankThree.Chevalley.even_E6_twisted_E6_outer_involution_full_centralizer_odd_core
      hf).2 K hK σ.toRingHom hσ H hIH α hαH hαI hα

@[expose] def ExceptionalHypothesisOne : Prop :=
  ∀ (Y : Type) [Group Y] (τ : StatedLieTag) (f : ℕ),
    (τ = .F4 ∨ τ = .E6 ∨ τ = .twistedE6 ∨ τ = .E7 ∨ τ = .E8) → LieModel Y τ 0 2 f →
      HypothesisOne Y

@[expose] def ExceptionalHypothesisOneInputs :
    Prop :=
  (∀ (τ : Tag) (f : ℕ) (K : Type) [Field K], 1 ≤ f → Nat.card K = 2 ^ f →
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → InnerInvolutionInput (adjointGroup τ K)) ∧
    (∀ (f : ℕ) (K : Type) [Field K], 1 ≤ f → Nat.card K = 2 ^ f →
      OuterInvolutionInput (adjointGroup .E6 K)) ∧
    ∀ (f : ℕ) (K : Type) [Field K] (σ : K ≃+* K), 1 ≤ f → Nat.card K = (2 ^ f) ^ 2 →
      (∀ c, σ c = c ^ 2 ^ f) →
      InnerInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom) ∧
        OuterInvolutionInput (graphFixedRootGroup .E6 K σ.toRingHom)

theorem exceptionalHypothesisOne_of_inputs
    (h : ExceptionalHypothesisOneInputs) : ExceptionalHypothesisOne := by
  intro Y _ τ f hτ hY
  rcases hY with ⟨hcl, -⟩ | ⟨-, -, hadm, hcase⟩ | ⟨-, hrt, -⟩ | ⟨-, hB2, -⟩
  · exfalso
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;> simp [classicalTags] at hcl
  · have hf : 1 ≤ f := hadm.2.1
    rcases hτ with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
      exact EvenSmallLie.hypothesisOne_of_mulEquiv
        (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K)).symm
        (hypothesisOne_F4_of_inner hf K hK (h.1 .F4 f K hf hK (.inl rfl)))
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
      exact EvenSmallLie.hypothesisOne_of_mulEquiv
        (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K)).symm
        (hypothesisOne_E6_of_inputs hf K hK (h.1 .E6 f K hf hK (.inr (.inl rfl)))
          (h.2.1 f K hf hK))
    · obtain ⟨K, _, _, hK, σ, hσ, ⟨e⟩⟩ := hcase
      obtain ⟨σ', rfl⟩ : ∃ σ' : K ≃+* K, σ'.toRingHom = σ :=
        ⟨RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩,
          RingHom.ext fun _ => rfl⟩
      obtain ⟨e'⟩ := RankThree.Chevalley.nonempty_derivedCentralQuotient_equiv _ Nat.prime_two hf
        K hK _ hσ
      obtain ⟨hin, hout⟩ := h.2.2 f K σ' hf hK hσ
      exact EvenSmallLie.hypothesisOne_of_mulEquiv (e.trans e').symm
        (hypothesisOne_twistedE6_of_inputs hf K hK σ' hσ hin hout)
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
      exact EvenSmallLie.hypothesisOne_of_mulEquiv
        (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K)).symm
        (hypothesisOne_E7_E8_of_inner .E7 (.inl rfl) hf K hK
          (h.1 .E7 f K hf hK (.inr (.inr (.inl rfl)))))
    · obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hcase
      exact EvenSmallLie.hypothesisOne_of_mulEquiv
        (e.trans (RankThree.Chevalley.adjointQuotientEquiv _ K)).symm
        (hypothesisOne_E7_E8_of_inner .E8 (.inr rfl) hf K hK
          (h.1 .E8 f K hf hK (.inr (.inr (.inr rfl)))))
  · exfalso
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;> simp [reeTitsTags] at hrt
  · exfalso
    rcases hτ with rfl | rfl | rfl | rfl | rfl <;> simp at hB2

end CFSG.SeitzReduction
