module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrModel
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHubs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrLarge
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrTwoFam
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrSp
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrOrth
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrUni

public section

namespace CFSG.AGLEmbedding.ParabAutIrr

open CFSG.AGLEmbedding CFSG.Assembly.LowTwoRank
open scoped commutatorElement

@[expose] def YLevelIrrOn (C : (Y : Type) → [Group Y] → Prop) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], C Y →
    Function.Injective (MulAut.conj : Y →* MulAut Y) →
    ∀ (p r : ℕ), p.Prime → p ≠ 2 → r.Prime → r ≠ 2 → r ≠ 3 → r ≠ p →
    ∀ (S₀ : Sylow 2 Y) (J : Subgroup Y), Subgroup.normalizer (S₀ : Set Y) ≤ J →
      PerfectCyclicSylow p J →
      ∀ (U Z : Subgroup (MulAut Y)) (y : MulAut Y), IsPGroup p U → Z = ⁅U, U⁆ → IrrAct y U Z →
        p ^ 3 ≤ Z.relIndex U → (∀ u ∈ U, u ^ p ∈ Z) →
        y ∈ Subgroup.normalizer (U : Set (MulAut Y)) →
        U ≤ Subgroup.normalizer
          ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)) →
        y ∈ Subgroup.normalizer
          ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)) →
        (∃ a : ℕ, y ^ r ^ a = 1) → False

@[expose] def IsG2Two (Y : Type) [Group Y] : Prop :=
  ∃ (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 ∧
    Nonempty (Y ≃* (TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.G2 q, hv⟩).Group)

@[expose] def IsSmallTwo (Y : Type) [Group Y] : Prop :=
  (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 8) ∧ Nonempty (Y ≃* alternatingGroup (Fin n))) ∨
    (∃ d : TauCeti.ValidLieTypeIndex, ((∃ q : TauCeti.PrimePower, q.card = 7 ∧ d.1 = .A 1 q) ∨
        (∃ q : TauCeti.PrimePower, q.card = 3 ∧ d.1 = .twistedA 2 q)) ∧
      Nonempty (Y ≃* (TauCeti.CFSGIndex.lie d).Group))

@[expose] def OrthPlusR2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ),
    StatedClassicalModel Y .POmegaPlus n 2 f → 2 ≤ f → AutScalarTorus Y

@[expose] def OrthMinusR2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ),
    StatedClassicalModel Y .POmegaMinus n 2 f → 2 ≤ f → AutScalarTorus Y

@[expose] def UniR2 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (n f : ℕ),
    StatedClassicalModel Y .PSU n 2 f → 2 ≤ f → AutScalarTorus Y

theorem isClassicalTwoOrG2_cases {Y : Type} [Group Y] (h : IsClassicalTwoOrG2 Y) :
    (∃ (t : StatedLieTag) (n f : ℕ), ClassicalTag t ∧ StatedClassicalModel Y t n 2 f) ∨
      IsG2Two Y ∨ IsSmallTwo Y := by
  rcases h with ⟨d, hd, ⟨e⟩⟩ | h | h
  · rcases classical_model_or_g2 d hd e with h | ⟨q, hv, hq, rfl⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl ⟨q, hv, hq, ⟨e⟩⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

section Dispatch

variable {Y : Type} [Group Y] [Finite Y]
  (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
  {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
  (S₀ : Sylow 2 Y) {J : Subgroup Y} (hJ : Subgroup.normalizer (S₀ : Set Y) ≤ J)
  (hcyc : PerfectCyclicSylow p J) {U Z : Subgroup (MulAut Y)} {y : MulAut Y}
  (hU : IsPGroup p U) (hZ : Z = ⁅U, U⁆) (hirr : IrrAct y U Z) (hrel : p ^ 3 ≤ Z.relIndex U)
  (hpow : ∀ u ∈ U, u ^ p ∈ Z) (hyU : y ∈ Subgroup.normalizer (U : Set (MulAut Y)))
  (hUJ : U ≤ Subgroup.normalizer
    ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)))
  (hyJ : y ∈ Subgroup.normalizer
    ((J.map (MulAut.conj : Y →* MulAut Y) : Subgroup (MulAut Y)) : Set (MulAut Y)))
  (hyr : ∃ a : ℕ, y ^ r ^ a = 1)

include hinj hp hp2 hr hr2 hr3 hJ hcyc hU hZ hirr hrel hpow hyU hUJ hyJ hyr in
theorem false_of_model (hOP : OrthPlusR2) (hOM : OrthMinusR2) (hUR : UniR2) {t : StatedLieTag}
    {n f : ℕ} (ht : ClassicalTag t) (h : StatedClassicalModel Y t n 2 f) : False := by
  have hf1 : 1 ≤ f := by
    rcases ht with rfl | rfl | rfl | rfl | rfl <;> exact h.1.2.1
  have hr5 : 5 ≤ r := by
    have h2 := hr.two_le
    by_contra hlt
    interval_cases r
    · exact hr2 rfl
    · exact hr3 rfl
    · exact absurd hr (by norm_num)
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    by_cases hf : f = 1
    · subst hf
      exact false_of_two hinj (twoHub_of_model_psl h) hp hr hr5 (outPTwoGen_psl h hp hp2)
        (outPInner_psl_two h hr hr2) S₀ hJ hcyc hU hZ hirr hrel hpow hyU hUJ hyJ hyr
    · exact false_of_large hinj (parabStruct_of_model_psl h (by omega)) hp hp2 hr hr2 hr3
        (outPTwoGen_psl h hp hp2) (autScalarTorus_psl h) S₀ hJ hcyc hU hZ hirr hrel hpow hyU hUJ
        hyJ hyr
  ·
    by_cases hf : f = 1
    · subst hf
      exact false_of_two hinj (twoHub_of_model_psu h) hp hr hr5 (outPTwoGen_psu h)
        (outPInner_psu_two h hr hr5) S₀ hJ hcyc hU hZ hirr hrel hpow hyU hUJ hyJ hyr
    · exact false_of_large hinj (parabStruct_of_model_psu h (by omega)) hp hp2 hr hr2 hr3
        (outPTwoGen_psu h) (hUR Y n f h (by omega)) S₀ hJ hcyc hU hZ hirr hrel hpow hyU hUJ hyJ
        hyr
  ·
    by_cases hf : f = 1
    · subst hf
      exact false_of_two hinj (twoHub_of_model_psp h) hp hr hr5 (outPTwoGen_psp h hp)
        (outPInner_psp_two h) S₀ hJ hcyc hU hZ hirr hrel hpow hyU hUJ hyJ hyr
    · exact false_of_large hinj (parabStruct_of_model_psp h (by omega)) hp hp2 hr hr2 hr3
        (outPTwoGen_psp h hp) (autScalarTorus_psp h) S₀ hJ hcyc hU hZ hirr hrel hpow hyU hUJ hyJ
        hyr
  ·
    by_cases hf : f = 1
    · subst hf
      exact false_of_two hinj (twoHub_of_model_pomegaPlus h) hp hr hr5
        (outPTwoGen_pomegaPlus h hp hp2) (outPInner_pomegaPlus_two h hr hr5) S₀ hJ hcyc hU hZ
        hirr hrel hpow hyU hUJ hyJ hyr
    · exact false_of_large hinj (parabStruct_of_model_pomegaPlus h (by omega)) hp hp2 hr hr2 hr3
        (outPTwoGen_pomegaPlus h hp hp2) (hOP Y n f h (by omega)) S₀ hJ hcyc hU hZ hirr hrel hpow
        hyU hUJ hyJ hyr
  ·
    by_cases hf : f = 1
    · subst hf
      exact false_of_two hinj (twoHub_of_model_pomegaMinus h) hp hr hr5
        (outPTwoGen_pomegaMinus h hp hp2) (outPInner_pomegaMinus_two h hr hr5) S₀ hJ hcyc hU hZ
        hirr hrel hpow hyU hUJ hyJ hyr
    · exact false_of_large hinj (parabStruct_of_model_pomegaMinus h (by omega)) hp hp2 hr hr2 hr3
        (outPTwoGen_pomegaMinus h hp hp2) (hOM Y n f h (by omega)) S₀ hJ hcyc hU hZ hirr hrel
        hpow hyU hUJ hyJ hyr

end Dispatch

theorem yLevelIrr_of_inputs (hOP : OrthPlusR2) (hOM : OrthMinusR2) (hUR : UniR2)
    (hG : YLevelIrrOn IsG2Two) (hS : YLevelIrrOn IsSmallTwo) : YLevelIrr := by
  intro Y _ _ hC hinj p r hp hp2 hr hr2 hr3 hrp S₀ J hJ hcyc U Z y hU hZ hirr hrel hpow hyU hUJ hyJ
    hyr
  rcases isClassicalTwoOrG2_cases hC with ⟨t, n, f, ht, h⟩ | hG2 | hSm
  · exact false_of_model hinj hp hp2 hr hr2 hr3 S₀ hJ hcyc hU hZ hirr hrel hpow hyU hUJ hyJ hyr hOP
      hOM hUR ht h
  · exact hG Y hG2 hinj p r hp hp2 hr hr2 hr3 hrp S₀ J hJ hcyc U Z y hU hZ hirr hrel hpow hyU hUJ
      hyJ hyr
  · exact hS Y hSm hinj p r hp hp2 hr hr2 hr3 hrp S₀ J hJ hcyc U Z y hU hZ hirr hrel hpow hyU hUJ
      hyJ hyr

end CFSG.AGLEmbedding.ParabAutIrr
