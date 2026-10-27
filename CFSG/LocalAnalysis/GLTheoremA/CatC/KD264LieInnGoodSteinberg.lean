module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGoodLangTorus
public import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2.E7FiveAux.Plane

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Classical CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2


theorem perfectCentralizerPlanes_adjointGroup_steinberg {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hpK : ¬ p ∣ Nat.card K)
    (htor : LangToralPlane τ p)
    (hst : ∀ b : Fin τ.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ p = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b)
    {w₀ : WeylGroup τ} (hw₀ : ∀ u : Fin τ.rank → ℤ, w₀ • u = -u)
    (hqp : Nat.card K % p = 1 ∨ Nat.card K % p = p - 1) (hK4 : 4 ≤ Nat.card K) :
    PerfectCentralizerPlanes p (adjointGroup τ K) := by
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := Or.inr (Or.inr hτ)
  have hτG : τ ≠ .G2 := by rcases hτ with rfl | rfl <;> decide
  have hdeg : entryDegreeBound τ < Nat.card K := by
    unfold entryDegreeBound
    split_ifs with h
    · exact absurd h hτG
    · omega
  refine perfectCentralizerPlanes_adjointGroup_of_langTorus (W := fun _ => True) hτ' K hp hpK
    (Or.inr hK4) (fun A hA hAc => ?_) ?_
  · obtain ⟨w, Fr, hFr, g0, hg0C, hg0, c, hc⟩ := htor K hpK A hA hAc
    exact ⟨w, trivial, Fr, hFr, g0, hg0C, hg0, c, hc⟩
  · intro w _ Fr hFr g0 hg0C hg0 S hSD D₁ hD₁ hc
    exact bigComponentSet_nonempty_of_centralizerTrivial S hD₁ hc
      (steinbergLang_centralizerTrivial K hFr hg0C hg0 S hSD hp hst hw₀ hqp hK4 hdeg hD₁ hc)

theorem perfectCentralizerPlanes_adjointGroup_E7_five_steinberg
    (K : Type) [Field K] [Finite K] (hd : 5 ∣ Nat.card K - 1 ∨ 5 ∣ Nat.card K + 1) :
    PerfectCentralizerPlanes 5 (adjointGroup Tag.E7 K) := by
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  exact perfectCentralizerPlanes_adjointGroup_steinberg (Or.inl rfl) K Nat.prime_five
    (by omega) langToralPlane_E7_five
    (fun b hb => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_five b hb).le)
    e7Neg_smul (by omega) (by omega)

theorem perfectCentralizerPlanes_adjointGroup_E7_seven_steinberg
    (K : Type) [Field K] [Finite K] (hd : 7 ∣ Nat.card K - 1 ∨ 7 ∣ Nat.card K + 1) :
    PerfectCentralizerPlanes 7 (adjointGroup Tag.E7 K) := by
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  exact perfectCentralizerPlanes_adjointGroup_steinberg (Or.inl rfl) K (by norm_num)
    (by omega)
    (langToralPlane_of_bar (by norm_num) planesToralBar_E7_seven)
    (fun b hb => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E7_seven b hb).le)
    e7Neg_smul (by omega) (by omega)

theorem perfectCentralizerPlanes_adjointGroup_E8_five_steinberg
    (K : Type) [Field K] [Finite K] (hd : 5 ∣ Nat.card K - 1 ∨ 5 ∣ Nat.card K + 1) :
    PerfectCentralizerPlanes 5 (adjointGroup Tag.E8 K) := by
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  exact perfectCentralizerPlanes_adjointGroup_steinberg (Or.inr rfl) K Nat.prime_five
    (by omega) (langToralPlane_E8_five_iff.2 e8FiveToralPlane_proved)
    (fun b hb => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_five b hb).le)
    e8Neg_smul (by omega) (by omega)

theorem perfectCentralizerPlanes_adjointGroup_E8_seven_steinberg
    (K : Type) [Field K] [Finite K] (hd : 7 ∣ Nat.card K - 1 ∨ 7 ∣ Nat.card K + 1) :
    PerfectCentralizerPlanes 7 (adjointGroup Tag.E8 K) := by
  have h2 : 2 ≤ Nat.card K := Finite.one_lt_card
  exact perfectCentralizerPlanes_adjointGroup_steinberg (Or.inr rfl) K (by norm_num)
    (by omega)
    (langToralPlane_of_bar (by norm_num) planesToralBar_E8_seven)
    (fun b hb => (rootCharStabilizerSubgroup_eq_kernelReflectionGroup_E8_seven b hb).le)
    e8Neg_smul (by omega) (by omega)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
