module

public import CFSG.ClassicalInvolution.Asc77.AscThm5IHBase

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

@[expose] def T5BaseAt (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (k e : ℕ) (P : Prop → Prop) :
    Prop :=
  p ≠ 2 → 5 ≤ p ^ f → IsFundTag t → StatedLieAdmissible t k p e →
    (e = f ∨ (t = .trialityD4 ∧ 3 * e = f)) →
      ∀ (H : Type) [Group H] [Finite H] (ψ : (modelUniv t k p e Fact.out).K →* H),
        ψ.ker ≤ Subgroup.center (modelUniv t k p e Fact.out).K →
        ∀ R ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
          ∀ R' ∈ fundamentalSubgroups t (modelUniv t k p e Fact.out).D,
            Nonempty (↥(R.map ψ) ≃* SL(2, GaloisField p f)) →
            Nonempty (↥(R'.map ψ) ≃* SL(2, GaloisField p f)) →
            R.map ψ ≠ R'.map ψ → Commutes (R.map ψ) (R'.map ψ) →
            ∀ z : H, IsUniqueInvolution (R.map ψ) z → P (z ∈ R'.map ψ) →
              ∀ A : Subgroup H, IsElemAbelian2 A 2 → A ≤ R.map ψ ⊔ R'.map ψ → z ∈ A →
                (∀ a ∈ A, a ≠ 1 → ¬ ∀ x ∈ ψ.range, a * x = x * a) →
                  alphaOf (inducedImage ψ.range A) = ⊥

variable {p f : ℕ} [Fact p.Prime]

theorem t5Base_iff_at : T5Base p f ↔ ∀ (t : StatedLieTag) (k e : ℕ),
    T5BaseAt p f t k e (fun _ => True) := by
  constructor
  · intro h t k e hp hq hf ha he H _ _ ψ hker R hR R' hR' eK eJ hne hc z hz _ A hA hAKJ hzA hfa
    exact h hp hq t k e hf ha he H ψ hker R hR R' hR' eK eJ hne hc z hz A hA hAKJ hzA hfa
  · intro h hp hq t k e hf ha he H _ _ ψ hker R hR R' hR' eK eJ hne hc z hz A hA hAKJ hzA hfa
    exact h t k e hp hq hf ha he H ψ hker R hR R' hR' eK eJ hne hc z hz trivial A hA hAKJ hzA hfa

theorem t5BaseAt_of_split {t : StatedLieTag} {k e : ℕ} (h1 : T5BaseAt p f t k e id)
    (h2 : T5BaseAt p f t k e Not) : T5BaseAt p f t k e (fun _ => True) := by
  intro hp hq hf ha he H _ _ ψ hker R hR R' hR' eK eJ hne hc z hz _ A hA hAKJ hzA hfa
  by_cases hzJ : z ∈ R'.map ψ
  · exact h1 hp hq hf ha he H ψ hker R hR R' hR' eK eJ hne hc z hz hzJ A hA hAKJ hzA hfa
  · exact h2 hp hq hf ha he H ψ hker R hR R' hR' eK eJ hne hc z hz hzJ A hA hAKJ hzA hfa

@[expose] def T5BaseTwin (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (k e : ℕ) : Prop :=
  T5BaseAt p f t k e id

@[expose] def T5BaseNT (p f : ℕ) [Fact p.Prime] (t : StatedLieTag) (k e : ℕ) : Prop :=
  T5BaseAt p f t k e Not

theorem t5Base_of_twin_of_nt (h1 : ∀ (t : StatedLieTag) (k e : ℕ), T5BaseTwin p f t k e)
    (h2 : ∀ (t : StatedLieTag) (k e : ℕ), T5BaseNT p f t k e) : T5Base p f :=
  t5Base_iff_at.mpr fun t k e => t5BaseAt_of_split (h1 t k e) (h2 t k e)

end CFSG.ClassicalInvolution.Asc77
