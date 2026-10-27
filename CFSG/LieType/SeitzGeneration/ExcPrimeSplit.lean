module

public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem PrimeRange.eq_three_or_five_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p = 3 ∨ 5 ≤ p := by
  have h2 := hp.two_le
  rcases (by omega : p = 3 ∨ p = 4 ∨ 5 ≤ p) with h | h | h
  · exact Or.inl h
  · subst h
    exact absurd hp (by norm_num)
  · exact Or.inr h

@[expose] def PrimeRange.three : TauCeti.LieTypeIndex → ℕ → Prop := fun _ p => p = 3

@[expose] def PrimeRange.geFive : TauCeti.LieTypeIndex → ℕ → Prop := fun _ p => 5 ≤ p

@[expose] def PrimeRange.all : TauCeti.LieTypeIndex → ℕ → Prop := fun _ _ => True

@[expose] def SeitzExcAnisotropicForAt (P : TauCeti.LieTypeIndex → Prop)
    (Q : TauCeti.LieTypeIndex → ℕ → Prop) : Prop :=
  SeitzPlanes fun d p E =>
    InnerPlane d p E ∧ P d.1 ∧ Q d.1 p ∧ RankLE2 p (Cat d) ∧ ¬ NormalizesRSubgroup d E

theorem SeitzExcAnisotropicFor.toAt {P : TauCeti.LieTypeIndex → Prop}
    (h : SeitzExcAnisotropicFor P) (Q : TauCeti.LieTypeIndex → ℕ → Prop) :
    SeitzExcAnisotropicForAt P Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, hE.2.2.2⟩) h

theorem seitzExcAnisotropicFor_iff_at {P : TauCeti.LieTypeIndex → Prop} :
    SeitzExcAnisotropicFor P ↔ SeitzExcAnisotropicForAt P PrimeRange.all :=
  ⟨fun h => h.toAt _, fun h =>
    SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, trivial, hE.2.2⟩) h⟩

theorem SeitzExcAnisotropicForAt.mono {P : TauCeti.LieTypeIndex → Prop}
    {Q Q' : TauCeti.LieTypeIndex → ℕ → Prop} (h : ∀ d p, Q' d p → Q d p)
    (hP : SeitzExcAnisotropicForAt P Q) : SeitzExcAnisotropicForAt P Q' :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, h _ _ hE.2.2.1, hE.2.2.2⟩) hP

theorem SeitzExcAnisotropicForAt.mono_index {P P' : TauCeti.LieTypeIndex → Prop}
    {Q : TauCeti.LieTypeIndex → ℕ → Prop} (h : ∀ d, P' d → P d)
    (hP : SeitzExcAnisotropicForAt P Q) : SeitzExcAnisotropicForAt P' Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, h _ hE.2.1, hE.2.2⟩) hP

theorem SeitzExcAnisotropicForAt.union {P : TauCeti.LieTypeIndex → Prop}
    {Q Q₁ Q₂ : TauCeti.LieTypeIndex → ℕ → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → Q d p → Q₁ d p ∨ Q₂ d p)
    (h₁ : SeitzExcAnisotropicForAt P Q₁) (h₂ : SeitzExcAnisotropicForAt P Q₂) :
    SeitzExcAnisotropicForAt P Q :=
  SeitzPlanes.of_cover (fun d p hp hp2 _ hE => by
    obtain ⟨hi, hP, hQ, hr, hn⟩ := hE
    exact (hcov d.1 p hp hp2 hQ).imp (fun h => ⟨hi, hP, h, hr, hn⟩)
      (fun h => ⟨hi, hP, h, hr, hn⟩)) h₁ h₂

theorem SeitzExcAnisotropicFor.of_three_geFive {P : TauCeti.LieTypeIndex → Prop}
    (h₃ : SeitzExcAnisotropicForAt P PrimeRange.three)
    (h₅ : SeitzExcAnisotropicForAt P PrimeRange.geFive) : SeitzExcAnisotropicFor P :=
  seitzExcAnisotropicFor_iff_at.mpr
    (SeitzExcAnisotropicForAt.union
      (fun _ _ hp hp2 _ => PrimeRange.eq_three_or_five_le hp hp2) h₃ h₅)

@[expose] def SeitzExcOuterNarrowForAt (P : TauCeti.LieTypeIndex → Prop)
    (Q : TauCeti.LieTypeIndex → ℕ → Prop) : Prop :=
  SeitzPlanes fun d p E => ¬ InnerPlane d p E ∧ NarrowScope p E ∧ P d.1 ∧ Q d.1 p

theorem SeitzExcOuterNarrowFor.toAt {P : TauCeti.LieTypeIndex → Prop}
    (h : SeitzExcOuterNarrowFor P) (Q : TauCeti.LieTypeIndex → ℕ → Prop) :
    SeitzExcOuterNarrowForAt P Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, hE.2.2.1⟩) h

theorem seitzExcOuterNarrowFor_iff_at {P : TauCeti.LieTypeIndex → Prop} :
    SeitzExcOuterNarrowFor P ↔ SeitzExcOuterNarrowForAt P PrimeRange.all :=
  ⟨fun h => h.toAt _, fun h =>
    SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, hE.2.2, trivial⟩) h⟩

theorem SeitzExcOuterNarrowForAt.mono {P : TauCeti.LieTypeIndex → Prop}
    {Q Q' : TauCeti.LieTypeIndex → ℕ → Prop} (h : ∀ d p, Q' d p → Q d p)
    (hP : SeitzExcOuterNarrowForAt P Q) : SeitzExcOuterNarrowForAt P Q' :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, hE.2.2.1, h _ _ hE.2.2.2⟩) hP

theorem SeitzExcOuterNarrowForAt.mono_index {P P' : TauCeti.LieTypeIndex → Prop}
    {Q : TauCeti.LieTypeIndex → ℕ → Prop} (h : ∀ d, P' d → P d)
    (hP : SeitzExcOuterNarrowForAt P Q) : SeitzExcOuterNarrowForAt P' Q :=
  SeitzPlanes.mono (fun _ _ _ hE => ⟨hE.1, hE.2.1, h _ hE.2.2.1, hE.2.2.2⟩) hP

theorem SeitzExcOuterNarrowForAt.union {P : TauCeti.LieTypeIndex → Prop}
    {Q Q₁ Q₂ : TauCeti.LieTypeIndex → ℕ → Prop}
    (hcov : ∀ d p, p.Prime → p ≠ 2 → Q d p → Q₁ d p ∨ Q₂ d p)
    (h₁ : SeitzExcOuterNarrowForAt P Q₁) (h₂ : SeitzExcOuterNarrowForAt P Q₂) :
    SeitzExcOuterNarrowForAt P Q :=
  SeitzPlanes.of_cover (fun d p hp hp2 _ hE => by
    obtain ⟨hi, hs, hP, hQ⟩ := hE
    exact (hcov d.1 p hp hp2 hQ).imp (fun h => ⟨hi, hs, hP, h⟩)
      (fun h => ⟨hi, hs, hP, h⟩)) h₁ h₂

theorem SeitzExcOuterNarrowFor.of_three_geFive {P : TauCeti.LieTypeIndex → Prop}
    (h₃ : SeitzExcOuterNarrowForAt P PrimeRange.three)
    (h₅ : SeitzExcOuterNarrowForAt P PrimeRange.geFive) : SeitzExcOuterNarrowFor P :=
  seitzExcOuterNarrowFor_iff_at.mpr
    (SeitzExcOuterNarrowForAt.union
      (fun _ _ hp hp2 _ => PrimeRange.eq_three_or_five_le hp hp2) h₃ h₅)

end CFSG.LieType.SeitzGeneration
