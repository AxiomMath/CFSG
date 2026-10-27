module

public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGen
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CZDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenDefs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.AGL81TheoremCD

variable {G : Type} [Group G] [Finite G]

abbrev threeStar (J : Subgroup G) : Type := ↥J ⧸ CFSG.pPrimeCore 3 ↥J

@[expose]
def H2StarAll (M : Subgroup G) : Set (Subgroup G) :=
  {H | ∃ p : ℕ, ∃ Q ∈ QSet M p, H ∈ H2StarFam M Q}

@[expose]
def IsKComp (M H J : Subgroup G) : Prop := IsPComponentIn 3 J (kSub 3 M H)

@[expose]
def IsSL34Star (J : Subgroup G) : Prop :=
  IsL34Type (threeStar J) ∧ Nat.card (Subgroup.center (threeStar J)) = 3

@[expose]
def IsL34Star (J : Subgroup G) : Prop :=
  IsL34Type (threeStar J) ∧ Nat.card (Subgroup.center (threeStar J)) = 1

@[expose]
def IsA11Star (J : Subgroup G) : Prop := IsA11Type (threeStar J)

@[expose]
def Is3A6Star (J : Subgroup G) : Prop :=
  IsA6Type (threeStar J) ∧ Nat.card (Subgroup.center (threeStar J)) = 3

@[expose]
def calK (M Q : Subgroup G) : Set (Subgroup G) :=
  {J | ∃ H ∈ H2StarFam M Q, IsKComp M H J ∧ (IsL34Type (threeStar J) ∨ IsA11Star J)}

@[expose]
def calKStar (M Q : Subgroup G) : Set (Subgroup G) :=
  {J | J ∈ calK M Q ∧ ∀ J' ∈ calK M Q, J ≤ J' → J' = J}

@[expose]
def TypeA (M H : Subgroup G) : Prop := ∃ J, IsKComp M H J ∧ IsSL34Star J

@[expose]
def TypeB (M H : Subgroup G) : Prop := ∃ J, IsKComp M H J ∧ IsA11Star J

@[expose]
def CaseThree (M H : Subgroup G) : Prop :=
  IsKComp M H (kSub 3 M H) ∧ IsL34Star (kSub 3 M H)

@[expose]
def FiveTypes (M H : Subgroup G) : Prop :=
  (IsKComp M H (kSub 3 M H) ∧ (IsL34Star (kSub 3 M H) ∨ IsSL34Star (kSub 3 M H) ∨
     IsA11Star (kSub 3 M H))) ∨
  ∃ J₁ J₂ : Subgroup G, J₁ ≠ J₂ ∧ IsKComp M H J₁ ∧ IsKComp M H J₂ ∧
    kSub 3 M H = J₁ ⊔ J₂ ∧ (∀ J, IsKComp M H J → J = J₁ ∨ J = J₂) ∧
    IsSL34Star J₁ ∧ (IsSL34Star J₂ ∨ Is3A6Star J₂)

structure S14Choice (G : Type) [Group G] [Finite G] (M H E Q J : Subgroup G) : Prop where
  cstar : CStarGen G
  maxLocal : rankThreeIsMaxTwoLocal M
  sigma_nonempty : (sigmaSet G M).Nonempty
  mem : H ∈ H2StarAll M
  E_le_H : E ≤ H
  elem : IsElemAbelian 3 E
  card : Nat.card E = 9
  gamma : rankThreeGamma 1 3 E ≤ M
  E_le_Q : E ≤ Q
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 Q (kSub 3 M H ⊔ E)
  J_comp : IsTwoPrimeComponentIn J (kSub 3 M H)
  J_star : J ∈ calKStar M Q
  prefA : (∃ H' ∈ H2StarAll M, TypeA M H') → TypeA M H
  prefB : (¬ ∃ H' ∈ H2StarAll M, TypeA M H') → (∃ H' ∈ H2StarAll M, TypeB M H') →
    TypeB M H

@[expose]
def PreambleTypes (M : Subgroup G) : Prop :=
  ∀ (p : ℕ) (Q : Subgroup G), Q ∈ QSet M p → ∀ H ∈ H2StarFam M Q, p = 3 ∧ FiveTypes M H

@[expose]
def ChoiceExists (M : Subgroup G) : Prop :=
  (H2StarAll M).Nonempty → ∃ H E Q J : Subgroup G, S14Choice G M H E Q J

@[expose]
def CaseOneFalse (M : Subgroup G) : Prop :=
  ∀ H E Q J : Subgroup G, S14Choice G M H E Q J → ¬ TypeA M H

@[expose]
def CaseTwoFalse (M : Subgroup G) : Prop :=
  ∀ H E Q J : Subgroup G, S14Choice G M H E Q J → ¬ TypeA M H → ¬ TypeB M H

theorem FiveTypes.caseThree {M H : Subgroup G} (h : FiveTypes M H) (hA : ¬ TypeA M H)
    (hB : ¬ TypeB M H) : CaseThree M H := by
  unfold CaseThree
  unfold FiveTypes at h
  have hA' : ¬ ∃ J : Subgroup G, IsKComp M H J ∧ IsSL34Star J := by
    simpa only [TypeA] using hA
  have hB' : ¬ ∃ J : Subgroup G, IsKComp M H J ∧ IsA11Star J := by
    simpa only [TypeB] using hB
  rcases h with hFirst | hSecond
  · rcases hFirst with ⟨hcomp, hL | hSL | hA11⟩
    · exact ⟨hcomp, hL⟩
    · exact absurd ⟨kSub 3 M H, hcomp, hSL⟩ hA'
    · exact absurd ⟨kSub 3 M H, hcomp, hA11⟩ hB'
  · obtain ⟨J₁, -, -, hJ₁, -, -, -, hSL₁, -⟩ := hSecond
    exact absurd ⟨J₁, hJ₁, hSL₁⟩ hA'

theorem caseThree_of_cases {M : Subgroup G} (hpre : PreambleTypes M) (hch : ChoiceExists M)
    (h1 : CaseOneFalse M) (h2 : CaseTwoFalse M) : ∀ H ∈ H2StarAll M, CaseThree M H := by
  unfold PreambleTypes at hpre
  unfold ChoiceExists at hch
  unfold CaseOneFalse at h1
  unfold CaseTwoFalse at h2
  intro H hH
  have hHmem : H ∈ H2StarAll M := hH
  obtain ⟨H₀, E, Q₀, J, hchoice⟩ := hch ⟨H, hH⟩
  have hnoA : ¬ ∃ H' ∈ H2StarAll M, TypeA M H' := by
    rintro ⟨H', hH', hAt⟩
    exact h1 H₀ E Q₀ J hchoice (hchoice.prefA ⟨H', hH', hAt⟩)
  have hnoB : ¬ ∃ H' ∈ H2StarAll M, TypeB M H' := by
    rintro ⟨H', hH', hBt⟩
    exact h2 H₀ E Q₀ J hchoice (fun hAt => hnoA ⟨H₀, hchoice.mem, hAt⟩)
      (hchoice.prefB hnoA ⟨H', hH', hBt⟩)
  unfold H2StarAll at hH
  obtain ⟨p, Q, hQ, hHfam⟩ := hH
  exact FiveTypes.caseThree (hpre p Q hQ H hHfam).2
    (fun hAt => hnoA ⟨H, hHmem, hAt⟩) (fun hBt => hnoB ⟨H, hHmem, hBt⟩)

theorem eq_three_of_mem {M : Subgroup G} (hpre : PreambleTypes M) {p : ℕ} {Q H : Subgroup G}
    (hQ : Q ∈ QSet M p) (hH : H ∈ H2StarFam M Q) : p = 3 := by
  unfold PreambleTypes at hpre
  exact (hpre p Q hQ H hH).1

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
