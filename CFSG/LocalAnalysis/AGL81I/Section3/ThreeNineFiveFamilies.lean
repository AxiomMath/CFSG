module

public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineCatFiveMain
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineGamma

public section

namespace CFSG.LocalAnalysis.AGL81I.Section3

open CFSG.Open
open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPSLType)
open CFSG.LocalAnalysis.AGL81TheoremCD.Section12
  (gammaIn gammaOver oPrimeModPrimeComplement ThreeNine)

structure ThreeNineHyp {X : Type} [Group X] [Finite X] (K E D X₁ : Subgroup X) (p d : ℕ) :
    Prop where
  prime : p.Prime
  ne_two : p ≠ 2
  quasisimple : CFSG.IsQuasisimple ↥K
  core : CFSG.pPrimeCore p ↥K = ⊥
  kgroup : CFSG.SectionRank.IsKGroupCat ↥K
  normal : K.Normal
  one_lt_rank : 1 < CFSG.Open.pRank p (⊤ : Subgroup X)
  rank_le : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3
  elem : CFSG.Open.IsElemAbelian p E
  card_E : Nat.card E = p ^ 2
  d_prime : d.Prime
  d_ne_two : d ≠ 2
  d_ne : d ≠ p
  sylow : CFSG.ABGLocalTools.IsSylowOf d D ⊤
  D_ne_bot : D ≠ ⊥
  lt : X₁ < K ⊔ D
  gammaE : gammaOver 1 p E (K ⊔ D) ≤ X₁
  gammaD : gammaIn 1 d D (K ⊔ D) ≤ X₁
  normQ : ∀ Q : Subgroup X, IsPGroup p Q → E ≤ Q →
    Subgroup.normalizer (Q : Set X) ⊓ (K ⊔ D) ≤ X₁

abbrev ThreeNineConclusion {X : Type} [Group X] [Finite X] (K D X₁ : Subgroup X) (p d : ℕ) :
    Prop :=
  IsCyclic ↥D ∧ D ≤ K ∧
    ((p = 3 ∧ d = 13 ∧ ReeTitsModel ↥K .Tits 2 1 ∧
        IsPSLType 3 (ZMod 3) (oPrimeModPrimeComplement d X₁)) ∨
      (p = 5 ∧ d = 7 ∧ IsSporadic ↥K .HS ∧
        StatedClassicalModel (oPrimeModPrimeComplement d X₁) .PSU 3 5 1) ∨
      (p = 5 ∧ d = 7 ∧ IsSporadic ↥K .Fi22 ∧
        StatedClassicalModel (oPrimeModPrimeComplement d X₁) .POmegaPlus 4 2 1) ∨
      (p = 5 ∧ d = 31 ∧ IsSporadic ↥K .Ly ∧
        ChevalleyExceptionalModel (oPrimeModPrimeComplement d X₁) .G2 5 1) ∨
      (p = 7 ∧ d = 19 ∧ IsSporadic ↥K .ONan ∧
        IsPSLType 3 (ZMod 7) (oPrimeModPrimeComplement d X₁)) ∨
      (p = 7 ∧ d = 17 ∧ IsSporadic ↥K .Fi24Prime ∧
        IsSporadic (oPrimeModPrimeComplement d X₁) .He) ∨
      (d ∣ p + 1 ∧ IsPSLType 3 (ZMod p) ↥K ∧
        IsPSLType 2 (ZMod p) (oPrimeModPrimeComplement d X₁)))

theorem threeNine_of_hyp
    (h : ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (p d : ℕ),
      ThreeNineHyp K E D X₁ p d → ThreeNineConclusion K D X₁ p d) : ThreeNine :=
  fun X _ _ K E D X₁ p d hp hp2 hKq hOp hKcat hKn h1 h3 hE hEc hd hd2 hdp hD hD1 hX1 hΓE hΓD
    hN => h X K E D X₁ p d ⟨hp, hp2, hKq, hOp, hKcat, hKn, h1, h3, hE, hEc, hd, hd2, hdp, hD, hD1,
      hX1, hΓE, hΓD, hN⟩

@[expose] def ThreeNineFiveSz : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 5 d → SuzukiModel ↥K 2 5 → False

@[expose] def ThreeNineFiveDef : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (p d : ℕ),
    ThreeNineHyp K E D X₁ p d → 5 ≤ p →
    (StatedClassicalModel ↥K .PSL 2 p 2 ∨ StatedClassicalModel ↥K .PSL 2 p 3 ∨
      IsPSLType 3 (ZMod p) ↥K ∨ StatedClassicalModel ↥K .PSU 3 p 1 ∨
      StatedClassicalModel ↥K .PSp 2 p 1 ∨ ChevalleyExceptionalModel ↥K .G2 p 1) →
    ThreeNineConclusion K D X₁ p d

@[expose] def ThreeNineFiveAlt : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (p d : ℕ),
    ThreeNineHyp K E D X₁ p d → 5 ≤ p →
    (Nonempty (↥K ≃* alternatingGroup (Fin (2 * p))) ∨
      Nonempty (↥K ≃* alternatingGroup (Fin (3 * p)))) → False

@[expose] def ThreeNineFiveTits : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 5 d → ReeTitsModel ↥K .Tits 2 1 → False

@[expose] def SporadicExtra24_14 (p : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (p = 5 ∧ (s = .McL ∨ s = .HS ∨ s = .Co2 ∨ s = .Co3 ∨ s = .Ru)) ∨
    (p = 7 ∧ (s = .He ∨ s = .ONan ∨ s = .Fi24Prime)) ∨ (p = 11 ∧ s = .J4)

@[expose] def ThreeNineFiveSporExtra : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (p d : ℕ)
    (s : TauCeti.SporadicName), ThreeNineHyp K E D X₁ p d → SporadicExtra24_14 p s →
    IsSporadic ↥K s → ThreeNineConclusion K D X₁ p d

@[expose] def ThreeNineFiveFi22 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (d : ℕ),
    ThreeNineHyp K E D X₁ 5 d → IsSporadic ↥K .Fi22 → ThreeNineConclusion K D X₁ 5 d

@[expose] def SporadicBig24_14 (p : ℕ) (s : TauCeti.SporadicName) : Prop :=
  (p = 5 ∧ (s = .Co1 ∨ s = .Ly ∨ s = .B ∨ s = .HN)) ∨ (p = 7 ∧ s = .M)

@[expose] def ThreeNineFiveSporBig : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (K E D X₁ : Subgroup X) (p d : ℕ)
    (s : TauCeti.SporadicName), ThreeNineHyp K E D X₁ p d → SporadicBig24_14 p s →
    IsSporadic ↥K s → ThreeNineConclusion K D X₁ p d

theorem four_le_pRank_of_isPSLType_four {K : Type} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h : IsPSLType 4 (ZMod p) K) :
    4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  obtain ⟨e⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have hm : StatedClassicalModel K .PSL 4 p 1 :=
    ⟨⟨hp, le_rfl, by norm_num, by simp, by simp⟩, ZMod p, inferInstance, inferInstance,
      by rw [Nat.card_zmod, pow_one],
      ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 4 (ZMod p))⟩⟩
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hm
  rcases hcases with ⟨-, ⟨h, -⟩ | ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
  all_goals first | omega | cases h

theorem four_le_pRank_of_psu_four {K : Type} [Group K] [Finite K] {p : ℕ} (hp2 : p ≠ 2)
    (h : StatedClassicalModel K .PSU 4 p 1) : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup K) := by
  obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 h
  rcases hcases with ⟨h, -⟩ | ⟨-, ⟨h, -⟩ | h⟩ | ⟨h, -⟩ | h
  all_goals first | omega | cases h

theorem threeNineFive_of_members (hCat : Catalogue24_12Five) (hSz : ThreeNineFiveSz)
    (hDef : ThreeNineFiveDef) (hAlt : ThreeNineFiveAlt) (hTits : ThreeNineFiveTits)
    (hExtra : ThreeNineFiveSporExtra) (hFi : ThreeNineFiveFi22) (hBig : ThreeNineFiveSporBig)
    {X : Type} [Group X] [Finite X] {K E D X₁ : Subgroup X} {p d : ℕ}
    (h : ThreeNineHyp K E D X₁ p d) (hp5 : 5 ≤ p) : ThreeNineConclusion K D X₁ p d := by
  have hΓ := threeNine_not_le_gammaOver K E D X₁ p d h.prime h.d_prime h.sylow h.D_ne_bot h.lt
    h.gammaE h.gammaD
  have hrk : CFSG.Open.pRank p (K ⊔ E) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono h.prime.one_lt (le_top : K ⊔ E ≤ ⊤)).trans h.rank_le
  have hrkK : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 3 := pRank_top_le_three_of_sup h.prime hrk
  obtain ⟨-, -, -, -, hK⟩ := hCat X K E p h.prime hp5 h.quasisimple h.core h.kgroup h.normal
    h.elem h.card_E hrk hΓ
  rcases hK with (hK | hK | hK | hK | hK | hK | hK | hK | hK) | ⟨-, hK⟩ | ⟨h3, -⟩ |
      ⟨rfl, hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK | hK⟩ |
      ⟨rfl, hK | hK | hK | hK⟩ | ⟨rfl, hK⟩
  · exact (hAlt X K E D X₁ p d h hp5 (Or.inl hK)).elim
  · exact (hAlt X K E D X₁ p d h hp5 (Or.inr hK)).elim
  · exact hDef X K E D X₁ p d h hp5 (Or.inl hK)
  · exact hDef X K E D X₁ p d h hp5 (Or.inr (Or.inl hK))
  · exact hDef X K E D X₁ p d h hp5 (Or.inr (Or.inr (Or.inl hK)))
  · exact hDef X K E D X₁ p d h hp5 (Or.inr (Or.inr (Or.inr (Or.inl hK))))
  · exact absurd (four_le_pRank_of_isPSLType_four h.prime h.ne_two hK) (by omega)
  · exact absurd (four_le_pRank_of_psu_four h.ne_two hK) (by omega)
  · exact hDef X K E D X₁ p d h hp5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hK)))))
  · exact hDef X K E D X₁ p d h hp5 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hK)))))
  · omega
  · exact (hSz X K E D X₁ d h hK).elim
  · exact (hTits X K E D X₁ d h hK).elim
  · exact hExtra X K E D X₁ 5 d _ h (by simp [SporadicExtra24_14]) hK
  · exact hExtra X K E D X₁ 5 d _ h (by simp [SporadicExtra24_14]) hK
  · exact hFi X K E D X₁ d h hK
  · exact hBig X K E D X₁ 5 d _ h (by simp [SporadicBig24_14]) hK
  · exact hExtra X K E D X₁ 5 d _ h (by simp [SporadicExtra24_14]) hK
  · exact hExtra X K E D X₁ 5 d _ h (by simp [SporadicExtra24_14]) hK
  · exact hBig X K E D X₁ 5 d _ h (by simp [SporadicBig24_14]) hK
  · exact hExtra X K E D X₁ 5 d _ h (by simp [SporadicExtra24_14]) hK
  · exact hBig X K E D X₁ 5 d _ h (by simp [SporadicBig24_14]) hK
  · exact hBig X K E D X₁ 5 d _ h (by simp [SporadicBig24_14]) hK
  · exact hExtra X K E D X₁ 7 d _ h (by simp [SporadicExtra24_14]) hK
  · exact hExtra X K E D X₁ 7 d _ h (by simp [SporadicExtra24_14]) hK
  · exact hExtra X K E D X₁ 7 d _ h (by simp [SporadicExtra24_14]) hK
  · exact hBig X K E D X₁ 7 d _ h (by simp [SporadicBig24_14]) hK
  · exact hExtra X K E D X₁ 11 d _ h (by simp [SporadicExtra24_14]) hK

end CFSG.LocalAnalysis.AGL81I.Section3
