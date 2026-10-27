module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator

variable {G : Type} [Group G]

theorem layer_eq_lambdaOf_sup_phiOf (p : ℕ) (B : Subgroup G) (b : G) :
    GLAPLayer p (Subgroup.centralizer ({b} : Set G)) = lambdaOf p B b ⊔ phiOf p B b := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    by_cases h : IsStronglyLocallyOneBalanced p B b L
    · exact le_sup_of_le_right (le_sSup ⟨hL, h⟩)
    · exact le_sup_of_le_left (le_sSup ⟨hL, h⟩)
  · exact sup_le (sSup_le_sSup fun L hL => hL.1) (sSup_le_sSup fun L hL => hL.1)

@[expose] def Lemma31 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ), GLStanding G m p →
    ∀ B : Subgroup G, GLAIsBmax p B → IsSCp p ⊤ B → ∀ b ∈ B, b ≠ 1 →
      ∀ L : Subgroup G, GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L →
        IsStronglyLocallyOneBalanced p B b L ∨ IsInGOne p B L ∨ Lemma31iii p B L ∨
          Lemma31iv p B L ∨ Lemma31v p L

variable [Finite G]

theorem psiOf_le_lambdaOf (p : ℕ) (B : Subgroup G) (b : G) : psiOf p B b ≤ lambdaOf p B b :=
  sSup_le_sSup fun _ hL => ⟨hL.1, hL.2.1⟩

theorem lambdaLOf_le_lambdaOf (p : ℕ) (B : Subgroup G) (b : G) :
    lambdaLOf p B b ≤ lambdaOf p B b :=
  sSup_le_sSup fun _ hL => ⟨hL.1, hL.2.1⟩

theorem lambdaONOf_le_lambdaOf (p : ℕ) (B : Subgroup G) (b : G) :
    lambdaONOf p B b ≤ lambdaOf p B b :=
  sSup_le_sSup fun _ hL => ⟨hL.1, hL.2.1⟩

theorem lambdaMOf_le_lambdaOf (p : ℕ) (B : Subgroup G) (b : G) :
    lambdaMOf p B b ≤ lambdaOf p B b :=
  sSup_le_sSup fun _ hL => ⟨hL.1, hL.2.1⟩

theorem lambdaOf_eq_of_lemma31 (h31 : Lemma31) {m p : ℕ} (hS : GLStanding G m p)
    {B : Subgroup G} (hB : GLAIsBmax p B) (hsc : IsSCp p ⊤ B) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    lambdaOf p B b = psiOf p B b ⊔ lambdaLOf p B b ⊔ lambdaONOf p B b ⊔ lambdaMOf p B b := by
  apply le_antisymm
  · refine sSup_le fun L hL => ?_
    rcases h31 G m p hS B hB hsc b hb hb1 L hL.1 with h | h | h | h | h
    · exact absurd h hL.2
    · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left
        (le_sSup ⟨hL.1, hL.2, h⟩)))
    · exact le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_right
        (le_sSup ⟨hL.1, hL.2, h⟩)))
    · exact le_sup_of_le_left (le_sup_of_le_right (le_sSup ⟨hL.1, hL.2, h⟩))
    · exact le_sup_of_le_right (le_sSup ⟨hL.1, hL.2, h⟩)
  · exact sup_le (sup_le (sup_le (psiOf_le_lambdaOf p B b) (lambdaLOf_le_lambdaOf p B b))
      (lambdaONOf_le_lambdaOf p B b)) (lambdaMOf_le_lambdaOf p B b)

theorem lambdaLOf_eq_bot_of_ne_three {p : ℕ} (hp : p ≠ 3) (B : Subgroup G) (b : G) :
    lambdaLOf p B b = ⊥ := by
  refine le_bot_iff.1 (sSup_le fun L hL => ?_)
  exact absurd hL.2.2.1 hp

theorem lambdaONOf_eq_bot_of_ne_three {p : ℕ} (hp : p ≠ 3) (B : Subgroup G) (b : G) :
    lambdaONOf p B b = ⊥ := by
  refine le_bot_iff.1 (sSup_le fun L hL => ?_)
  exact absurd hL.2.2.1 hp

theorem lambdaMOf_eq_bot_of_ne_five {p : ℕ} (hp : p ≠ 5) (B : Subgroup G) (b : G) :
    lambdaMOf p B b = ⊥ := by
  refine le_bot_iff.1 (sSup_le fun L hL => ?_)
  exact absurd hL.2.2.1 hp

theorem lambdaOf_eq_psiOf_of_five_lt (h31 : Lemma31) {m p : ℕ} (hS : GLStanding G m p)
    (hp5 : 5 < p) {B : Subgroup G} (hB : GLAIsBmax p B) (hsc : IsSCp p ⊤ B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) : lambdaOf p B b = psiOf p B b := by
  rw [lambdaOf_eq_of_lemma31 h31 hS hB hsc hb hb1, lambdaLOf_eq_bot_of_ne_three (by omega),
    lambdaONOf_eq_bot_of_ne_three (by omega), lambdaMOf_eq_bot_of_ne_five (by omega)]
  simp

theorem lambdaOf_eq_psiOf_sup_lambdaMOf_of_five (h31 : Lemma31) {m : ℕ}
    (hS : GLStanding G m 5) {B : Subgroup G} (hB : GLAIsBmax 5 B) (hsc : IsSCp 5 ⊤ B) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) : lambdaOf 5 B b = psiOf 5 B b ⊔ lambdaMOf 5 B b := by
  rw [lambdaOf_eq_of_lemma31 h31 hS hB hsc hb hb1, lambdaLOf_eq_bot_of_ne_three (by omega),
    lambdaONOf_eq_bot_of_ne_three (by omega)]
  simp

theorem lambdaStarGroup_eq_psiStarGroup_of_forall {p : ℕ} {B : Subgroup G}
    (h : ∀ b ∈ B, b ≠ 1 → lambdaOf p B b = psiOf p B b) :
    lambdaStarGroup p B = psiStarGroup p B := by
  unfold lambdaStarGroup psiStarGroup
  refine iSup_congr fun b => iSup_congr fun hb => iSup_congr fun hb1 => ?_
  unfold lambdaStar psiStar
  rw [h b hb hb1]

theorem lambdaStarGroup_eq_psiStarGroup_of_five_lt (h31 : Lemma31) {m p : ℕ}
    (hS : GLStanding G m p) (hp5 : 5 < p) {B : Subgroup G} (hB : GLAIsBmax p B)
    (hsc : IsSCp p ⊤ B) : lambdaStarGroup p B = psiStarGroup p B :=
  lambdaStarGroup_eq_psiStarGroup_of_forall fun _ hb hb1 =>
    lambdaOf_eq_psiOf_of_five_lt h31 hS hp5 hB hsc hb hb1

end CFSG.HardMathSupport.Solomon.LocalBalance
