module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CaseInst
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.L52

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem fr_normalizer_ne_top [Fact p.Prime] (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {Y₀ : Subgroup G} (hY1 : Y₀ ≠ ⊥) (hYZ : Y₀ ≤ centralizer ((layerOf x : Subgroup G) : Set G)) :
    normalizer (Y₀ : Set G) ≠ ⊤ ∧ layerOf x ≤ normalizer (Y₀ : Set G) := by
  refine ⟨fun htop => ?_, (le_centralizer_iff.mp hYZ).trans (centralizer_le_normalizer _)⟩
  have : Y₀.Normal := normalizer_eq_top_iff.mp htop
  rcases hG.simple.eq_bot_or_eq_top_of_normal Y₀ with h | h
  · exact hY1 h
  · exact hl.not_le fun l _ => fr_centralizer_layer_le hG hl (hYZ (h ▸ mem_top l))

theorem fr_L54_N [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {N : Subgroup G} (hNtop : N ≠ ⊤) (hLN : layerOf x ≤ N)
    (hcase : IsSylowOf p (frU P x) N ∨ x ∈ N)
    {W : Subgroup G} (hWp : Nat.Coprime p (Nat.card W)) (hWN : W ≤ N)
    (hUW : frU P x ≤ normalizer (W : Set G)) :
    W ≤ centralizer ((layerOf x : Subgroup G) : Set G) := by
  obtain ⟨-, hNO, hOcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p N
  rcases hcase with hSyl | hxN
  · exact (fr_caseI_N hK hG hl hNtop hLN hSyl hWp hWN hUW).trans
      (fr_L52 hG hl hOcop (hLN.trans hNO)).1
  · have hcomm := fr_caseII_N hK hG hl hNtop hLN hxN hWp hWN hUW
    set X := CFSG.Open.GLBPrimeCore p N ⊔ W
    have hXcop : Nat.Coprime p (Nat.card X) :=
      CFSG.LocalAnalysis.RankThreeUC.coprime_card_sup_of_le_normalizer (hWN.trans hNO) hOcop hWp
    have hLX : layerOf x ≤ normalizer (X : Set G) := by
      refine le_normalizer_iff.mpr fun l hl' k hk => ?_
      refine (show X ≤ X.comap (MulAut.conj l).toMonoidHom from
        sup_le (fun o ho => ?_) fun w hw => ?_) hk
      · exact mem_sup_left (le_normalizer_iff.mp (hLN.trans hNO) l hl' o ho)
      · have heq : l * w * l⁻¹ = w * (w⁻¹ * (l⁻¹⁻¹ * w * l⁻¹)) := by group
        change l * w * l⁻¹ ∈ X
        rw [heq]
        exact X.mul_mem (mem_sup_right hw) (mem_sup_left (hcomm w hw l⁻¹ (inv_mem hl')))
    exact le_sup_right.trans (fr_L52 hG hl hXcop hLX).1

theorem fr_L54 [Fact p.Prime] (hK : FrobKFacts) (hG : FrobGlobal G) (hl : FrobLocal p P M x)
    {Y₀ : Subgroup G} (hY1 : Y₀ ≠ ⊥) (hYZ : Y₀ ≤ centralizer ((layerOf x : Subgroup G) : Set G))
    (hcase : IsSylowOf p (frU P x) (normalizer (Y₀ : Set G)) ∨ x ∈ normalizer (Y₀ : Set G))
    {W : Subgroup G} (hWp : Nat.Coprime p (Nat.card W)) (hWN : W ≤ normalizer (Y₀ : Set G))
    (hUW : frU P x ≤ normalizer (W : Set G)) :
    W ≤ centralizer ((layerOf x : Subgroup G) : Set G) := by
  obtain ⟨hNtop, hLN⟩ := fr_normalizer_ne_top hG hl hY1 hYZ
  exact fr_L54_N hK hG hl hNtop hLN hcase hWp hWN hUW

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
