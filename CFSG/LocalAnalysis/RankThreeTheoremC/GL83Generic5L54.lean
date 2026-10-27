module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Ctx
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5CaseNInst
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5L52
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5Setup2
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5KFacts
public import CFSG.LocalAnalysis.RankThreeTheoremC.K1NoBMDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactSections3

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools CFSG.AGLEmbedding Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}

theorem gen5_normalizer_ne_top (hG : Gen5Global G) (hl : Gen5Local G p P M x) {Y : Subgroup G}
    (hY1 : Y ≠ ⊥) (hYZ : Y ≤ centralizer ((gen5L x : Subgroup G) : Set G)) :
    normalizer (Y : Set G) ≠ ⊤ ∧ gen5L x ≤ normalizer (Y : Set G) := by
  refine ⟨fun htop => ?_, (le_centralizer_iff.mp hYZ).trans (centralizer_le_normalizer _)⟩
  have : Y.Normal := normalizer_eq_top_iff.mp htop
  rcases hG.setting.simple.eq_bot_or_eq_top_of_normal Y with h | h
  · exact hY1 h
  · exact gen5_not_le hG hl fun l _ => gen5_Z_le hG hl (hYZ (h ▸ mem_top l))

theorem gen5_L54 (hG : Gen5Global G) (K1 : StronglyEmbeddedRankTwoKFactNoBM)
    (Sch : KFactCatalogSchreier) (hK : GL83Generic5KFacts) (hExcl : NoExcludedSection3 G)
    (hl : Gen5Local G p P M x) {Y : Subgroup G} (hY1 : Y ≠ ⊥)
    (hYZ : Y ≤ centralizer ((gen5L x : Subgroup G) : Set G))
    (hcase : IsSylowOf p (gen5U (P : Subgroup G) x) (normalizer (Y : Set G)) ∨
      x ∈ normalizer (Y : Set G))
    {W : Subgroup G} (hWp : Nat.Coprime p (Nat.card W)) (hWN : W ≤ normalizer (Y : Set G))
    (hUW : gen5U (P : Subgroup G) x ≤ normalizer (W : Set G)) :
    W ≤ centralizer ((gen5L x : Subgroup G) : Set G) := by
  have : Fact p.Prime := ⟨gen5_prime hl⟩
  obtain ⟨hNtop, hLN⟩ := gen5_normalizer_ne_top hG hl hY1 hYZ
  obtain ⟨-, hNO, hOcop⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p (normalizer (Y : Set G))
  rcases hcase with hSyl | hxN
  · exact (gen5_caseI_N hG K1 Sch hK.signalizer hExcl hl hNtop hLN hSyl hWp hWN hUW).trans
      (gen5_L52 hG hl hOcop (hLN.trans hNO)).1
  · have hcomm := gen5_caseII_N hG Sch hK hl hNtop hLN hxN hWp hWN hUW
    set X := rankThreePrimeCore p (normalizer (Y : Set G)) ⊔ W
    have hXcop : Nat.Coprime p (Nat.card X) :=
      CFSG.LocalAnalysis.RankThreeUC.coprime_card_sup_of_le_normalizer (hWN.trans hNO) hOcop hWp
    have hLX : gen5L x ≤ normalizer (X : Set G) := by
      refine le_normalizer_iff.mpr fun l hl k hk => ?_
      refine (show X ≤ X.comap (MulAut.conj l).toMonoidHom from
        sup_le (fun o ho => ?_) fun w hw => ?_) hk
      · exact mem_sup_left (le_normalizer_iff.mp (hLN.trans hNO) l hl o ho)
      · have heq : l * w * l⁻¹ = w * (w⁻¹ * (l⁻¹⁻¹ * w * l⁻¹)) := by group
        change l * w * l⁻¹ ∈ X
        rw [heq]
        exact X.mul_mem (mem_sup_right hw) (mem_sup_left (hcomm w hw l⁻¹ (inv_mem hl)))
    exact le_sup_right.trans (gen5_L52 hG hl hXcop hLX).1

end CFSG.LocalAnalysis.RankThreeTheoremC
