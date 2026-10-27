module

public import CFSG.LocalAnalysis.RankThreeTheoremC.FullCoreReduction
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.SignalizerCore
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionCentre
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def SignalizerCase (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    (P : Subgroup G) ≤ normalizer (D : Set G) →
    ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
      (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) → K ≤ M

@[expose] def TransitivityCase (G : Type) [Group G] [Finite G] : Prop :=
  ∀ p ∈ rankThreeSigmaA G, ∀ (P : Sylow p G) (M D : Subgroup G), ExtremalObstruction p P M D →
    ¬ (P : Subgroup G) ≤ normalizer (D : Set G) →
    centralizer (D : Set G) ≤ M ∧
      ∃ T : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D T ∧ normalizer (T : Set G) ≤ M ∧
        ∀ T' : Subgroup G, rankTwoMaximalInvariantTwoSubgroup D T' →
          ∃ c : G, c ∈ centralizer (D : Set G) ∧ T'.map (MulAut.conj c).toMonoidHom = T

theorem ExtremalObstruction.normalizer_le_of_signalizers_le (hS : Setting G) (hD1 : TheoremD1 G)
    {p : ℕ} (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M D : Subgroup G}
    (hext : ExtremalObstruction p P M D) (hPD : (P : Subgroup G) ≤ normalizer (D : Set G))
    (hsig : ∀ K : Subgroup G, Nat.Coprime p (Nat.card K) →
      (P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) ≤ normalizer (K : Set G) → K ≤ M) :
    normalizer (D : Set G) ≤ M := by
  have hprime := sigmaA_prime p hp
  have hfact : Fact p.Prime := ⟨hprime⟩
  obtain ⟨hM, hDP, -, -⟩ := hext.obstruction
  obtain ⟨hPM, hP3⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨-, U, hUD, -, -, -, -, hNU⟩ := hext.exists_normal_plane hS hp hPD
  have hCD : centralizer (D : Set G) ≤ M :=
    (centralizer_le (SetLike.coe_subset_coe.mpr hUD.le)).trans
      ((centralizer_le_normalizer _).trans hNU)
  have hD₂M : D ⊔ centralizer (D : Set G) ≤ M := sup_le (hDP.trans hPM) hCD
  have hND₂ : normalizer (D : Set G) ≤
      normalizer ((D ⊔ centralizer (D : Set G) : Subgroup G) : Set G) :=
    (le_inf le_rfl (normalizer_le_normalizer_centralizer D)).trans
      (inf_normalizer_le_normalizer_sup _ _)
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf p (P : Subgroup G) (normalizer (D : Set G)) :=
    ⟨P.subtype hPD, by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hPD]⟩
  have hD₁syl := hPsyl.inf_of_le_normalizer
    (sup_le le_normalizer (centralizer_le_normalizer _)) hND₂
  have hPD₁ : (P : Subgroup G) ≤ normalizer (((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G)) :
      Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf (P : Subgroup G) (P : Subgroup G) _ le_normalizer
      (hPD.trans hND₂)
  have hND₁ := rankTwo_full_sylow_normalizer_signalizer_branch p hprime (sigmaA_odd p hp) P M
    ((P : Subgroup G) ⊓ (D ⊔ centralizer (D : Set G))) hM.1 (inf_le_left.trans hPM) hPD₁ hPM
    hP3.ge hsig (fun H hH h3 => le_of_three_le_pRank_inf hD1 hp hM hH h3)
  exact (le_sup_normalizer_of_isSylowOf hND₂ hD₁syl).trans (sup_le hD₂M hND₁)

theorem fullCoreLocal_of_cases (hS : Setting G) (hD1 : TheoremD1 G) (hA : SignalizerCase G)
    (hB : TransitivityCase G) : FullCoreLocal G := by
  by_contra hfail
  obtain ⟨p, hp, P, M, D, hext⟩ := exists_extremal_obstruction hS hD1 hfail
  obtain ⟨hM, hDP, -, hDM⟩ := hext.obstruction
  by_cases hPD : (P : Subgroup G) ≤ normalizer (D : Set G)
  · exact hDM (hext.normalizer_le_of_signalizers_le hS hD1 hp hPD
      (fun K hK hDK => hA p hp P M D hext hPD K hK hDK))
  · obtain ⟨hC, T, hT, hNT, htrans⟩ := hB p hp P M D hext hPD
    exact hDM (rankTwo_normalizer_le_of_signalizer_transitivity D M T hT hC hNT htrans)

end CFSG.LocalAnalysis.RankThreeTheoremC
