module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.BlockB.E9Transitive.Proj
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.E9Main

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.E9Transitive

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.RankThreeTheoremC CFSG.AGLEmbeddingD2.McLaughlin
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData


theorem not_transitive_of_typeTwo {Q : Type} [Group Q] [Finite Q] {Lb P E N : Subgroup Q}
    (hqs : CFSG.Open.IsQuasisimple ↥Lb) (hcl : IsClassicalTwoOrG2 (↥Lb ⧸ Subgroup.center ↥Lb))
    (hpar : IsParabolicTwo Lb P) (hnot : ¬ IsSylowTwoOf (pCoreOf 2 P) Lb)
    (hno : ∀ J : Subgroup Q, J ≤ P → ⁅J, J⁆ = J → ¬ 3 ∣ Nat.card J)
    (hEL : E ≤ Lb ⊔ Subgroup.centralizer (Lb : Set Q))
    (hEC : E ⊓ Subgroup.centralizer (Lb : Set Q) = ⊥) (hE9 : Nat.card E = 9)
    (hEJ : (projHom hEL).range ≤
      (P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)))
    (hsyl : ¬ 3 ∣ ((projHom hEL).range.subgroupOf
      ((P.subgroupOf Lb).map (QuotientGroup.mk' (Subgroup.center ↥Lb)))).index)
    (hNL : N ≤ Subgroup.normalizer (Lb : Set Q)) (hNP : N ≤ Subgroup.normalizer (P : Set Q)) :
    ¬ TransitiveOnNonidentity N E := by
  classical
  intro htr
  have hPL : P ≤ Lb := hpar.1
  set ρ := QuotientGroup.mk' (Subgroup.center ↥Lb)
  set P' : Subgroup ↥Lb := P.subgroupOf Lb
  have hcardE : Nat.card (projHom hEL).range = 9 := (card_range_projHom hEL hEC).trans hE9
  obtain ⟨T, hT, hNJ, hJ, hperf⟩ := exists_overgroup_quotient_map Lb P hpar hnot hno
  have hcen := kFactParabolicThreeCensus _ hcl T _ hT hNJ hJ hperf
  have hXp : ⁅(⊤ : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb)),
      (⊤ : Subgroup (↥Lb ⧸ Subgroup.center ↥Lb))⁆ = ⊤ := by
    have hLp : Group.IsPerfect ↥Lb := OutElemRank.isPerfect_of_quasisimple hqs
    have : Group.IsPerfect (↥Lb ⧸ Subgroup.center ↥Lb) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    exact this.commutator_eq_top
  have h9J : 9 ∣ Nat.card (P'.map ρ) := hcardE ▸ Subgroup.card_dvd_of_le hEJ
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowTwoOf_top hT
  have hNJ' := hNJ
  have hJ' := hJ
  rw [← hS] at hNJ' hJ'
  have hsep : ∀ {t : CFSG.Open.StatedLieTag} {n : ℕ},
      CFSG.Open.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb) t n 2 1 →
      (t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU) → False :=
    fun {t n} hc ht =>
      not_transitive_of_separated_proj hPL hEL hNL hNP
        (separated_pair_of_model hc ht S _ hNJ' hJ' hperf hEJ hcardE hsyl) htr
  have hmodel : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n : ℕ},
      CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥Lb ⧸ Subgroup.center ↥Lb) t n 2 1 →
      (t = .PSL ∨ t = .PSp ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .PSU) → False := by
    intro t n hc ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · exact hsep (t := .PSL) hc (Or.inl rfl)
    · exact hsep (t := .PSp) hc (Or.inr (Or.inl rfl))
    · exact hsep (t := .POmegaPlus) hc (Or.inr (Or.inr (Or.inl rfl)))
    · exact hsep (t := .POmegaMinus) hc (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact hsep (t := .PSU) hc (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rcases hcen with ⟨d, hd, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | ⟨d, hd, ⟨e⟩⟩
  · obtain ⟨t, n, ht, hc⟩ := exists_model_of_indexTwo d hd e
    exact hmodel hc ht
  · rcases hm with rfl | rfl | rfl
    ·
      have h60 : Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) = 60 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      have := h9J.trans (Subgroup.card_subgroup_dvd_card _)
      rw [h60] at this
      norm_num at this
    · exact false_of_nineFree (NineFreeOver.of_mulEquiv e.symm nineFreeOver_alt_six) hXp hT hNJ
        hperf h9J
    · exact hmodel (CFSG.QuasithinUnique.Ch1.statedClassicalModel_psl_four_two_of_alternating_eight
        _ ⟨e⟩) (Or.inl rfl)
  · rcases hd with ⟨q, hq, hd'⟩ | ⟨q, hq, hd'⟩
    · exact false_of_nineFree (nineFreeOver_catalog_seven hq hd' e) hXp hT hNJ hperf h9J
    · exact false_of_nineFree (nineFreeOver_catalog_psu_three_three hq hd' e) hXp hT hNJ hperf h9J

end CFSG.LocalAnalysis.RankThreeTheoremC.BlockB.E9Transitive
