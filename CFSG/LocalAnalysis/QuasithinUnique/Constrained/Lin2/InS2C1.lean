module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Syl

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem Q_eq_Y₁₁ : pCoreOf 2 H = AppE.cB S (blockU L) ⊓ AppE.cB S (conjSubgroup (blockU L) t) :=
  B.su.O_eq_DU.trans B.su.Y₁₁_eq.symm

theorem conj_cB (V : Subgroup G) :
    conjSubgroup (AppE.cB S V) x₀ = AppE.cB S (conjSubgroup V x₀) := by
  unfold AppE.cB
  rw [C5.conjSubgroup_inf, C5.conjSubgroup_eq_self B.su.hxB, C5.conjSubgroup_centralizer]

theorem conj_pCore_eq : conjR (pCoreOf 2 H) x₀ = AppE.cB S (conjSubgroup (blockU L) x₀) ⊓
    AppE.cB S (conjSubgroup (conjSubgroup (blockU L) t) x₀) := by
  show conjSubgroup (pCoreOf 2 H) x₀ = _
  rw [B.Q_eq_Y₁₁, C5.conjSubgroup_inf, B.conj_cB, B.conj_cB]

theorem Q_le_R : pCoreOf 2 H ≤ thompsonJ S := by
  rw [B.Q_eq_Y₁₁, ← B.baum_eq]
  exact inf_le_left.trans (AppE.cB_le_baum S _)

theorem conj_pCore_le_R : conjR (pCoreOf 2 H) x₀ ≤ thompsonJ S := by
  rw [B.conj_pCore_eq, ← B.baum_eq]
  exact inf_le_left.trans (AppE.cB_le_baum S _)

theorem D_le_normalizer_pCore : D ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  (B.D_le_L₀.trans B.L₀_le_H).trans
    (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)

theorem S_le_normalizer_pCore : S ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
  B.S_le_H.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)

theorem pCore_sup_conj : pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x₀ = thompsonJ S := by
  have h2 : conjR (pCoreOf 2 H) x₀ =
      baumD S L ⊔ conjSubgroup (blockU L ⊔ conjSubgroup (blockU L) t) x₀ := by
    rw [B.conj_pCore_eq]
    exact B.su.Y₂₂_eq
  rw [h2, B.su.O_eq_DU, ← B.baum_eq]
  refine le_antisymm (sup_le (sup_le (AppE.baumD_le_baum S L) (sup_le B.su.U₁_le_B B.su.U₂_le_B))
    (sup_le (AppE.baumD_le_baum S L) ?_)) ?_
  · rw [C5.conjSubgroup_sup]
    exact sup_le B.su.X_le_B B.su.Y_le_B
  · rw [B.su.B_eq_sup]
    exact sup_le (sup_le (le_sup_of_le_left le_sup_left) (le_sup_of_le_left le_sup_right))
      (le_sup_of_le_right le_sup_right)

theorem conj_pCore_elemAb : C5.ElemAb2 (conjR (pCoreOf 2 H) x₀) := by
  have h := B.su.elemAb_DX
  rw [← B.su.Y₂₂_eq, ← B.conj_pCore_eq] at h
  exact h

theorem D_le_normalizer_conj_pCore :
    D ≤ Subgroup.normalizer ((conjR (pCoreOf 2 H) x₀ : Subgroup G) : Set G) := by
  intro d hd
  have hdR : d ∈ Subgroup.normalizer (thompsonJ S : Set G) := B.D_le_normalizer_R hd
  have hdB : d ∈ Subgroup.normalizer (baum S : Set G) := by rw [B.baum_eq]; exact hdR
  have hdQ : d ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) := B.D_le_normalizer_pCore hd
  have hQ := B.Q_eq_Y₁₁
  have hY := B.conj_pCore_eq
  set Y : Subgroup G := conjR (pCoreOf 2 H) x₀ with hYdef
  have hYB : Y ≤ baum S := by rw [B.baum_eq]; exact B.conj_pCore_le_R
  have hAle : conjR Y d ≤ baum S := by
    have := conjR_mono hYB d
    rwa [conjR_eq_of_mem_normalizer hdB] at this
  have hAe : C5.ElemAb2 (conjR Y d) := B.conj_pCore_elemAb.conjSubgroup d
  have hQA : pCoreOf 2 H ⊔ conjR Y d = baum S := by
    have h1 : conjR (pCoreOf 2 H ⊔ Y) d = conjR (thompsonJ S) d := by rw [B.pCore_sup_conj]
    rw [conjR_sup, conjR_eq_of_mem_normalizer hdQ, conjR_eq_of_mem_normalizer hdR] at h1
    rw [h1, B.baum_eq]
  have hQ1 : pCoreOf 2 H ≤ baum S ⊓ Subgroup.centralizer (blockU L : Set G) := by
    rw [hQ]; exact inf_le_left
  have hQ2 : pCoreOf 2 H ≤ baum S ⊓
      Subgroup.centralizer ((conjSubgroup (blockU L) t : Subgroup G) : Set G) := by
    rw [hQ]; exact inf_le_right
  obtain ⟨hd1, hd2⟩ := B.su.elemAb_dichotomy hAe hAle
  have hgood := B.su.good
  have hgood₂ := B.su.good₂
  rw [B.su.loc₂.rk.Q_eq] at hgood₂
  rw [← conjR_eq_self_iff]
  rcases hd1 with h1 | h1'
  · exfalso
    apply hgood
    refine B.su.X_le_B.trans ?_
    calc baum S = pCoreOf 2 H ⊔ conjR Y d := hQA.symm
      _ ≤ _ := sup_le hQ1 h1
  rcases hd2 with h2 | h2'
  · exfalso
    apply hgood₂
    refine B.su.Y_le_B.trans ?_
    calc baum S = pCoreOf 2 H ⊔ conjR Y d := hQA.symm
      _ ≤ _ := sup_le hQ2 h2
  · have hle : conjR Y d ≤ Y := le_of_le_of_eq (le_inf h1' h2') hY.symm
    exact Subgroup.eq_of_le_of_card_ge hle (card_conjR Y d).ge

end S2Base

end CFSG.QuasithinUnique.Lin2
