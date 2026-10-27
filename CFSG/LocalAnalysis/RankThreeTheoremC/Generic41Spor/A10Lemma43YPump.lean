module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43YBasic
import CFSG.HardMathSupport.Solomon.Coordinator.I18_3Main
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_6_Normalizes
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueRelativeBMinimal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding Subgroup

variable {Y : Type} [Group Y] [Finite Y] {P : Subgroup Y} {x t₁ t₂ : Y} {J₁ J₂ F : Subgroup Y}

theorem a10y_pumpup_one (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h : A10YData Y P x t₁ t₂ J₁ J₂ F) {J : Subgroup Y}
    (hJ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set Y)) J) (hJ1 : J ≠ ⊥) :
    ∃ A : Subgroup Y, IsComponentOf A ⊤ ∧ J ≤ A := by
  have hx5 : x ^ 5 = 1 := by
    have h1 := pow_orderOf_eq_one x
    rwa [h.x_ord] at h1
  have hE : IsElemAbelian 5 (zpowers x) := CFSG.Open.isElemAbelian_zpowers hx5
  have hcent : (⊤ : Subgroup Y) ⊓ Subgroup.centralizer ((zpowers x : Subgroup Y) : Set Y) =
      Subgroup.centralizer ({x} : Set Y) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure, top_inf_eq]
  have hJ' : GLAPComponent 5
      ((⊤ : Subgroup Y) ⊓ Subgroup.centralizer ((zpowers x : Subgroup Y) : Set Y)) J := by
    rw [hcent]; exact hJ
  obtain ⟨𝒞, hC1, hC2, -, hC4⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.input18_3_4_of_schreier hSch Y ⊤ (a10y_isKGroup h) 5
      (by norm_num) (zpowers x) le_top hE J hJ'
  have hcomp : ∀ L ∈ 𝒞, IsComponentOf L ⊤ := fun L hL =>
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.i116n_isComponentOf_of_glaPComponent
      (a10y_glaCore h) (hC1 L hL)
  have hsingle : ∀ L ∈ 𝒞, ∀ L' ∈ 𝒞, L = L' := by
    intro L hL L' hL'
    obtain ⟨e, he, rfl⟩ := hC4 L hL L' hL'
    refine (CFSG.LocalAnalysis.GLTheoremB.gLBConj_eq_of_mem_normalizer ?_).symm
    refine a10y_mem_normalizer_of_pElement h ?_ (hcomp L hL)
    exact ⟨1, by simpa using hE.2 e he⟩
  have hJle : J ≤ ⨆ L ∈ 𝒞, L := by
    rw [hC2]
    refine le_trans (le_of_eq (CFSG.LocalAnalysis.GLTheoremB.gLBConj_one J).symm) ?_
    exact le_iSup₂ (f := fun (g : Y) (_ : g ∈ GLAPLayer 5 (⊤ : Subgroup Y)) => GLBConj g J)
      (1 : Y) (one_mem _)
  have hne : 𝒞.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    subst hemp
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, le_bot_iff] at hJle
    exact hJ1 hJle
  obtain ⟨A, hA⟩ := hne
  have hAle : (⨆ L ∈ 𝒞, L) ≤ A := iSup₂_le fun L hL => (hsingle L hL A hA).le
  exact ⟨A, hcomp A hA, hJle.trans hAle⟩

theorem a10y_pumpup (hSch : CFSG.ComponentClassification.CatalogueRelativeB.CatalogueSchreier)
    (h : A10YData Y P x t₁ t₂ J₁ J₂ F) :
    ∃ A₁ A₂ : Subgroup Y, IsComponentOf A₁ ⊤ ∧ IsComponentOf A₂ ⊤ ∧ J₁ ≤ A₁ ∧ J₂ ≤ A₂ := by
  have hne : ∀ {t : Y} {J : Subgroup Y}, t ∈ J → orderOf t = 5 → J ≠ ⊥ := by
    intro t J ht ho hJ
    subst hJ
    have : t = 1 := (Subgroup.mem_bot).1 ht
    subst this
    simp at ho
  obtain ⟨A₁, hA₁, hJ₁⟩ := a10y_pumpup_one hSch h h.comp₁ (hne h.t₁_mem.2 h.t₁_ord)
  obtain ⟨A₂, hA₂, hJ₂⟩ := a10y_pumpup_one hSch h h.comp₂ (hne h.t₂_mem.2 h.t₂_ord)
  exact ⟨A₁, A₂, hA₁, hA₂, hJ₁, hJ₂⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
