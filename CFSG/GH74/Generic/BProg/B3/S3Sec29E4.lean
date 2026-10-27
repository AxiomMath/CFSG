module

public import CFSG.GH74.Generic.BProg.B3.S3Sec29E1
public import CFSG.GH74.Generic.BProg.B3.S3Sec29E3
public import CFSG.GH74.Generic.BProg.B3.S3Ctx29wFacts
public import CFSG.GH74.GLS.C3.Layer1.Th2P72cR3

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.Obs
  CFSG.GH74.GLS.Th2.Bal CFSG.ClassicalInvolution.Balance Subgroup
open scoped commutatorElement

section Lemma299

variable {G : Type} [Group G] [Finite G]

theorem lemma299w
    (hDich : S3Sec29E3.A7Dich) {x y : G} {K A B Q D J : Subgroup G}
    (h : Ctx29w G x K A B Q y y D J) (htype : IsA7Bar J ∨ IsL2OddW J)
    (h298 : ¬ HasSL2Model (↥J ⧸ pPrimeCore 2 ↥J) Odd) :
    IsA7Bar J ∧ B ≤ normalizer (J : Set G) ∧
      (∀ J'' : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) J'' → IsA7Bar J'' → J'' = J) ∧
      ∃ (e : kBar J ≃* alternatingGroup (Fin 7)) (F₀ F₁ : Subgroup (Equiv.Perm (Fin 7))),
        GLS.Th2.Obs.IsRootFour F₀ ∧
        (F₁ = ⊥ ∨ ∃ t : Equiv.Perm (Fin 7), t.IsSwap ∧ F₁ = zpowers t ∧
          ∀ i, (∃ f ∈ F₀, f i ≠ i) → t i = i) ∧
        (B.subgroupOf (normalizer (J : Set G))).map (GLS.Th2.Obs.a7Act J e) = F₀ ⊔ F₁ := by
  classical
  have hty : IsA7Bar J ∨ IsL2OddNonSquare J := isL2OddNonSquare_of_W htype h298
  have hG4 : pRank 2 G ≤ 4 := Gen4.pRank_two_le h.hyp.gen4
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := h.ext.2.2.2.1
  have hyB : y ∈ B := h.b_mem
  have hy2 : orderOf y = 2 := h.y_ord
  have hcomp : IsPCompIn 2 (centralizer ({y} : Set G)) J := by
    rcases h.obs with ho | ⟨-, ho, -⟩
    · exact ho.comp
    · exact ho.comp
  obtain ⟨hcen, hrk⟩ := S3Sec29E1.centerless_and_rank hcomp hty
  have hBN : ∀ g ∈ B, g ∈ normalizer (J : Set G) := fun g hg =>
    mem_normalizer_of_pRank_le_four hG4 hy2 hBel hyB hcomp hcen hrk hg
  have hBN' : B ≤ normalizer (J : Set G) := fun g hg => hBN g hg
  have hA7J : IsA7Bar J := by
    rcases h.obs with hobs | ⟨-, -, -, hA7, -⟩
    · exact (S3Sec29E1.caseA hobs hBel hyB hBN hty).1
    · exact hA7
  have huniq : ∀ J'' : Subgroup G, IsPCompIn 2 (centralizer ({y} : Set G)) J'' → IsA7Bar J'' →
      J'' = J := by
    intro J'' hJ'' hA''
    obtain ⟨hcen'', hrk''⟩ := S3Sec29E1.centerless_and_rank hJ'' (Or.inl hA'')
    exact eq_of_isPCompIn_of_pRank_le_four hG4 hy2 hcomp hJ'' hcen hcen'' hrk hrk''
  obtain ⟨e⟩ := hA7J
  refine ⟨⟨e⟩, hBN', huniq, e, ?_⟩
  rcases h.obs with hobs | ⟨-, hobs, -, -, hnot⟩
  · exact (S3Sec29E1.caseA hobs hBel hyB hBN hty).2 e
  · exact S3Sec29E3.caseB hDich hcomp hyB hBel h.rankB hBN' hcen e
      ((Ctx29w.rank_quot h).2 rfl hobs) hnot

end Lemma299

end CFSG.GH74.Generic.BProg.B3
