module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthD4CentralizerSpin
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternBasic

public section

namespace CFSG.ClassicalInvolution.RouteD.ETCtx

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups modelUniv
  IsClassicalMember centralizingMembers)

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {N : Subgroup G} {x : G}

theorem commutes_iff_of_d4 (cx : ETCtx p f .POmegaPlus 6 Ω N x)
    (hD4 : Gaps.D4Centralizer (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D))
    {S S' J₂ J₃ J₄ J₅ B : Subgroup G} {wS wS' w₂ w₃ w₄ w₅ wB : G}
    (hS : IsLayerMember cx S) (hS' : IsLayerMember cx S') (h₂ : IsLayerMember cx J₂)
    (h₃ : IsLayerMember cx J₃) (h₄ : IsLayerMember cx J₄) (h₅ : IsLayerMember cx J₅)
    (hB : IsLayerMember cx B) (hwS : IsClassicalMember p f S wS)
    (hwS' : IsClassicalMember p f S' wS') (hw₂ : IsClassicalMember p f J₂ w₂)
    (hw₃ : IsClassicalMember p f J₃ w₃) (hw₄ : IsClassicalMember p f J₄ w₄)
    (hw₅ : IsClassicalMember p f J₅ w₅) (hwB : IsClassicalMember p f B wB)
    (p23 : ∃ W, LinearBlockStandardPair (GaloisField p f) W J₂ J₃)
    (p34 : ∃ W, LinearBlockStandardPair (GaloisField p f) W J₃ J₄)
    (p35 : ∃ W, LinearBlockStandardPair (GaloisField p f) W J₃ J₅)
    (c24 : Commutes J₂ J₄) (c25 : Commutes J₂ J₅) (c45 : Commutes J₄ J₅) (hSS' : S ≠ S')
    (s₂ : Commutes S J₂) (s₃ : Commutes S J₃) (s₄ : Commutes S J₄) (s₅ : Commutes S J₅)
    (s₂' : Commutes S' J₂) (s₃' : Commutes S' J₃) (s₄' : Commutes S' J₄)
    (s₅' : Commutes S' J₅) (hBS : B ≠ S) (hBS' : B ≠ S') (cBS : Commute wB wS)
    (cBS' : Commute wB wS') : Commutes B S ↔ Commutes B S' := by
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f cx.hp2
  obtain ⟨RS, hRS, hSR⟩ := hS.exists_fund
  obtain ⟨RS', hRS', hSR'⟩ := hS'.exists_fund
  obtain ⟨R₂, hR₂, h₂R⟩ := h₂.exists_fund
  obtain ⟨R₃, hR₃, h₃R⟩ := h₃.exists_fund
  obtain ⟨R₄, hR₄, h₄R⟩ := h₄.exists_fund
  obtain ⟨R₅, hR₅, h₅R⟩ := h₅.exists_fund
  obtain ⟨RB, hRB, hBR⟩ := hB.exists_fund
  obtain ⟨W₂₃, hW₂₃⟩ := p23
  obtain ⟨W₃₄, hW₃₄⟩ := p34
  obtain ⟨W₃₅, hW₃₅⟩ := p35
  have a32 : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) R₃ R₂ :=
    cx.modelAdj_of_adj h₃.1 h₂.1 hR₃ hR₂ h₃R h₂R hw₃ hw₂ (ne_of_linearBlockStandardPair hW₂₃).symm
      (fun h => not_commutes_of_linearBlockStandardPair hW₂₃ (Gaps.commutes_symm h))
      (Gaps.standardPair_involutions_commute h2 hW₂₃ hw₂.mem hw₃.mem hw₂.orderOf_eq_two
        hw₃.orderOf_eq_two).symm
      (Gaps.conjSub_eq_of_standardPair h2 hW₂₃.symm hw₂.mem hw₂.orderOf_eq_two)
  have a34 : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) R₃ R₄ :=
    cx.modelAdj_of_adj h₃.1 h₄.1 hR₃ hR₄ h₃R h₄R hw₃ hw₄ (ne_of_linearBlockStandardPair hW₃₄)
      (not_commutes_of_linearBlockStandardPair hW₃₄)
      (Gaps.standardPair_involutions_commute h2 hW₃₄ hw₃.mem hw₄.mem hw₃.orderOf_eq_two
        hw₄.orderOf_eq_two)
      (Gaps.conjSub_eq_of_standardPair h2 hW₃₄ hw₄.mem hw₄.orderOf_eq_two)
  have a35 : Gaps.ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) R₃ R₅ :=
    cx.modelAdj_of_adj h₃.1 h₅.1 hR₃ hR₅ h₃R h₅R hw₃ hw₅ (ne_of_linearBlockStandardPair hW₃₅)
      (not_commutes_of_linearBlockStandardPair hW₃₅)
      (Gaps.standardPair_involutions_commute h2 hW₃₅ hw₃.mem hw₅.mem hw₃.orderOf_eq_two
        hw₅.orderOf_eq_two)
      (Gaps.conjSub_eq_of_standardPair h2 hW₃₅ hw₅.mem hw₅.orderOf_eq_two)
  have ne_of_comm : ∀ {L L' : Subgroup G}, L ∈ centralizingMembers Ω {x} → Commutes L L' →
      L ≠ L' := fun hL hc e => not_commutes_self_of_mem cx.hΩ hL.1 (e ▸ hc)
  have hne_of_R : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 6 p f
      Fact.out).K}, L ∈ centralizingMembers Ω {x} → L' ∈ centralizingMembers Ω {x} →
      L ≠ L' → locImg Ω x L = R.map cx.d.ψ → locImg Ω x L' = R'.map cx.d.ψ → R ≠ R' :=
    fun hL hL' hne hlR hlR' h => hne (cx.eq_of_locImg_eq hL hL' (by rw [hlR, hlR', h]))
  have cR : ∀ {L L' : Subgroup G} {R R' : Subgroup (modelUniv .POmegaPlus 6 p f Fact.out).K},
      L ∈ centralizingMembers Ω {x} → L' ∈ centralizingMembers Ω {x} →
      R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 p f Fact.out).D →
      locImg Ω x L = R.map cx.d.ψ → locImg Ω x L' = R'.map cx.d.ψ → Commutes L L' →
      Commutes R R' := fun hL hL' hR hlR hlR' hc =>
    (cx.commutes_iff_fund hL hL' hR hlR hlR').mp hc
  have hind := hD4 R₃ hR₃ R₂ hR₂ R₄ hR₄ R₅ hR₅ a32 a34 a35
    (hne_of_R h₂.1 h₄.1 (ne_of_comm h₂.1 c24) h₂R h₄R)
    (hne_of_R h₂.1 h₅.1 (ne_of_comm h₂.1 c25) h₂R h₅R)
    (hne_of_R h₄.1 h₅.1 (ne_of_comm h₄.1 c45) h₄R h₅R)
    (cR h₂.1 h₄.1 hR₂ h₂R h₄R c24) (cR h₂.1 h₅.1 hR₂ h₂R h₅R c25)
    (cR h₄.1 h₅.1 hR₄ h₄R h₅R c45) RS hRS RS' hRS' (hne_of_R hS.1 hS'.1 hSS' hSR hSR')
    (cR hS.1 h₃.1 hRS hSR h₃R s₃) (cR hS.1 h₂.1 hRS hSR h₂R s₂) (cR hS.1 h₄.1 hRS hSR h₄R s₄)
    (cR hS.1 h₅.1 hRS hSR h₅R s₅) (cR hS'.1 h₃.1 hRS' hSR' h₃R s₃')
    (cR hS'.1 h₂.1 hRS' hSR' h₂R s₂') (cR hS'.1 h₄.1 hRS' hSR' h₄R s₄')
    (cR hS'.1 h₅.1 hRS' hSR' h₅R s₅')
  have hiK : Gaps.ModelInvComm (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) RB
      RS := by
    obtain ⟨r, r', hr, hr', hcen, -, -⟩ := cx.modelInvComm_of_commute hB.1 hS.1 hRB hRS hBR hSR
      hwB hwS cBS
    exact ⟨r, r', hr, hr', hcen⟩
  have hiN : Gaps.ModelInvComm (Subgroup.center (modelUniv .POmegaPlus 6 p f Fact.out).K) RB
      RS' := by
    obtain ⟨r, r', hr, hr', hcen, -, -⟩ := cx.modelInvComm_of_commute hB.1 hS'.1 hRB hRS' hBR
      hSR' hwB hwS' cBS'
    exact ⟨r, r', hr, hr', hcen⟩
  have key := hind.2 RB hRB (hne_of_R hB.1 hS.1 hBS hBR hSR) (hne_of_R hB.1 hS'.1 hBS' hBR hSR')
    hiK hiN
  rw [cx.commutes_iff_fund hB.1 hS.1 hRB hBR hSR, cx.commutes_iff_fund hB.1 hS'.1 hRB hBR hSR']
  exact key

end CFSG.ClassicalInvolution.RouteD.ETCtx
