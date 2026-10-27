module

public import CFSG.Quasithin.EmptyFaithful.SBd9Glue
public import CFSG.GH74.QTGen4.DCopy.Quasithin.EmptyFaithful.S153D35

public section

namespace CFSG.Quasithin.SBd9

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

@[expose] def Input15338Rest_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) →
      IsPSL 3 2 2 (↥L ⧸ Subgroup.center ↥L) → oTwoUpper (Yp ⊓ L) ≠ ⊥ →
      (∃ y ∈ Yp, orderOf y = 3 ∧ y ∉ L ⊔ Subgroup.centralizer (L : Set G) ∧
        Yp = oTwoUpper (Yp ⊓ L) ⊔ Subgroup.zpowers y ⊔ pCoreOf 2 Yp) → ¬ Yp ≤ L →
      I ≤ Subgroup.normalizer (L : Set G) → Yp = Y153 Mc M →
      Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) →
      L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I →
      Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G) →
      V₁ ≤ Subgroup.centralizer (L : Set G) →
      (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) → V₂ ≤ oTwoUpper (Yp ⊓ L) →
      (¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) → False

theorem input15338_of_rest_F4 (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hrank : Lemma122Rank) (kR : RankOneFamilies153) (kRest : Input15338Rest_F4) : Input15338_F4 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c c37 hr
  by_contra hY
  have hq := c.hyp.hyp.qtfe
  have hLI := c.c33.mem
  rcases c37 with h1 | ⟨hL0, hlist, -⟩ | ⟨hL0, hlist, hYL, hy⟩
  ·
    have hn := lemma_1_2_2_b hq.qtke hq.simple hq.nonabelian h37 h38 hrank c.inH.1.2 hLI
      Nat.prime_three (by norm_num) hr
    exact hY (h1.trans (S153I.conjClosure_le_of_normal (le_of_mem_cComp hLI)
      (le_sup_right.trans c.inH.1.1) hn))
  ·
    have h := kR ↥L (S153I.isPGroup_two_center_of_center_eq c.c33.center_eq) hlist
    rw [pRank_top_subtype] at h
    omega
  ·
    have hNL : I ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hLI)).mp
        (lemma_1_2_2_b hq.qtke hq.simple hq.nonabelian h37 h38 hrank c.inH.1.2 hLI Nat.prime_three
          (by norm_num) hr)
    obtain ⟨hn2, hYY, ⟨hB, hBM, hQV⟩, hcase⟩ := prefix38_of_psl h113 h37 h38 c hL0 hlist hYL
    rcases hcase with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
    · exact kRest G T Mc M V₁ V₂ Yp I L t c hL0 hn2 hYL hy hY hNL hYY hB hBM hQV h1 h2 h3 h4
    ·
      have hS := sgp153_swap c.hyp.hyp c.hyp.decomp
      have c' := ctxComp2_swap c hYY
      have hL0' : L = conjClosure L (Sgp153 T V₂) := by rw [hS]; exact hL0
      rw [← hS] at hB hBM hQV
      exact kRest G T Mc M V₂ V₁ Yp I L t c' hL0' hn2 hYL hy hY hNL hYY hB hBM hQV h1 h2 h3 h4

end CFSG.Quasithin.SBd9
