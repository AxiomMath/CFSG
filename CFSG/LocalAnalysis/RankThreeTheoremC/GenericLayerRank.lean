module

public import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoPElements
public import CFSG.GroupTheory.ABGLocalTools.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericCaseExtremal
import CFSG.LocalAnalysis.RankThreeTheoremC.PSLTwoRank
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_elemAbelian_card {p : ℕ} [Fact p.Prime] {P E : Subgroup G} {k : ℕ}
    (hEP : E ≤ P) (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p P := CFSG.SectionRank.le_pRank (Fact.out : p.Prime).one_lt hEP hE hc

theorem add_le_pRank_of_commute {p : ℕ} [Fact p.Prime] {P E₁ E₂ : Subgroup G} {r s : ℕ}
    (h₁ : IsElemAbelian p E₁) (h₂ : IsElemAbelian p E₂) (hc₁ : Nat.card E₁ = p ^ r)
    (hc₂ : Nat.card E₂ = p ^ s) (hcomm : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a)
    (hdisj : Disjoint E₁ E₂) (h₁P : E₁ ≤ P) (h₂P : E₂ ≤ P) : r + s ≤ CFSG.Open.pRank p P := by
  have e₁ : CFSG.IsElementaryAbelian p E₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₁).2 h₁
  have e₂ : CFSG.IsElementaryAbelian p E₂ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₂).2 h₂
  have hCE : E₂ ≤ centralizer (E₁ : Set G) := fun b hb =>
    mem_centralizer_iff.mpr fun a ha => hcomm a ha b hb
  have hsup : CFSG.IsElementaryAbelian p ↥(E₁ ⊔ E₂) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hCE
  have hcard : Nat.card ↥(E₁ ⊔ E₂) = p ^ (r + s) := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E₁ E₂
      (hCE.trans (centralizer_le_normalizer _)) hdisj, hc₁, hc₂, pow_add]
  exact le_pRank_of_elemAbelian_card (sup_le h₁P h₂P)
    ((CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hsup) hcard

theorem le_pRank_inf_of_mulEquiv_psl {p : ℕ} [Fact p.Prime] {P C L : Subgroup G}
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p P C) (hLC : L ≤ C)
    (hCL : C ≤ normalizer (L : Set G)) {m : ℕ} (hm : m ≠ 0)
    (e : L ≃* PSL(2, GaloisField p m)) : m ≤ CFSG.Open.pRank p (P ⊓ L) := by
  have hprime : p.Prime := Fact.out
  have hAsyl : CFSG.ABGLocalTools.IsSylowOf p (P ⊓ L) L := hsyl.inf_of_le_normalizer hLC hCL
  have h1 : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p (P ⊓ L) := pRank_le_of_isSylowOf hAsyl
  have h2 : m ≤ CFSG.Open.pRank p L := by
    rw [pRank_subgroup_eq_internal_top p hprime.one_lt L,
      pRank_top_eq_of_equiv p hprime.one_lt e]
    exact le_pRank_psl_two p m hm
  omega

theorem exists_isElemAbelian_le_sup_zpowers {p : ℕ} [Fact p.Prime] {P C L : Subgroup G} {x : G}
    (hLC : L ≤ C) (hxP : x ∈ P) (hxp : x ^ p = 1) (hxC : ∀ c ∈ C, c * x = x * c)
    (hxL : x ∉ L) (hpos : 0 < CFSG.Open.pRank p (P ⊓ L)) :
    ∃ E : Subgroup G, E ≤ P ∧ E ≤ L ⊔ zpowers x ∧ IsElemAbelian p E ∧
      Nat.card E = p ^ (CFSG.Open.pRank p (P ⊓ L) + 1) := by
  have hprime : p.Prime := Fact.out
  obtain ⟨E, hEA, hE, hEc⟩ := pRank_attained p (P ⊓ L) hpos
  have hxE : x ∉ E := fun h => hxL (hEA h).2
  have hcommE : ∀ a ∈ E, a * x = x * a := fun a ha => hxC a (hLC (hEA ha).2)
  have hcardE := CFSG.RankThree.PartOne.Planes.card_sup_zpowers hprime E hxp hxE hcommE
  have e₁ : CFSG.IsElementaryAbelian p E :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E).2 hE
  have e₂ : CFSG.IsElementaryAbelian p (zpowers x) :=
    CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hxp
  have hCE : zpowers x ≤ centralizer (E : Set G) :=
    zpowers_le.mpr (mem_centralizer_iff.mpr fun a ha => hcommE a ha)
  have hsup : CFSG.IsElementaryAbelian p ↥(E ⊔ zpowers x) :=
    CFSG.IsElementaryAbelian.sup_of_le_centralizer hCE
  exact ⟨E ⊔ zpowers x, sup_le (hEA.trans inf_le_left) (zpowers_le.mpr hxP),
    sup_le_sup (hEA.trans inf_le_right) le_rfl,
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p _).1 hsup,
    by rw [hcardE, hEc, pow_succ]⟩

theorem pRank_inf_add_one_le {p : ℕ} [Fact p.Prime] {P C L : Subgroup G} {x : G}
    (hLC : L ≤ C) (hxP : x ∈ P) (hxp : x ^ p = 1) (hxC : ∀ c ∈ C, c * x = x * c)
    (hxL : x ∉ L) (hpos : 0 < CFSG.Open.pRank p (P ⊓ L)) :
    CFSG.Open.pRank p (P ⊓ L) + 1 ≤ CFSG.Open.pRank p P := by
  obtain ⟨E, hEP, -, hE, hEc⟩ := exists_isElemAbelian_le_sup_zpowers hLC hxP hxp hxC hxL hpos
  exact le_pRank_of_elemAbelian_card hEP hE hEc

theorem eq_two_of_isSylowOf_mulEquiv_psl {p : ℕ} [Fact p.Prime] {P C L : Subgroup G} {x : G}
    (hsyl : CFSG.ABGLocalTools.IsSylowOf p P C) (hLC : L ≤ C)
    (hCL : C ≤ normalizer (L : Set G)) (hxP : x ∈ P) (hx1 : x ≠ 1) (hxp : x ^ p = 1)
    (hxC : ∀ c ∈ C, c * x = x * c) (hP3 : CFSG.Open.pRank p P ≤ 3) {m : ℕ} (hm : 2 ≤ m)
    (e : L ≃* PSL(2, GaloisField p m)) : m = 2 ∧ CFSG.Open.pRank p (P ⊓ L) = 2 := by
  have hrk := le_pRank_inf_of_mulEquiv_psl hsyl hLC hCL (by omega) e
  have hxL : x ∉ L := fun h => hx1 (eq_one_of_commute_of_mulEquiv_psl_two e h
    fun h' hh' => hxC h' (hLC hh'))
  have hrk3 := pRank_inf_add_one_le hLC hxP hxp hxC hxL (by omega)
  omega

end CFSG.LocalAnalysis.RankThreeTheoremC
