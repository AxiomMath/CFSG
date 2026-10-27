module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Step

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

structure S4Ctx (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  prime : p.Prime
  simple : IsSimpleGroup G
  nonabelian : ∃ a b : G, a * b ≠ b * a
  kProper : CFSG.Open.IsKProper G
  input18_3_4 : Input18_3_4
  i1131 : I1131At G p
  i1122 : I1122IsoAt G p

variable {G : Type} [Group G] [Finite G]

theorem S4Ctx.step {p : ℕ} (hc : S4Ctx G p) {t t' : Triple G} (hrel : PumpRel p t t') :
    Nat.card (PQuot p t.2.2) ≤ Nat.card (PQuot p t'.2.2) ∧
    (CentMod p t'.2.2 t.2.1 ↔ Nat.card (PQuot p t.2.2) = Nat.card (PQuot p t'.2.2)) ∧
    (CentMod p t'.2.2 t.2.1 → Nonempty (PQuot p t.2.2 ≃* PQuot p t'.2.2) ∧
      closureIn (GLAPLayer p (t.2.2 ⊓ Subgroup.centralizer ({t'.2.1} : Set G)))
        (GLAPLayer p (Subgroup.centralizer ({t'.2.1} : Set G))) = t'.2.2) :=
  pumpRel_step hc.prime hc.input18_3_4 hc.kProper hc.simple hc.nonabelian hc.i1131 hc.i1122 hrel

theorem card_lt_of_pumpRel_of_not_centMod {p : ℕ} (hc : S4Ctx G p) {t t' : Triple G}
    (hrel : PumpRel p t t') (hnc : ¬ CentMod p t'.2.2 t.2.1) :
    Nat.card (PQuot p t.2.2) < Nat.card (PQuot p t'.2.2) := by
  obtain ⟨hle, hiff, -⟩ := hc.step hrel
  exact lt_of_le_of_ne hle fun h => hnc (hiff.2 h)

theorem card_le_of_reflTransGen {p : ℕ} (hc : S4Ctx G p) {t t' : Triple G}
    (h : Relation.ReflTransGen (PumpRel p) t t') :
    Nat.card (PQuot p t.2.2) ≤ Nat.card (PQuot p t'.2.2) := by
  induction h with
  | refl => exact le_rfl
  | tail _ hstep ih => exact ih.trans (hc.step hstep).1

theorem card_lt_of_pumpLt {p : ℕ} (hc : S4Ctx G p) {t t' : Triple G} (h : PumpLt p t t') :
    Nat.card (PQuot p t.2.2) < Nat.card (PQuot p t'.2.2) := by
  obtain ⟨s, s', hts, hss', hnc, hs't'⟩ := h
  exact ((card_le_of_reflTransGen hc hts).trans_lt
    (card_lt_of_pumpRel_of_not_centMod hc hss' hnc)).trans_le (card_le_of_reflTransGen hc hs't')

theorem lemma41_card {p : ℕ} (hc : S4Ctx G p) {t t' : Triple G}
    (h : Relation.ReflTransGen (PumpRel p) t t') :
    Nat.card (PQuot p t.2.2) ≤ Nat.card (PQuot p t'.2.2) ∧
      (PumpLt p t t' ↔ Nat.card (PQuot p t.2.2) < Nat.card (PQuot p t'.2.2)) := by
  refine ⟨card_le_of_reflTransGen hc h, card_lt_of_pumpLt hc, ?_⟩
  induction h with
  | refl => exact fun h => absurd h (lt_irrefl _)
  | @tail u u' htu hstep ih =>
    intro hlt
    rcases lt_or_eq_of_le (card_le_of_reflTransGen hc htu) with hlt' | heq
    · obtain ⟨s, s', hts, hss', hnc, hs'u⟩ := ih hlt'
      exact ⟨s, s', hts, hss', hnc, hs'u.tail hstep⟩
    · refine ⟨u, u', htu, hstep, fun hcm => ?_, Relation.ReflTransGen.refl⟩
      have := ((hc.step hstep).2.1.1 hcm)
      omega

theorem isSMax_of_reflTransGen {p : ℕ} {t t' : Triple G}
    (h : Relation.ReflTransGen (PumpRel p) t t') (hmax : IsSMax p t.1 t.2.1 t.2.2) :
    IsSMax p t'.1 t'.2.1 t'.2.2 := by
  refine ⟨?_, fun ⟨t'', s, s', ht's, hss', hnc, hs't''⟩ => hmax.2 ⟨t'', s, s', h.trans ht's, hss',
    hnc, hs't''⟩⟩
  rcases Relation.ReflTransGen.cases_tail h with heq | ⟨u, -, hstep⟩
  · exact heq ▸ hmax.1
  · exact hstep.2.1

theorem lemma41_max {p : ℕ} (hc : S4Ctx G p) {t t' : Triple G}
    (h : Relation.ReflTransGen (PumpRel p) t t') (hmax : IsSMax p t.1 t.2.1 t.2.2) :
    Nonempty (PQuot p t.2.2 ≃* PQuot p t'.2.2) ∧ IsSMax p t'.1 t'.2.1 t'.2.2 ∧
      (t.1 ≤ Subgroup.normalizer (t.2.2 : Set G) →
        t'.1 ≤ Subgroup.normalizer (t'.2.2 : Set G)) := by
  refine ⟨?_, isSMax_of_reflTransGen h hmax, ?_⟩
  · induction h with
    | refl => exact ⟨MulEquiv.refl _⟩
    | @tail u u' htu hstep ih =>
      obtain ⟨e⟩ := ih
      have hcm : CentMod p u'.2.2 u.2.1 := by
        by_contra hnc
        exact hmax.2 ⟨u', u, u', htu, hstep, hnc, Relation.ReflTransGen.refl⟩
      obtain ⟨⟨e'⟩, -⟩ := (hc.step hstep).2.2 hcm
      exact ⟨e.trans e'⟩
  · induction h with
    | refl => exact id
    | @tail u u' htu hstep ih =>
      intro hBL
      have hBuL := ih hBL
      have hcm : CentMod p u'.2.2 u.2.1 := by
        by_contra hnc
        exact hmax.2 ⟨u', u, u', htu, hstep, hnc, Relation.ReflTransGen.refl⟩
      obtain ⟨-, hJ⟩ := (hc.step hstep).2.2 hcm
      obtain ⟨-, ⟨hB', hx', -⟩, -, hdec, hx'B', -, -⟩ := hstep
      have hB'L : u'.1 ≤ Subgroup.normalizer (u.2.2 : Set G) := by
        intro b hb
        obtain ⟨v, hv, w, -, hw, rfl⟩ := hdec b hb
        exact Subgroup.mul_mem _ (hBuL hv.1) hw.1
      have hB'Cx' : u'.1 ≤ Subgroup.centralizer ({u'.2.1} : Set G) :=
        isElemAbelian_le_centralizer hB'.1 hx'B'
      intro b hb
      rw [← hJ]
      have hbC : b ∈ Subgroup.normalizer
          ((Subgroup.centralizer ({u'.2.1} : Set G) : Subgroup G) : Set G) :=
        Subgroup.le_normalizer (hB'Cx' hb)
      have hbLC : b ∈ Subgroup.normalizer
          ((u.2.2 ⊓ Subgroup.centralizer ({u'.2.1} : Set G) : Subgroup G) : Set G) := by
        have h1 := mem_normalizer_iff_gLBConj_eq.1 (hB'L hb)
        have h2 := mem_normalizer_iff_gLBConj_eq.1 hbC
        rw [mem_normalizer_iff_gLBConj_eq, gLBConj_inf, h1, h2]
      exact mem_normalizer_closureIn (mem_normalizer_glaPLayer hbLC) (mem_normalizer_glaPLayer hbC)

end CFSG.LocalAnalysis.GLTheoremA
