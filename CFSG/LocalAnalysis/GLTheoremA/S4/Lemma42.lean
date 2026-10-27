module

public import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma41

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

theorem reflTransGen_of_pumpLt {p : ℕ} {t t' : Triple G} (h : PumpLt p t t') :
    Relation.ReflTransGen (PumpRel p) t t' := by
  obtain ⟨s, s', hts, hss', -, hs't'⟩ := h
  exact (hts.tail hss').trans hs't'

theorem exists_isSMax_reflTransGen {p : ℕ} (hc : S4Ctx G p) {t : Triple G}
    (ht : IsSTriple p t.1 t.2.1 t.2.2) :
    ∃ t' : Triple G, Relation.ReflTransGen (PumpRel p) t t' ∧ IsSMax p t'.1 t'.2.1 t'.2.2 := by
  classical
  obtain ⟨t', ht', hmax⟩ := Set.exists_max_image {t' : Triple G | Relation.ReflTransGen (PumpRel p) t t'}
    (fun t' => Nat.card (PQuot p t'.2.2)) (Set.toFinite _) ⟨t, Relation.ReflTransGen.refl⟩
  refine ⟨t', ht', ?_, fun ⟨t'', hlt⟩ => ?_⟩
  · rcases Relation.ReflTransGen.cases_tail ht' with heq | ⟨u, -, hstep⟩
    · exact heq ▸ ht
    · exact hstep.2.1
  · have h1 : Nat.card (PQuot p t'.2.2) < Nat.card (PQuot p t''.2.2) := card_lt_of_pumpLt hc hlt
    have h2 := hmax t'' (ht'.trans (reflTransGen_of_pumpLt hlt))
    omega

end CFSG.LocalAnalysis.GLTheoremA
