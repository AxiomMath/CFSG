module

public import CFSG.HardMathSupport.Solomon.Coordinator.Generation228
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.CyclicCatalog
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartOne.TCB.Final

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open

theorem pRank_mulAut_le_one_of_pSubgroupsCyclic {p : ℕ} (hp : p.Prime) {K : Type} [Group K]
    [Finite K] (h : CFSG.SignalizerFunctorTheorem.CatalogBridge.PSubgroupsCyclic p K) :
    CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ≤ 1 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hEel, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := p) hp.one_lt (⊤ : Subgroup (MulAut K))
  have hEp : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hEel.2 x x.2)⟩
  have hEcyc : IsCyclic E := h E hEp
  obtain ⟨g, hg⟩ := hEcyc.exists_generator
  have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hEel.2 g g.2)
  have hdvd : p ^ CFSG.Open.pRank p (⊤ : Subgroup (MulAut K)) ∣ p ^ 1 := by
    rw [← hEcard, ← hord, pow_one]
    exact orderOf_dvd_of_pow_eq_one hgp
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd

theorem i_7_13_1_pPrime_of (hbridge : CFSG.RankThree.PartOne.TauCetiCatalogBridge)
    (hcyc : ∀ {p : ℕ}, p.Prime → ∀ {X : Type} [Group X] [Finite X], IsSimpleGroup X →
      (∃ a b : X, a * b ≠ b * a) → CFSG.Blueprint.Catalog X → Nat.Coprime p (Nat.card X) →
        CFSG.SignalizerFunctorTheorem.CatalogBridge.PSubgroupsCyclic p X) :
    I_7_13_1_pPrime := by
  intro p hp _ K _ _ hsimple hnonab hcat hcop
  have := hsimple
  have hK : CFSG.Blueprint.Catalog K := hbridge K hnonab hcat
  exact pRank_mulAut_le_one_of_pSubgroupsCyclic hp
    (hcyc hp hsimple hnonab hK ((Nat.Prime.coprime_iff_not_dvd hp).2 hcop))

theorem i_7_13_1_pPrime_holds :
    I_7_13_1_pPrime :=
  i_7_13_1_pPrime_of CFSG.RankThree.PartOne.TCB.tauCetiCatalogBridge
    fun hp _ _ _ hs hn hc hcop =>
      CFSG.SignalizerFunctorTheorem.CatalogBridge.catalog_pSubgroupsCyclic
        CFSG.RankThree.PartOne.SPOR.sporadicHS_outer_le_two
        CFSG.RankThree.PartOne.SPOR.sporadicOuterOrderLeTwoSimple_holds hp hs hn hc hcop

end CFSG.HardMathSupport.Solomon.Coordinator
