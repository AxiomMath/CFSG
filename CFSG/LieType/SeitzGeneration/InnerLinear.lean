module

public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.RankThree.PartOne.CTP.SeitzLinear

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem planeGen_inner_A {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ≠ q.p) (hlift : ¬ (p ∣ q.card - 1 ∧ p ∣ m + 1))
    {E : Subgroup (MulAut (Cat ⟨.A m q, hv⟩))} (hE : IsElemAbelian p E)
    (hc : Nat.card E = p ^ 2) (hinner : InnerPlane ⟨.A m q, hv⟩ p E) : PlaneGen E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact p.Prime := ⟨hp⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm1 : 1 ≤ m := hrange.1
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hfour : 3 ≤ m + 1 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    by_cases h3 : 3 ≤ m + 1
    · exact Or.inl h3
    · right
      have h4 : 4 ≤ q.card := hrange.2 (by omega)
      have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
        Finset (GaloisField q.p q.exponent))) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h4)
      exact ⟨s, hs⟩
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).2.1
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).commutator_eq_top
  have hinjP := conj_injective_of_simple_perfect hperf
  refine planeGen_of_inner_model (conj_injective_of_mulEquiv e hinjP) e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have : CFSG.IsElementaryAbelian p E₁ :=
    (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian p E₁).mpr hE₁
  refine CFSG.RankThree.PartOne.CTP.closure_centralizers_psl_elementary (by omega) hp hp5 ?_ ?_
    E₁ hcard₁
  · rw [hcardF, TauCeti.PrimePower.card_def]
    intro hdvd
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp q.prime_p).mp (hp.dvd_of_dvd_pow hdvd))
  · intro hdvd hdvdm
    exact hlift ⟨by rwa [hcardF] at hdvd, hdvdm⟩

theorem seitzInnerLinear :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ 5 ≤ p ∧ IsLinearIndex d.1 ∧ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, ⟨m, q, hd⟩, hlift⟩
  subst hd
  exact planeGen_inner_A hv hp hp5 (by simpa using hpd) hlift hE hc hinner

end CFSG.LieType.SeitzGeneration
