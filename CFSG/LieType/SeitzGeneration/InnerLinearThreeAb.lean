module

public import CFSG.LieType.SeitzGeneration.LinearPlaneFixed
public import CFSG.LieType.SeitzGeneration.SpFourScope
public import CFSG.LieType.Steinberg.CentralExt.LinearPerfect

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem planeGen_inner_A_three_ab {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) (hq3 : 3 ≠ q.p)
    (hlift : ¬ (3 ∣ q.card - 1 ∧ 3 ∣ m + 1))
    {E : Subgroup (MulAut (Cat ⟨.A m q, hv⟩))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hinner : InnerPlane ⟨.A m q, hv⟩ 3 E) : PlaneGen E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
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
  have h3 : (3 : GaloisField q.p q.exponent) ≠ 0 :=
    three_ne_zero_of_card q.prime_p (by rw [hcardF, TauCeti.PrimePower.card_def]) (Ne.symm hq3)
  refine planeGen_of_inner_model (conj_injective_of_mulEquiv e hinjP) e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  have hZdvd := CFSG.LieType.Steinberg.card_center_specialLinearGroup_dvd (by omega : 1 ≤ m + 1)
    (GaloisField q.p q.exponent)
  refine closure_centralizers_psl_three_ab (by omega) h3 (fun hd => hlift ⟨?_, ?_⟩) E₁
    (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE₁.2
    (by simpa using hcard₁)
  · have := (hd.trans hZdvd).trans (Nat.gcd_dvd_right _ _)
    rwa [hcardF] at this
  · exact (hd.trans hZdvd).trans (Nat.gcd_dvd_left _ _)

theorem seitzInnerLinearThreeAb :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ p = 3 ∧ IsLinearIndex d.1 ∧ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, ⟨m, q, hd⟩, hlift⟩
  subst hd hp3
  exact planeGen_inner_A_three_ab hv (by simpa using hpd) hlift hE hc hinner

end CFSG.LieType.SeitzGeneration
