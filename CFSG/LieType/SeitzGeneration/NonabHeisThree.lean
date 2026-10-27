module

public import CFSG.LieType.SeitzGeneration.NonabHeisThreeGen
public import CFSG.LieType.SeitzGeneration.NonabLinear

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

theorem closure_centralizers_psl_three {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hpq : 3 ∣ Nat.card F - 1) (hpn : 3 ∣ n) (hn : 0 < n) (h4 : n = 3 → 4 < Nat.card F)
    (E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ 3 = 1)
    (hcard : Nat.card E = 3 ^ 2) :
    Subgroup.closure {k : Matrix.ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  have hpF := natCast_ne_zero_of_dvd_card_sub_one hp hpq
  by_cases hred : ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x : Matrix.SpecialLinearGroup (Fin n) F, toPSL x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W
  · obtain ⟨W, hW0, hWt, hWE⟩ := hred
    exact closure_centralizers_psl_of_reducible hp hpF (natCast_card_center_ne_zero hn) E hcomm
      hexp hcard hW0 hWt hWE
  · push Not at hred
    obtain ⟨hnp, hnc⟩ := irreducible_plane_dim hp (by norm_num) hn hpn hpq
      (exists_primitiveRoot_of_dvd_card_sub_one hp hpq) E hcomm hexp hcard
      (fun W hW => by
        by_contra h
        push Not at h
        obtain ⟨x, hx, w, hw, hnot⟩ := hred W h.1 h.2
        exact hnot (hW x hx w hw))
    subst hnp
    exact closure_centralizers_psl_nonab_three (h4 rfl) E hcomm hexp hnc

theorem planeGen_inner_A_three {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) (hlift : 3 ∣ q.card - 1 ∧ 3 ∣ m + 1)
    (h4 : m = 2 → q.card ≠ 4) {E : Subgroup (MulAut (Cat ⟨.A m q, hv⟩))}
    (hE : IsElemAbelian 3 E) (hc : Nat.card E = 3 ^ 2) (hinner : InnerPlane ⟨.A m q, hv⟩ 3 E) :
    PlaneGen E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hm1 : 1 ≤ m := hrange.1
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hq1 : 1 < q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_lt_pow q.exponent_pos.ne' q.prime_p.one_lt
  have hfour : 3 ≤ m + 1 ∨ ∃ s : Finset (GaloisField q.p q.exponent), s.card = 4 := by
    by_cases h3 : 3 ≤ m + 1
    · exact Or.inl h3
    · right
      have h4' : 4 ≤ q.card := hrange.2 (by omega)
      have : Fintype (GaloisField q.p q.exponent) := Fintype.ofFinite _
      obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ :
        Finset (GaloisField q.p q.exponent))) (n := 4)
        (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcardF]; exact h4')
      exact ⟨s, hs⟩
  let e := CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv
  have hsimple := (CFSG.LinearGroups.linear_projective_simple (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).2.1
  have hperf := (CFSG.LinearGroups.linear_projective_perfect (n := m + 1)
    (K := GaloisField q.p q.exponent) (by omega) hfour).commutator_eq_top
  have hinjP := conj_injective_of_simple_perfect hperf
  refine planeGen_of_inner_model (conj_injective_of_mulEquiv e hinjP) e ?_ hE hc hinner
  intro E₁ hE₁ hcard₁
  exact closure_centralizers_psl_three (by rw [hcardF]; exact hlift.1) hlift.2 (by omega)
    (fun hm => by
      have h2 : m = 2 := by omega
      rw [hcardF]
      have h5 := h4 h2
      obtain ⟨k, hk⟩ := hlift.1
      omega) E₁
    (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE₁.2 hcard₁

theorem seitzInnerLinearThree :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ p = 3 ∧ IsLinearIndex d.1 ∧ ¬ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp3, ⟨m, q, hd⟩, hlift⟩
  subst hd hp3
  refine planeGen_inner_A_three hv (by simpa [CentralPrimeFree] using hlift) ?_ hE hc hinner
  rintro rfl h4card
  have hp2 : q.p = 2 := by
    have hdvd : q.p ∣ 2 ^ 2 := by
      have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
      rw [← TauCeti.PrimePower.card_def, h4card] at h1
      simpa using h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hdvd)
  have he2 : q.exponent = 2 := by
    have h1 : 2 ^ q.exponent = 2 ^ 2 := by
      have h2 := h4card
      rw [TauCeti.PrimePower.card_def, hp2] at h2
      rw [h2]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h1
  exact hex (Or.inl ⟨rfl, Or.inr (Or.inl ⟨q, hp2, he2, rfl⟩)⟩)

end CFSG.LieType.SeitzGeneration
