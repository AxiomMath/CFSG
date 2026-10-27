module

public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.LieType.SeitzGeneration.NonabLift
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Adapters.LinearCatalog

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open CFSG.AGLEmbeddingD2

@[expose] def LinearHeisenbergPlanes : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (p : ℕ), p.Prime → 5 ≤ p → p ∣ Nat.card F - 1 →
    ∀ E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin p) F),
      (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
      (∃ x y : Matrix.SpecialLinearGroup (Fin p) F, toPSL x ∈ E ∧ toPSL y ∈ E ∧ x * y ≠ y * x) →
      Subgroup.closure {k : Matrix.ProjectiveSpecialLinearGroup (Fin p) F |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤

section Field

variable {F : Type*} [Field F] [Finite F]

theorem natCast_ne_zero_of_dvd_card_sub_one {p : ℕ} (hp : p.Prime) (h : p ∣ Nat.card F - 1) :
    (p : F) ≠ 0 := by
  intro h0
  have : Fact p.Prime := ⟨hp⟩
  have hchar : CharP F p := (CharP.charP_iff_prime_eq_zero hp).2 h0
  have := Fintype.ofFinite F
  obtain ⟨k, -, hk⟩ := FiniteField.card F p
  have hpq : p ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hk]
    exact dvd_pow_self p k.ne_zero
  have hq : 0 < Nat.card F := Nat.card_pos
  have h1 : p ∣ 1 := by
    have := Nat.dvd_sub hpq h
    rwa [Nat.sub_sub_self (by omega : 1 ≤ Nat.card F)] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 h1)

theorem exists_primitiveRoot_of_dvd_card_sub_one {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card F - 1) : ∃ ζ : F, IsPrimitiveRoot ζ p := by
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  exact ⟨(x : F), IsPrimitiveRoot.coe_units_iff.mpr (hx ▸ IsPrimitiveRoot.orderOf x)⟩

theorem natCast_card_center_ne_zero {n : ℕ} (hn : 0 < n) :
    (Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) : F) ≠ 0 := by
  intro h
  have hr : Fact (ringChar F).Prime := ⟨CharP.prime_ringChar F⟩
  have hdvd : ringChar F ∣ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) :=
    (CharP.cast_eq_zero_iff F (ringChar F) _).1 h
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (ringChar F) hdvd
  have hz1 : z ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hz
    exact hr.out.one_lt.ne hz
  obtain ⟨r, hr0, hrz⟩ := exists_scalar_of_mem_center hn z.2
  have hzp : (z : Matrix.SpecialLinearGroup (Fin n) F) ^ ringChar F = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one]
    rfl
  have h2 := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hzp
  simp only [Matrix.SpecialLinearGroup.coe_pow, hrz, smul_pow, one_pow,
    Matrix.SpecialLinearGroup.coe_one] at h2
  have h3 : r ^ ringChar F = 1 := by
    have := congrFun (congrFun h2 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this
  have h4 : (r - 1) ^ ringChar F = 0 := by rw [sub_pow_char, h3, one_pow, sub_self]
  have h5 : r = 1 := sub_eq_zero.1 (pow_eq_zero_iff hr.out.ne_zero |>.1 h4)
  exact hz1 (Subtype.ext (Subtype.ext (by rw [hrz, h5, one_smul]; rfl)))

end Field

theorem closure_centralizers_psl_nonab (hH : LinearHeisenbergPlanes) {F : Type} [Field F]
    [Finite F] {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card F - 1) (hpn : p ∣ n)
    (hn : 0 < n) (E : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hexp : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : Matrix.ProjectiveSpecialLinearGroup (Fin n) F |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have hpF := natCast_ne_zero_of_dvd_card_sub_one hp hpq
  by_cases hred : ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧
      ∀ x : Matrix.SpecialLinearGroup (Fin n) F, toPSL x ∈ E →
        ∀ w ∈ W, (x : Matrix (Fin n) (Fin n) F).mulVec w ∈ W
  · obtain ⟨W, hW0, hWt, hWE⟩ := hred
    exact closure_centralizers_psl_of_reducible hp hpF (natCast_card_center_ne_zero hn) E hcomm
      hexp hcard hW0 hWt hWE
  · push Not at hred
    obtain ⟨hnp, hnc⟩ := irreducible_plane_dim hp (by omega) hn hpn hpq
      (exists_primitiveRoot_of_dvd_card_sub_one hp hpq) E hcomm hexp hcard
      (fun W hW => by
        by_contra h
        push Not at h
        obtain ⟨x, hx, w, hw, hnot⟩ := hred W h.1 h.2
        exact hnot (hW x hx w hw))
    subst hnp
    exact hH F n hp hp5 hpq E hcomm hexp hcard hnc

theorem planeGen_inner_A_nonab (hH : LinearHeisenbergPlanes) {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hlift : p ∣ q.card - 1 ∧ p ∣ m + 1)
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
  exact closure_centralizers_psl_nonab hH hp hp5 (by rw [hcardF]; exact hlift.1) hlift.2
    (by omega) E₁
    (fun x hx y hy => congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)) hE₁.2 hcard₁

theorem seitzInnerLinearNonab (hH : LinearHeisenbergPlanes) :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ 5 ≤ p ∧ IsLinearIndex d.1 ∧ ¬ CentralPrimeFree p d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hp5, ⟨m, q, hd⟩, hlift⟩
  subst hd
  exact planeGen_inner_A_nonab hH hv hp hp5 (by simpa [CentralPrimeFree] using hlift) hE hc hinner

end CFSG.LieType.SeitzGeneration
