module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019ClassicalPartsSO
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocal
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.LocalAnalysis.GLTheoremA.CatA.S2019FixTransport
import all CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.OrthAut
import CFSG.HardMathSupport.Lang.Proving.OrthogonalFieldDescentOdd
import CFSG.SignalizerFunctorTheorem.NonLocal.OrthCent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S2019

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.HardMathSupport.Lang.Proving
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)
open CFSG.ComponentClassification (OuterAutomorphisms.congr_conj)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple (mem_E_of_pow_eq_one_omega
  mem_inner_of_mem_D_omega perfect_le_of_solvable_quotient)
open CFSG.SignalizerFunctorTheorem.CatalogBridge (NonLocalized)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusFamilyOrbit
  (orthogonal_geometry_plus_point_family_orbit)

theorem s2019FixCentralizes_of_nonLocalized_of_solvable {G : Type} [Group G] [Finite G]
    (p : ℕ) (α : MulAut G) {N J : Subgroup G} (hfix : fixSubgroup α = N) (hJN : J ≤ N)
    [(J.subgroupOf N).Normal] (hsol : Group.IsSolvable (↥N ⧸ J.subgroupOf N))
    (hJs : IsSimpleGroup ↥J) (hJn : NonLocalized J) : S2019FixCentralizes p α := by
  subst hfix
  intro L hL T hT2 hLT
  have hperf : ⁅L, L⁆ = L := CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hL
  have hLJ : L ≤ J := perfect_le_of_solvable_quotient hJN hsol hL.1 hperf
  have hsn : IsSubnormal L J := by
    have h1 := hL.2.1.inf_of_le hJN
    rwa [inf_eq_left.2 hLJ] at h1
  rcases hsn.eq_bot_or_eq_of_isSimpleGroup hJs with h | h
  · rw [h, Subgroup.commutator_bot_right]
  · subst h
    by_cases hT : T = ⊥
    · rw [hT, Subgroup.commutator_bot_left]
    · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : Group.IsNilpotent ↥T := hT2.isNilpotent
      exact absurd hLT (hJn T hT inferInstance)

private theorem le_pow_sub_four {c d : ℕ} (hc : 3 ≤ c) (hd : 6 ≤ d) : d ≤ c ^ (d - 4) := by
  have h3 : ∀ m : ℕ, 2 ≤ m → m + 4 ≤ 3 ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih =>
      rw [pow_succ]
      omega
  calc d = (d - 4) + 4 := by omega
    _ ≤ 3 ^ (d - 4) := h3 _ (by omega)
    _ ≤ c ^ (d - 4) := Nat.pow_le_pow_left hc _

section Field

variable {K : Type} [Field K] [Finite K] {k : Subfield K} {d : ℕ}
  {Q₀ : QuadraticForm k (Fin d → k)} {Q : QuadraticForm K (Fin d → K)} {σ : K ≃+* K} {p : ℕ}

theorem s2019FixCentralizes_fieldAutT (S : SubfieldSetup k Q₀ Q σ p) (h2 : (2 : K) ≠ 0)
    (hd6 : 6 ≤ d) : S2019FixCentralizes p (fieldAutT Q σ S.hQσ) := by
  have hd : 0 < d := three_le_of_totallySingular k S.hT₀
  obtain ⟨hsimp, -⟩ := matrix_simple_nonabelian hd S.hnd₀ S.hT₀
  have hJs : IsSimpleGroup ↥(subfieldDerivedImage k S.hext) :=
    (inclEquiv k S.hext hd).isSimpleGroup_congr.1 hsimp
  have hfix : fixSubgroup (fieldAutT Q σ S.hQσ) = subfieldFixedGroup k Q₀ Q :=
    Subgroup.ext fun t => fieldAutT_apply_iff S t
  have hJn := subfieldDerivedImage_normal k S.hext
  haveI := hJn
  have hquot := fixedGroup_quotient_isPGroup k S.hext S.hnd₀ S.hT₀
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := IsPGroup.isNilpotent hquot
  have hk3 : 3 ≤ Nat.card k := by
    have h2k := two_ne_zero_of_subfield k h2
    have h1 : 1 < Nat.card k := Finite.one_lt_card
    by_contra hlt
    have hk2 : Nat.card k = 2 := by omega
    apply h2k
    haveI := Fintype.ofFinite k
    have := FiniteField.cast_card_eq_zero k
    rwa [← Nat.card_eq_fintype_card, hk2, Nat.cast_ofNat] at this
  have hNL := CFSG.SignalizerFunctorTheorem.NonLocal.Orth.nonLocalized_orthogonalSubfield k
    S.hext S.hnd₀ S.hnd S.hT₀ (by omega) (le_pow_sub_four hk3 hd6)
  exact s2019FixCentralizes_of_nonLocalized_of_solvable p _ hfix (subfieldDerivedImage_le k S.hext)
    inferInstance hJs hNL

private theorem s2019FixCentralizes_of_fieldDescent {Q' : QuadraticForm K (Fin d → K)}
    {Q₀' : QuadraticForm k (Fin d → k)} (S : SubfieldSetup k Q₀' Q' σ p) (h2 : (2 : K) ≠ 0)
    (hd6 : 6 ≤ d) [Finite (matrixProjectiveDerived Q)] (U : similarityPairs Q)
    (Θ : matrixProjectiveDerived Q ≃* matrixProjectiveDerived Q') (g' : similarityPairs Q')
    (hl : g'.val.left = 1) (hr : g'.val.right = σ)
    (hΘ : ∀ x, Θ (matrixProjectiveConjugationHom Q U x) =
      matrixProjectiveConjugationHom Q' g' (Θ x)) :
    S2019FixCentralizes p (matrixProjectiveConjugationHom Q U) := by
  have hg' : g' = fieldPair Q' σ S.hQσ := Subtype.ext (SemidirectProduct.ext hl hr)
  have hcongr : MulAut.congr Θ (matrixProjectiveConjugationHom Q U) = fieldAutT Q' σ S.hQσ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : (MulAut.congr Θ (matrixProjectiveConjugationHom Q U)) x =
        Θ (matrixProjectiveConjugationHom Q U (Θ.symm x)) := rfl
    rw [h1, hΘ, MulEquiv.apply_symm_apply, hg']
    rfl
  exact s2019FixCentralizes_of_congr S.hp Θ _ (hcongr ▸ s2019FixCentralizes_fieldAutT S h2 hd6)

end Field

private theorem two_ne_zero_of_card_eq_pow {K : Type} [Field K] [Finite K] {q f : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hK : Nat.card K = q ^ f) : (2 : K) ≠ 0 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K q := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  intro h
  have h' : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff K q] at h'
  exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 h')

private theorem not_mem_D_of_not_inner {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    {d f p : ℕ} {Q : QuadraticForm K (Fin d → K)} (hg : OrthogonalGates Q f) (hp : p.Prime)
    (hp2 : p ≠ 2) (e' : G ≃* matrixProjectiveDerived Q) (β : MulAut G) (hβ : β ^ p = 1)
    (hnot : ∀ a : G, β ≠ MulAut.conj a) :
    MulAut.congr e' β ∉ (linearConjugationHom Q).range := by
  intro hD
  obtain ⟨t, ht⟩ := mem_inner_of_mem_D_omega hg hp hp2 hD (by rw [← map_pow, hβ, map_one])
  apply hnot (e'.symm t)
  have hcongr : MulAut.congr e' (MulAut.conj (e'.symm t)) = MulAut.congr e' β := by
    rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, ht]
  exact ((MulAut.congr e').injective hcongr).symm

theorem s2019FixCentralizes_omega_odd_of_not_inner {G : Type} [Group G] {n q f : ℕ}
    (hG : StatedClassicalModel G .POmegaOdd n q f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (β : MulAut G) (hβ : β ^ p = 1) (hnot : ∀ a : G, β ≠ MulAut.conj a) :
    S2019FixCentralizes p β := by
  obtain ⟨hq, -, hn3, hq2⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaOdd
    (Or.inl rfl) n q f hG K hK e
  have htop : projectivePointFamilyAut (coordinateQuadOdd n K) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaOdd
      (.inl rfl) n q f hG) K hK).2
  have h2 := two_ne_zero_of_card_eq_pow hq hq2 hK
  set e' := coordinateOddWitnessEquiv K e
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (matrixProjectiveDerived (coordinateQuadOdd n K)) := Finite.of_equiv _ e'.toEquiv
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE := mem_E_of_pow_eq_one_omega hgates hp (Or.inr htop) hβ'
  have hD := not_mem_D_of_not_inner hgates hp hp2 e' β hβ hnot
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
  refine s2019FixCentralizes_of_congr hp e' β ?_
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaOdd (Or.inl rfl)
    n q f p hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord1, -, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord1
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  exact s2019FixCentralizes_of_fieldDescent
    (subfieldSetup_odd (semilinearFixedSubfield U.val.right) hσk hp hp2 hord' hn3 h2) h2
    (by omega) U Θ g' hg'l hg'r hΘ

theorem s2019FixCentralizes_omega_plus_of_not_inner {G : Type} [Group G] {n q f : ℕ}
    (hG : StatedClassicalModel G .POmegaPlus n q f) (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hD4 : n = 4 → p ≠ 3) (β : MulAut G) (hβ : β ^ p = 1)
    (hnot : ∀ a : G, β ≠ MulAut.conj a) : S2019FixCentralizes p β := by
  obtain ⟨hq, -, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hG.2
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaPlus
    (Or.inr (Or.inl rfl)) n q f hG K hK e
  have hEA : 3 < p ∨ projectivePointFamilyAut (coordinateQuadPlus n K) = ⊤ := by
    rcases (show n = 4 ∨ 5 ≤ n by omega) with h4 | h5
    · left
      have := hD4 h4
      have := hp.two_le
      omega
    · right
      exact (orthogonal_geometry_plus_point_family_orbit hG hK e).2.2.2.2.1 h5
  have h2 := two_ne_zero_of_card_eq_pow hq hq2 hK
  set e' := coordinatePlusWitnessEquiv K e
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (matrixProjectiveDerived (coordinateQuadPlus n K)) := Finite.of_equiv _ e'.toEquiv
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE := mem_E_of_pow_eq_one_omega hgates hp hEA hβ'
  have hD := not_mem_D_of_not_inner hgates hp hp2 e' β hβ hnot
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
  refine s2019FixCentralizes_of_congr hp e' β ?_
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaPlus
    (Or.inr (Or.inl rfl)) n q f p hG hp hp2 K hK e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨-, hrest⟩ := hdesc
  obtain ⟨hord1, -, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨_, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord1
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  rw [← hUκ]
  exact s2019FixCentralizes_of_fieldDescent
    (subfieldSetup_plus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord' (by omega : 3 ≤ n))
    h2 (by omega) U Θ g' hg'l hg'r hΘ

theorem s2019FixCentralizes_omega_minus_of_not_inner {G : Type} [Group G] {n q f : ℕ}
    (hG : StatedClassicalModel G .POmegaMinus n q f) (hq2 : q ≠ 2) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (β : MulAut G) (hβ : β ^ p = 1) (hnot : ∀ a : G, β ≠ MulAut.conj a) :
    S2019FixCentralizes p β := by
  obtain ⟨hq, hf, hn4⟩ := hG.1
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hG.2
  have hn1 : 1 ≤ n := by omega
  have hgates := orthogonal_large_prime_semilinear_field_and_diagonal_gates G .POmegaMinus
    (Or.inr (Or.inr rfl)) n q f hG hn1 K hK b c hirr e
  have htop : projectivePointFamilyAut (coordinateQuadMinus n K hn1 b c) = ⊤ :=
    ((orthogonal_geometry_tail_model_point_family_invariant G .POmegaMinus (.inr rfl) n q f hG)
      hn1 K hK b c hirr).2
  have h2 := two_ne_zero_of_card_eq_pow hq hq2 hK
  set e' := coordinateMinusWitnessEquiv K hn1 b c e
  haveI : Finite G := Finite.of_equiv _ e.toEquiv.symm
  haveI : Finite (matrixProjectiveDerived (coordinateQuadMinus n K hn1 b c)) :=
    Finite.of_equiv _ e'.toEquiv
  have hβ' : MulAut.congr e' β ^ p = 1 := by rw [← map_pow, hβ, map_one]
  have hE := mem_E_of_pow_eq_one_omega hgates hp (Or.inr htop) hβ'
  have hD := not_mem_D_of_not_inner hgates hp hp2 e' β hβ hnot
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (MulAut.congr e' β) = p := orderOf_eq_prime hβ' fun h => hD (h ▸ one_mem _)
  refine s2019FixCentralizes_of_congr hp e' β ?_
  have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' G .POmegaMinus
    (Or.inr (Or.inr rfl)) n q f p hG hp hp2 hn1 K hK b c hirr e _ hE hD hord
  obtain ⟨g, hgE⟩ := hE
  obtain ⟨hpf, hrest⟩ := hdesc
  obtain ⟨hord1, hcard, U, _, _, hUκ, hUr, _, hDisp⟩ := hrest g.val.right ⟨g, hgE, rfl⟩
  obtain ⟨b', c', hirr', _, _, -, -, hT'⟩ := hDisp
  obtain ⟨_, _, -, -, -, Θ, -, g', hg'l, hg'r, hΘ⟩ := hT'
  have hord' : orderOf U.val.right = p := by rw [hUr]; exact hord1
  have hcard' : Nat.card (semilinearFixedSubfield U.val.right) = q ^ (f / p) := by
    rw [hUr]
    exact hcard
  have hσk : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x := fun x =>
    RingHom.mem_eqLocusField
  obtain ⟨m, hm⟩ := hpf
  have hdiv : f / p = m := by rw [hm]; exact Nat.mul_div_cancel_left m hp.pos
  rw [hdiv] at hcard'
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      omega
    · exact h
  have hK' : Nat.card K = q ^ (m * p) := by rw [hK, hm, mul_comm]
  have hdeg := finrank_subfield_eq (semilinearFixedSubfield U.val.right) hq hm1 hcard' hK'
  rw [← hUκ]
  exact s2019FixCentralizes_of_fieldDescent
    (subfieldSetup_minus (semilinearFixedSubfield U.val.right) hσk hp hp2 hord' hn4 hdeg b' c'
      hirr') h2 (by omega) U Θ g' hg'l hg'r hΘ

theorem s2019OrthOuter (Qs : ℕ → Prop) : S2019OrthOuter Qs := by
  intro p q hp hp2 hq hq2 hqp _ t ht G _ n f hG hD4 β hβ hnot
  rcases ht with rfl | rfl | rfl
  · exact s2019FixCentralizes_omega_odd_of_not_inner hG hp hp2 β hβ hnot
  · exact s2019FixCentralizes_omega_plus_of_not_inner hG hq2 hp hp2 (hD4 rfl) β hβ hnot
  · exact s2019FixCentralizes_omega_minus_of_not_inner hG hq2 hp hp2 β hβ hnot

end CFSG.LocalAnalysis.GLTheoremA.S2019
