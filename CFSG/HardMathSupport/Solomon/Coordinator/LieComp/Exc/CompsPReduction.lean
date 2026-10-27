module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPInner
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPTypeA
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterDispatch

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

theorem kacCount_F4_B2 : kacCount Tag.F4 ![2, 3, 4, 2]
    (([2, 3] : List ℕ).map (idxNode (r := Tag.F4.rank))).toFinset = 8 := by
  decide +kernel

section Excl


theorem not_comp_eq_B4_F4_odd {p : ℕ} (hp2 : p % 2 = 1) {μ : Fin Tag.F4.rank → ℤ}
    (hμ : kacF4.IsNormal p μ) {x : Option (Fin Tag.F4.rank)}
    (hc : kacF4.comp p μ x = {y | nodeIdx y ∈ ([0, 1, 2, 3] : List ℕ)}) : False := by
  have hmem : ∀ y : Option (Fin Tag.F4.rank), nodeIdx y ∈ ([0, 1, 2, 3] : List ℕ) →
      kacF4.IsZ p μ y := fun y hy => by
    have : y ∈ kacF4.comp p μ x := by rw [hc]; exact hy
    exact this.1
  have hz0 : kacF4.IsZ p μ none := hmem none (by decide)
  have hz1 : kacF4.IsZ p μ (some 0) := hmem (some 0) (by decide)
  have hz2 : kacF4.IsZ p μ (some 1) := hmem (some 1) (by decide)
  have hz3 : kacF4.IsZ p μ (some 2) := hmem (some 2) (by decide)
  change kacF4.θ ⬝ᵥ μ = ((p : ℕ) : ℤ) at hz0
  change μ 0 = 0 at hz1
  change μ 1 = 0 at hz2
  change μ 2 = 0 at hz3
  rw [f4_theta_dot, hz1, hz2, hz3] at hz0
  omega

end Excl

section Reduction


theorem false_of_g2Class_nonAP {p : ℕ} (hp : p.Prime) {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup Tag.G2 L p₀) (hpL : ((p : ℕ) : L) ≠ 0) {a : Fin Tag.G2.rank → Lˣ}
    (hTp : rootDiagUnit Tag.G2 a ^ p = 1) (h1 : rootDiagUnit Tag.G2 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) : False := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacG2 facts_G2 g2_tree g2_adj g2_check g2_lt g2_card S hp hpL hTp i
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.G2 ![2, 3]
      (c.map (idxNode (r := Tag.G2.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hnonA
    exact hnonA
  have hc12 := g2_nonA_cases c hc hlen hnonA'
  subst hc12
  apply h1
  refine eq_one_of_simple_mem_class i (fun j => ?_)
  rw [hroots, rootsOf_eq_parabolicRoots kacG2 facts_G2 (J := Set.univ) (by decide)
    (fun j => by simp only [Set.mem_univ, iff_true]; revert j; decide)]
  exact ⟨v⁻¹ • Pi.single j 1, ⟨IsRoot.smul (isRoot_single _ j) v⁻¹, fun i hi =>
    (hi (Set.mem_univ i)).elim⟩, smul_inv_smul v _⟩

theorem f4_nonA_casesP {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) (hpL : ((p : ℕ) : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ p = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    (compRank (componentRoots (rootCharHom a) i) = 2 ∧
      (componentRoots (rootCharHom a) i).ncard = 8) ∨
    ∃ (v : WeylGroup Tag.F4) (J : Set (Fin (Tag.rank .F4))), (J = f4LeviB3 ∨ J = f4LeviC3) ∧
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J ∧
      compRank (componentRoots (rootCharHom a) i) = 3 ∧
      (componentRoots (rootCharHom a) i).ncard = 18 := by
  classical
  obtain ⟨v, μ, x, c, hμ, hc, hcomp, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S hp hpL hTp i
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2]
      (c.map (idxNode (r := Tag.F4.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hnonA
    exact hnonA
  rcases f4_nonA_cases c hc hlen hnonA' with rfl | rfl | rfl | rfl | rfl
  · left
    exact ⟨by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_B2⟩
  · right
    refine ⟨v, f4LeviB3, Or.inl rfl, ?_, by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_B3⟩
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviB3) (by decide)
      (fun j => by rw [mem_f4LeviB3]; revert j; decide)]
  · right
    refine ⟨v, f4LeviC3, Or.inr rfl, ?_, by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_C3⟩
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviC3) (by decide)
      (fun j => by rw [mem_f4LeviC3]; revert j; decide)]
  · exact (not_comp_eq_B4_F4_odd hp2 hμ hcomp).elim
  · exfalso
    apply h1
    refine eq_one_of_simple_mem_class i (fun j => ?_)
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := Set.univ) (by decide)
      (fun j => by simp only [Set.mem_univ, iff_true]; revert j; decide)]
    exact ⟨v⁻¹ • Pi.single j 1, ⟨IsRoot.smul (isRoot_single _ j) v⁻¹, fun i hi =>
      (hi (Set.mem_univ i)).elim⟩, smul_inv_smul v _⟩

@[expose] def ExcRationalLieTypesOuterDP (p : ℕ) : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = 2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1)) →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def ExcRationalLieTypesF4P (p : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.F4 L p₀)
    (a : Fin Tag.F4.rank → Lˣ), rootDiagUnit Tag.F4 a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
    rootDiagUnit Tag.F4 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) →
      twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      ((compRank (componentRoots (rootCharHom a) i) = 2 ∧
          (componentRoots (rootCharHom a) i).ncard = 8) ∨
        (compRank (componentRoots (rootCharHom a) i) = 3 ∧
          (componentRoots (rootCharHom a) i).ncard = 18 ∧
          ¬ (4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        LieCompData (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem excRationalLieTypesP_of_residuals {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hD : ExcRationalLieTypesOuterDP p) (hF : ExcRationalLieTypesF4P p) :
    ExcRationalLieTypesP p := by
  intro τ L _ _ p₀ S a hT hap h1 i hq
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  by_cases hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)
  · exact lieCompData_of_typeA S hp hT hap h1 i hA hq
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  ·
    cases τ with
    | G2 => exact (false_of_g2Class_nonAP hp S hpL hTp h1 i hA).elim
    | F4 =>
      rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hA with hB2 | ⟨v, J, hJ, hroots, hr3, hn18⟩
      · exact hF L p₀ S a hT hap h1 i hA hinner (Or.inl hB2) hq
      · by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
        · exact (rationalLieType_of_f4Levi_class S hT i v hJ hroots hinner hQ).lieCompData
        · exact hF L p₀ S a hT hap h1 i hA hinner (Or.inr ⟨hr3, hn18, hQ⟩) hq
    | D4 => exact (rationalLieType_of_inner_nonA_D4 S hp hpL hT hTp i hA hinner).lieCompData
    | E6 => exact (rationalLieType_of_inner_nonA_E6 S hp hpL hT hTp i hA hinner).lieCompData
    | E7 => exact (rationalLieType_of_inner_nonA_E7 S hp hpL hT hTp i hA hinner).lieCompData
    | E8 => exact (rationalLieType_of_inner_nonA_E8 S hp hpL hT hTp i hA hinner).lieCompData
  ·
    cases τ with
    | G2 => exact (false_of_g2Class_nonAP hp S hpL hTp h1 i hA).elim
    | F4 =>
      rcases f4_nonA_casesP hp hp2' S hpL hTp h1 i hA with ⟨hr, hn⟩ | ⟨v, J, -, -, hr, hn⟩
      · exact (hinner (twistInner_of_shape S hT i 2 8 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
      · exact (hinner (twistInner_of_shape S hT i 3 18 hr hn (by omega) (by omega) (by omega)
          (by omega))).elim
    | D4 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt d4_card S hp hpL hTp i
      have hshape := d4_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD'
      · exact (hA hA').elim
      · exact (hD _ L p₀ S a hT hap h1 i hD' hinner hq).lieCompData
    | E6 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
      have hshape := e6_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE
      · exact (hA hA').elim
      · exact (hD _ L p₀ S a hT hap h1 i hD' hinner hq).lieCompData
      · exact (false_of_e6Class_E S hp hpL hTp h1 i hE.1 hE.2).elim
    | E7 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
      have hshape := e7_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE
      · exact (hA hA').elim
      · exact (hD _ L p₀ S a hT hap h1 i hD' hinner hq).lieCompData
      · exact (rationalLieType_of_outer_E7 S hp hpL hT hTp i hE.1 hE.2 hinner).lieCompData
    | E8 =>
      obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
        exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
      have hshape := e8_shape c hc hlen
      rw [← hncard, ← hrank] at hshape
      rcases hshape with hA' | hD' | hE
      · exact (hA hA').elim
      · exact (hD _ L p₀ S a hT hap h1 i hD' hinner hq).lieCompData
      · exact (rationalLieType_of_outer_E8 S hp hpL hT hTp i hE.1 hE.2 hinner).lieCompData

end Reduction

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
