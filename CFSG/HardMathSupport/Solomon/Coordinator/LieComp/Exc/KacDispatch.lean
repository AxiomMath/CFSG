module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDAll
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacEAll
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacF4
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.TypeA
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUG2
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

theorem d4_shape_raw : ∀ c ∈ d4Conn, c.length ≤ 4 →
    (1 ≤ c.length ∧ kacCount Tag.D4 ![1, 1, 2, 1] (c.map (idxNode (r := Tag.D4.rank))).toFinset =
      c.length * (c.length + 1)) ∨
    (4 ≤ c.length ∧ kacCount Tag.D4 ![1, 1, 2, 1] (c.map (idxNode (r := Tag.D4.rank))).toFinset =
      2 * c.length * (c.length - 1)) := by
  decide +kernel

theorem e6_shape_raw : ∀ c ∈ e6Conn, c.length ≤ 6 →
    (1 ≤ c.length ∧ kacCount Tag.E6 ![1, 2, 2, 3, 2, 1] (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      c.length * (c.length + 1)) ∨
    (4 ≤ c.length ∧ kacCount Tag.E6 ![1, 2, 2, 3, 2, 1] (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      2 * c.length * (c.length - 1)) ∨
    (6 ≤ c.length ∧ kacCount Tag.E6 ![1, 2, 2, 3, 2, 1] (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      eRootCount c.length) := by
  decide +kernel

theorem e7_shape_raw : ∀ c ∈ e7Conn, c.length ≤ 7 →
    (1 ≤ c.length ∧ kacCount Tag.E7 ![2, 2, 3, 4, 3, 2, 1] (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      c.length * (c.length + 1)) ∨
    (4 ≤ c.length ∧ kacCount Tag.E7 ![2, 2, 3, 4, 3, 2, 1] (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      2 * c.length * (c.length - 1)) ∨
    (6 ≤ c.length ∧ kacCount Tag.E7 ![2, 2, 3, 4, 3, 2, 1] (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      eRootCount c.length) := by
  decide +kernel

theorem e8_shape_raw : ∀ c ∈ e8Conn, c.length ≤ 8 →
    (1 ≤ c.length ∧ kacCount Tag.E8 ![2, 3, 4, 6, 5, 4, 3, 2] (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      c.length * (c.length + 1)) ∨
    (4 ≤ c.length ∧ kacCount Tag.E8 ![2, 3, 4, 6, 5, 4, 3, 2] (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      2 * c.length * (c.length - 1)) ∨
    (6 ≤ c.length ∧ kacCount Tag.E8 ![2, 3, 4, 6, 5, 4, 3, 2] (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      eRootCount c.length) := by
  decide +kernel

theorem g2_nonA_cases : ∀ c ∈ g2Conn, c.length ≤ 2 →
    ¬ (1 ≤ c.length ∧ kacCount Tag.G2 ![2, 3] (c.map (idxNode (r := Tag.G2.rank))).toFinset =
      c.length * (c.length + 1)) → c = [1, 2] := by
  decide +kernel

section Dispatch



theorem d4_shape : ∀ c ∈ d4Conn, c.length ≤ 4 →
    (1 ≤ c.length ∧ kacCount Tag.D4 kacD4.θ (c.map (idxNode (r := Tag.D4.rank))).toFinset =
      c.length * (c.length + 1)) ∨
    (4 ≤ c.length ∧ kacCount Tag.D4 kacD4.θ (c.map (idxNode (r := Tag.D4.rank))).toFinset =
      2 * c.length * (c.length - 1)) :=
  d4_shape_raw

theorem rationalLieType_of_inner_nonA_D4 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.D4 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.D4.rank → Lˣ} (hTor : rootDiagUnit Tag.D4 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.D4 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.D4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt d4_card S hp hpL hTp i
  have hshape := d4_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD
  · exact (hnonA hA).elim
  · exact rationalLieType_of_dClass_D4 S hp hpL hTor hTp i hD.1 hD.2 hinner

theorem e6_shape : ∀ c ∈ e6Conn, c.length ≤ 6 →
    (1 ≤ c.length ∧ kacCount Tag.E6 kacE6.θ (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      c.length * (c.length + 1)) ∨
    (4 ≤ c.length ∧ kacCount Tag.E6 kacE6.θ (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      2 * c.length * (c.length - 1)) ∨
    (6 ≤ c.length ∧ kacCount Tag.E6 kacE6.θ (c.map (idxNode (r := Tag.E6.rank))).toFinset =
      eRootCount c.length) :=
  e6_shape_raw

theorem rationalLieType_of_inner_nonA_E6 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTor : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E6 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hshape := e6_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact rationalLieType_of_dClass_E6 S hp hpL hTor hTp i hD.1 hD.2 hinner
  · exact rationalLieType_of_eClass_E6 S hp hpL hTor hTp i hE.1 hE.2 hinner

theorem e7_shape : ∀ c ∈ e7Conn, c.length ≤ 7 →
    (1 ≤ c.length ∧ kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      c.length * (c.length + 1)) ∨
    (4 ≤ c.length ∧ kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      2 * c.length * (c.length - 1)) ∨
    (6 ≤ c.length ∧ kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset =
      eRootCount c.length) :=
  e7_shape_raw

theorem rationalLieType_of_inner_nonA_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL hTp i
  have hshape := e7_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact rationalLieType_of_dClass_E7 S hp hpL hTor hTp i hD.1 hD.2 hinner
  · exact rationalLieType_of_eClass_E7 S hp hpL hTor hTp i hE.1 hE.2 hinner

theorem e8_shape : ∀ c ∈ e8Conn, c.length ≤ 8 →
    (1 ≤ c.length ∧ kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      c.length * (c.length + 1)) ∨
    (4 ≤ c.length ∧ kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      2 * c.length * (c.length - 1)) ∨
    (6 ≤ c.length ∧ kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset =
      eRootCount c.length) :=
  e8_shape_raw

theorem rationalLieType_of_inner_nonA_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, -, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL hTp i
  have hshape := e8_shape c hc hlen
  rw [← hncard, ← hrank] at hshape
  rcases hshape with hA | hD | hE
  · exact (hnonA hA).elim
  · exact rationalLieType_of_dClass_E8 S hp hpL hTor hTp i hD.1 hD.2 hinner
  · exact rationalLieType_of_eClass_E8 S hp hpL hTor hTp i hE.1 hE.2 hinner

theorem false_of_g2Class_nonA {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.G2 L p₀) (hpL : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.G2.rank → Lˣ}
    (hT3 : rootDiagUnit Tag.G2 a ^ 3 = 1) (h1 : rootDiagUnit Tag.G2 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) : False := by
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacG2 facts_G2 g2_tree g2_adj g2_check g2_lt g2_card S Nat.prime_three
      hpL hT3 i
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

end Dispatch


section Residuals


@[expose] def ExcRationalLieTypesOuter : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def ExcRationalLieTypesF4Two : Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup Tag.F4 L p₀)
    (a : Fin Tag.F4.rank → Lˣ), rootDiagUnit Tag.F4 a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    rootDiagUnit Tag.F4 a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
          (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
            (compRank (componentRoots (rootCharHom a) i) + 1)) →
      twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      ¬ (4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)

end Residuals

section Reduction


theorem excRationalLieTypesNonA_of_residuals (hOuter : ExcRationalLieTypesOuter)
    (hF2 : ExcRationalLieTypesF4Two) : ExcRationalLieTypesNonA := by
  intro τ L _ _ p₀ S a hT hap h1 i hnonA hqs
  classical
  by_cases hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · have hℓ3 : ringChar L ≠ 3 := ringChar_ne_three_of_pow_three hap h1
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    have h3L : ((3 : ℕ) : L) ≠ 0 := by
      intro h
      have hd : ringChar L ∣ 3 := (ringChar.spec L 3).1 (by exact_mod_cast h)
      rcases (Nat.dvd_prime Nat.prime_three).1 hd with h' | h'
      · exact CharP.ringChar_ne_one h'
      · exact hℓ3 h'
    cases τ with
    | G2 => exact (false_of_g2Class_nonA S h3L hTp h1 i hnonA).elim
    | F4 =>
      by_cases hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
      · exact rationalLieType_of_f4Class S h3L hT hTp h1 i hnonA hQ
      · exact hF2 L p₀ S a hT hap h1 i hnonA hinner hQ hqs
    | D4 => exact rationalLieType_of_inner_nonA_D4 S Nat.prime_three h3L hT hTp i hnonA hinner
    | E6 => exact rationalLieType_of_inner_nonA_E6 S Nat.prime_three h3L hT hTp i hnonA hinner
    | E7 => exact rationalLieType_of_inner_nonA_E7 S Nat.prime_three h3L hT hTp i hnonA hinner
    | E8 => exact rationalLieType_of_inner_nonA_E8 S Nat.prime_three h3L hT hTp i hnonA hinner
  · exact hOuter τ L p₀ S a hT hap h1 i hnonA hinner hqs


theorem excRationalLieTypes_of_residuals (hOuter : ExcRationalLieTypesOuter)
    (hF2 : ExcRationalLieTypesF4Two) : ExcRationalLieTypes :=
  excRationalLieTypes_of_nonA (excRationalLieTypesNonA_of_residuals hOuter hF2)

end Reduction

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
