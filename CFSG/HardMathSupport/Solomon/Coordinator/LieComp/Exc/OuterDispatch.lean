module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.OuterE6
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacDispatch
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcTame

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KD4T CFSG.ComponentClassification.CatLeafProof
  CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.RankThree.Lattice
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

theorem toVec_ofFn_gen (r : ℕ) (v : Fin r → ℤ) : toVec r (List.ofFn v) = v := by
  funext i
  simp [toVec, vget]

section Dispatch


theorem twistInner_of_shape {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (i : KernelComponent (rootCharHom a)) (r n : ℕ)
    (hr : compRank (componentRoots (rootCharHom a) i) = r)
    (hn : (componentRoots (rootCharHom a) i).ncard = n) (h6 : ¬ (r = 6 ∧ n = 72))
    (h4 : ¬ (r = 4 ∧ n = 24)) (hD : ¬ (4 ≤ r ∧ n = 2 * r * (r - 1)))
    (hA : ¬ (2 ≤ r ∧ n = r * (r + 1))) :
    twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]) := by
  classical
  by_cases hin : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])
  · exact hin
  · have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
      unfold twistKind
      rw [if_neg hin]
      rw [if_neg (by
        rintro (⟨h1, h2⟩ | ⟨h1, h2, -⟩)
        · rw [hr] at h1
          rw [hn] at h2
          exact h6 ⟨h1, h2⟩
        · rw [hr] at h1
          rw [hn] at h2
          exact h4 ⟨h1, h2⟩)]
      rw [if_neg (fun h => by
        rw [hr, hn] at h
        exact hD h)]
      rw [if_neg (fun h => by
        rw [hr, hn] at h
        exact hA h)]
    exact twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hT i hkind


theorem rationalLieType_of_outer_E7 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E7 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E7.rank → Lˣ} (hTor : rootDiagUnit Tag.E7 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E7 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E7.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S hp hpL
      hTp i
  have hn' := hn
  rw [hrank] at h6 hn'
  rw [hncard] at hn'
  have hrk : Tag.E7.rank = 7 := rfl
  by_cases hc6 : c.length = 6
  · have h72 : kacCount Tag.E7 kacE7.θ (c.map (idxNode (r := Tag.E7.rank))).toFinset = 72 := by
      rw [hn', hc6]
      rfl
    have hCeq := kacCount_E7_six ((c.map (idxNode (r := Tag.E7.rank))).toFinset)
      (by rw [e7_card c hc, hc6]) h72
    refine rationalLieType_of_e6_outer S hTor i v ?_ hout
    rw [hroots, hCeq, rootsOf_eq_parabolicRoots kacE7 facts_E7 (J := e6Nodes Tag.E7)
      (by decide) (fun j => by simp only [e6Nodes, Set.mem_setOf_eq]; revert j; decide)]
  ·
    exfalso
    apply hout
    have hc7 : c.length = 7 := by omega
    refine twistInner_of_shape S hTor i 7 126 (by rw [hrank, hc7]) (by rw [hncard, hn', hc7]; rfl)
      (by omega) (by omega) (by omega) (by omega)

theorem rationalLieType_of_outer_E8 {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E8 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E8.rank → Lˣ} (hTor : rootDiagUnit Tag.E8 a ∈ S.D.torus)
    (hTp : rootDiagUnit Tag.E8 a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E8.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S hp hpL
      hTp i
  have hn' := hn
  rw [hrank] at h6 hn'
  rw [hncard] at hn'
  have hrk : Tag.E8.rank = 8 := rfl
  by_cases hc6 : c.length = 6
  · have h72 : kacCount Tag.E8 kacE8.θ (c.map (idxNode (r := Tag.E8.rank))).toFinset = 72 := by
      rw [hn', hc6]
      rfl
    have hCeq := kacCount_E8_six ((c.map (idxNode (r := Tag.E8.rank))).toFinset)
      (by rw [e8_card c hc, hc6]) h72
    refine rationalLieType_of_e6_outer S hTor i v ?_ hout
    rw [hroots, hCeq, rootsOf_eq_parabolicRoots kacE8 facts_E8 (J := e6Nodes Tag.E8)
      (by decide) (fun j => by simp only [e6Nodes, Set.mem_setOf_eq]; revert j; decide)]
  ·
    exfalso
    apply hout
    have hc78 : c.length = 7 ∨ c.length = 8 := by omega
    rcases hc78 with hc7 | hc8
    · refine twistInner_of_shape S hTor i 7 126 (by rw [hrank, hc7])
        (by rw [hncard, hn', hc7]; rfl) (by omega) (by omega) (by omega) (by omega)
    · refine twistInner_of_shape S hTor i 8 240 (by rw [hrank, hc8])
        (by rw [hncard, hn', hc8]; rfl) (by omega) (by omega) (by omega) (by omega)


theorem mem_rootsOf_of_kacTest_all {τ : Tag} (K : KacData τ) (hK : K.Facts)
    {C : Finset (Option (Fin τ.rank))} (hC : ∃ x, x ∉ C)
    (hall : ∀ r ∈ τ.artifactRoots, kacTest K.θ C (toVec τ.rank r)) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : γ ∈ K.rootsOf (C : Set (Option (Fin τ.rank))) := by
  refine (mem_rootsOf_iff K hK hC).2 ⟨hγ, ?_⟩
  have := hall _ (isRoot_iff_mem_artifactRoots.1 hγ)
  rwa [toVec_ofFn_gen] at this

@[expose] def e6θ : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

theorem e6_allRoots : ∀ c ∈ e6Conn, c.length = 6 →
    kacCount Tag.E6 e6θ (c.map (idxNode (r := Tag.E6.rank))).toFinset = 72 →
    ∀ r ∈ Tag.E6.artifactRoots,
      kacTest e6θ (c.map (idxNode (r := Tag.E6.rank))).toFinset
        (toVec Tag.E6.rank r) := by
  decide +kernel

theorem false_of_e6Class_E {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.E6 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.E6.rank → Lˣ} (hTp : rootDiagUnit Tag.E6 a ^ p = 1)
    (h1 : rootDiagUnit Tag.E6 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (h6 : 6 ≤ compRank (componentRoots (rootCharHom a) i))
    (hn : (componentRoots (rootCharHom a) i).ncard =
      eRootCount (compRank (componentRoots (rootCharHom a) i))) : False := by
  classical
  obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S hp hpL hTp i
  have hrk : Tag.E6.rank = 6 := rfl
  have hc6 : c.length = 6 := by
    rw [hrank] at h6
    omega
  have h72 : kacCount Tag.E6 kacE6.θ (c.map (idxNode (r := Tag.E6.rank))).toFinset = 72 := by
    rw [← hncard, hn, hrank, hc6]
    rfl
  have hCp : ∃ y, y ∉ (c.map (idxNode (r := Tag.E6.rank))).toFinset := by
    by_contra hcon
    push Not at hcon
    have h1' : (c.map (idxNode (r := Tag.E6.rank))).toFinset = Finset.univ :=
      Finset.eq_univ_of_forall hcon
    have h2 := e6_card c hc
    rw [h1', Finset.card_univ, Fintype.card_option, Fintype.card_fin, hc6] at h2
    omega
  apply h1
  refine eq_one_of_simple_mem_class i (fun j => ?_)
  rw [hroots]
  refine ⟨v⁻¹ • Pi.single j 1, ?_, smul_inv_smul v _⟩
  exact mem_rootsOf_of_kacTest_all kacE6 facts_E6 hCp (e6_allRoots c hc hc6 h72)
    (IsRoot.smul (isRoot_single _ j) v⁻¹)

theorem f4_nonA_shape {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) (hpL : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.F4.rank → Lˣ}
    (hT3 : rootDiagUnit Tag.F4 a ^ 3 = 1) (h1 : rootDiagUnit Tag.F4 a ≠ 1)
    (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    compRank (componentRoots (rootCharHom a) i) = 3 ∧
      (componentRoots (rootCharHom a) i).ncard = 18 := by
  classical
  obtain ⟨v, μ, x, c, hμ, hc, hcomp, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S Nat.prime_three
      hpL hT3 i
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2]
      (c.map (idxNode (r := Tag.F4.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hnonA
    exact hnonA
  rcases f4_nonA_cases c hc hlen hnonA' with rfl | rfl | rfl | rfl | rfl
  · exact (not_comp_eq_B2_F4 (p := 3) le_rfl hμ hcomp).elim
  · exact ⟨by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_B3⟩
  · exact ⟨by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_C3⟩
  · exact (not_comp_eq_B4_F4 hμ hcomp).elim
  · exfalso
    apply h1
    refine eq_one_of_simple_mem_class i (fun j => ?_)
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := Set.univ) (by decide)
      (fun j => by simp only [Set.mem_univ, iff_true]; revert j; decide)]
    exact ⟨v⁻¹ • Pi.single j 1, ⟨IsRoot.smul (isRoot_single _ j) v⁻¹, fun i hi =>
      (hi (Set.mem_univ i)).elim⟩, smul_inv_smul v _⟩

end Dispatch

section Residuals


@[expose] def ExcRationalLieTypesOuterD : Prop :=
  ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ : ℕ) (S : LangSetup τ L p₀)
    (a : Fin τ.rank → Lˣ), rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ 3 = 1) →
    rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
      (4 ≤ compRank (componentRoots (rootCharHom a) i) ∧
        (componentRoots (rootCharHom a) i).ncard = 2 * compRank (componentRoots (rootCharHom a) i) *
          (compRank (componentRoots (rootCharHom a) i) - 1)) →
      ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i)

end Residuals

section Reduction


theorem excRationalLieTypesOuter_of_D (h : ExcRationalLieTypesOuterD) :
    ExcRationalLieTypesOuter := by
  intro τ L _ _ p₀ S a hT hap h1 i hnonA hout hqs
  classical
  have hℓ3 : ringChar L ≠ 3 := ringChar_ne_three_of_pow_three hap h1
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h'
    have hd : ringChar L ∣ 3 := (ringChar.spec L 3).1 (by exact_mod_cast h')
    rcases (Nat.dvd_prime Nat.prime_three).1 hd with h'' | h''
    · exact CharP.ringChar_ne_one h''
    · exact hℓ3 h''
  cases τ with
  | G2 => exact (false_of_g2Class_nonA S h3L hTp h1 i hnonA).elim
  | F4 =>
    obtain ⟨hr3, hn18⟩ := f4_nonA_shape S h3L hTp h1 i hnonA
    exact (hout (twistInner_of_shape S hT i 3 18 hr3 hn18 (by omega) (by omega) (by omega)
      (by omega))).elim
  | D4 =>
    obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacD4 facts_D4 d4_tree d4_adj d4_check d4_lt d4_card S Nat.prime_three
        h3L hTp i
    have hshape := d4_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA | hD
    · exact (hnonA hA).elim
    · exact h _ L p₀ S a hT hap h1 i hD hout hqs
  | E6 =>
    obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE6 facts_E6 e6_tree e6_adj e6_check e6_lt e6_card S Nat.prime_three
        h3L hTp i
    have hshape := e6_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA | hD | hE
    · exact (hnonA hA).elim
    · exact h _ L p₀ S a hT hap h1 i hD hout hqs
    · exact (false_of_e6Class_E S Nat.prime_three h3L hTp h1 i hE.1 hE.2).elim
  | E7 =>
    obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE7 facts_E7 e7_tree e7_adj e7_check e7_lt e7_card S Nat.prime_three
        h3L hTp i
    have hshape := e7_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA | hD | hE
    · exact (hnonA hA).elim
    · exact h _ L p₀ S a hT hap h1 i hD hout hqs
    · exact rationalLieType_of_outer_E7 S Nat.prime_three h3L hT hTp i hE.1 hE.2 hout
  | E8 =>
    obtain ⟨v, μ, x, c, -, hc, -, hlen, hroots, hrank, hncard⟩ :=
      exists_cand_of_class kacE8 facts_E8 e8_tree e8_adj e8_check e8_lt e8_card S Nat.prime_three
        h3L hTp i
    have hshape := e8_shape c hc hlen
    rw [← hncard, ← hrank] at hshape
    rcases hshape with hA | hD | hE
    · exact (hnonA hA).elim
    · exact h _ L p₀ S a hT hap h1 i hD hout hqs
    · exact rationalLieType_of_outer_E8 S Nat.prime_three h3L hT hTp i hE.1 hE.2 hout


theorem excRationalLieTypes_of_residualsD (hD : ExcRationalLieTypesOuterD)
    (hF2 : ExcRationalLieTypesF4Two) : ExcRationalLieTypes :=
  excRationalLieTypes_of_residuals (excRationalLieTypesOuter_of_D hD) hF2

end Reduction


end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
