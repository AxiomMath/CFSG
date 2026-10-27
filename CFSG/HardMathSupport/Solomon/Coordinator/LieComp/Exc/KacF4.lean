module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.KacShape
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.RecogF4
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUF4
import CFSG.HardMathSupport.Timmesfeld.RootAut.Main
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.ComponentClassification.CatLeafProof
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

theorem f4_nonA_cases : ∀ c ∈ f4Conn, c.length ≤ 4 →
    ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2] (c.map (idxNode (r := Tag.F4.rank))).toFinset =
      c.length * (c.length + 1)) →
    c = [2, 3] ∨ c = [1, 2, 3] ∨ c = [2, 3, 4] ∨ c = [0, 1, 2, 3] ∨ c = [1, 2, 3, 4] := by
  decide +kernel

theorem kacCount_F4_B3 : kacCount Tag.F4 ![2, 3, 4, 2]
    (([1, 2, 3] : List ℕ).map (idxNode (r := Tag.F4.rank))).toFinset = 18 := by
  decide +kernel

theorem kacCount_F4_C3 : kacCount Tag.F4 ![2, 3, 4, 2]
    (([2, 3, 4] : List ℕ).map (idxNode (r := Tag.F4.rank))).toFinset = 18 := by
  decide +kernel

section Excl


theorem f4_theta_dot (μ : Fin Tag.F4.rank → ℤ) :
    kacF4.θ ⬝ᵥ μ = 2 * μ 0 + 3 * μ 1 + 4 * μ 2 + 2 * μ 3 := by
  rw [show kacF4.θ = ![2, 3, 4, 2] from rfl]
  show ∑ j : Fin 4, (![2, 3, 4, 2] : Fin 4 → ℤ) j * μ j = _
  rw [Fin.sum_univ_four]
  rfl

theorem not_comp_eq_B2_F4 {p : ℕ} (hp : p ≤ 3) {μ : Fin Tag.F4.rank → ℤ}
    (hμ : kacF4.IsNormal p μ) {x : Option (Fin Tag.F4.rank)}
    (hc : kacF4.comp p μ x = {y | nodeIdx y ∈ ([2, 3] : List ℕ)}) : False := by
  have hmem : ∀ y : Option (Fin Tag.F4.rank), nodeIdx y ∈ ([2, 3] : List ℕ) →
      kacF4.IsZ p μ y := fun y hy => by
    have : y ∈ kacF4.comp p μ x := by rw [hc]; exact hy
    exact this.1
  have hz1 : kacF4.IsZ p μ (some 1) := hmem (some 1) (by decide)
  have hz2 : kacF4.IsZ p μ (some 2) := hmem (some 2) (by decide)
  have hout : ∀ (y z : Option (Fin Tag.F4.rank)), nodeIdx z ∈ ([2, 3] : List ℕ) →
      nodeIdx y ∉ ([2, 3] : List ℕ) → kacF4.Adj z y → kacF4.IsZ p μ z →
      ¬ kacF4.IsZ p μ y := by
    intro y z hz hy hadj hzz hyz
    have hin : z ∈ kacF4.comp p μ x := by rw [hc]; exact hz
    have : y ∈ kacF4.comp p μ x :=
      ⟨hyz, hin.2.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨hzz, hyz, hadj⟩)⟩
    rw [hc] at this
    exact hy this
  have h0 : ¬ kacF4.IsZ p μ (some 0) :=
    hout (some 0) (some 1) (by decide) (by decide) ((f4_adj _ _).2 (by decide)) hz1
  have h3 : ¬ kacF4.IsZ p μ (some 3) :=
    hout (some 3) (some 2) (by decide) (by decide) ((f4_adj _ _).2 (by decide)) hz2
  change μ 1 = 0 at hz1
  change μ 2 = 0 at hz2
  change ¬ μ 0 = 0 at h0
  change ¬ μ 3 = 0 at h3
  have h0pos : 1 ≤ μ 0 := by
    have := hμ.1 0
    omega
  have h3pos : 1 ≤ μ 3 := by
    have := hμ.1 3
    omega
  have hθ := hμ.2
  rw [f4_theta_dot, hz1, hz2] at hθ
  have hp' : (p : ℤ) ≤ 3 := by exact_mod_cast hp
  omega

theorem not_comp_eq_B4_F4 {μ : Fin Tag.F4.rank → ℤ} (hμ : kacF4.IsNormal 3 μ)
    {x : Option (Fin Tag.F4.rank)}
    (hc : kacF4.comp 3 μ x = {y | nodeIdx y ∈ ([0, 1, 2, 3] : List ℕ)}) : False := by
  have hmem : ∀ y : Option (Fin Tag.F4.rank), nodeIdx y ∈ ([0, 1, 2, 3] : List ℕ) →
      kacF4.IsZ 3 μ y := fun y hy => by
    have : y ∈ kacF4.comp 3 μ x := by rw [hc]; exact hy
    exact this.1
  have hz0 : kacF4.IsZ 3 μ none := hmem none (by decide)
  have hz1 : kacF4.IsZ 3 μ (some 0) := hmem (some 0) (by decide)
  have hz2 : kacF4.IsZ 3 μ (some 1) := hmem (some 1) (by decide)
  have hz3 : kacF4.IsZ 3 μ (some 2) := hmem (some 2) (by decide)
  change kacF4.θ ⬝ᵥ μ = ((3 : ℕ) : ℤ) at hz0
  change μ 0 = 0 at hz1
  change μ 1 = 0 at hz2
  change μ 2 = 0 at hz3
  rw [f4_theta_dot, hz1, hz2, hz3] at hz0
  push_cast at hz0
  omega

end Excl


section Main

open CFSG.HardMathSupport.Timmesfeld.RootAut


theorem rationalLieType_of_f4Levi_class {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4) {J : Set (Fin (Tag.rank .F4))} (hJ : J = f4LeviB3 ∨ J = f4LeviC3)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 J)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  refine rationalLieType_of_innerRecog_card S hTor i hinner (fun K' hfin hcardK' => ?_)
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan Tag.F4 K' ((fun α => v • α) '' parabolicRoots Tag.F4 J) := by
    show rootSpan Tag.F4 K' (componentRoots (rootCharHom a) i) = _
    rw [hroots]
  rw [hcomp]
  haveI : Fintype ↥K' := Fintype.ofFinite ↥K'
  haveI : CharP ↥K' (ringChar ↥K') := ringChar.charP ↥K'
  obtain ⟨f, hprime, hcardf⟩ := FiniteField.card ↥K' (ringChar ↥K')
  have hring : ringChar ↥K' = ringChar L := ringChar_subfield' K'
  rw [hring] at hprime hcardf
  have hK'card : Nat.card ↥K' = ringChar L ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardf]
  have h4 : 4 ≤ Nat.card ↥K' := hcardK' ▸ hQ
  have hrec := innerRecog_f4_levi hJ hprime f.pos hK'card h4
  have hsub : subsystemGroup Tag.F4 ↥K' J = rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 J) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := J) ↥K'
  rw [hsub] at hrec
  exact innerRecog_rootSpan_smul v (fun α hα => hα.1) hrec

theorem eq_one_of_simple_mem_class {τ : Tag} {L : Type} [Field L] {a : Fin τ.rank → Lˣ}
    (i : KernelComponent (rootCharHom a))
    (h : ∀ j, (Pi.single j 1 : Fin τ.rank → ℤ) ∈ componentRoots (rootCharHom a) i) :
    rootDiagUnit τ a = 1 := by
  have ha : a = 1 := by
    funext j
    obtain ⟨hker, -⟩ := h j
    have h1 : rootChar a (Pi.single j 1) = 1 := hker.2
    rw [CFSG.RankThree.PartOne.KE.CTTorus.rootChar_single] at h1
    exact h1
  rw [ha]
  exact rootDiagUnit_one

theorem rationalLieType_of_f4Class {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) (hpL : ((3 : ℕ) : L) ≠ 0) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (hT3 : rootDiagUnit Tag.F4 a ^ 3 = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1)))
    (hQ : 4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  obtain ⟨v, μ, x, c, hμ, hc, hcomp, hlen, hroots, hrank, hncard⟩ :=
    exists_cand_of_class kacF4 facts_F4 f4_tree f4_adj f4_check f4_lt f4_card S Nat.prime_three
      hpL hT3 i
  have hnonA' : ¬ (1 ≤ c.length ∧ kacCount Tag.F4 ![2, 3, 4, 2]
      (c.map (idxNode (r := Tag.F4.rank))).toFinset = c.length * (c.length + 1)) := by
    rw [hrank, hncard] at hnonA
    exact hnonA
  have hkindInner : ∀ (hr3 : compRank (componentRoots (rootCharHom a) i) = 3)
      (hn18 : (componentRoots (rootCharHom a) i).ncard = 18),
      twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
          (componentRoots (rootCharHom a) i)]) := by
    intro hr3 hn18
    have hkind : twistKind S.ρ (rootCharHom a) i = .inner := by
      by_cases hin : twistInner (componentRoots (rootCharHom a) i)
          ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (rootCharHom a) i)])
      · unfold twistKind
        rw [if_pos hin]
      · unfold twistKind
        rw [if_neg hin, if_neg (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> omega),
          if_neg (fun h => by omega),
          if_neg (fun h => by have := h.2; rw [hr3, hn18] at this; omega)]
    exact twistInner_of_twistKind_eq_innerT S rootAutIsWeyl_holds hTor i hkind
  rcases f4_nonA_cases c hc hlen hnonA' with rfl | rfl | rfl | rfl | rfl
  · exact (not_comp_eq_B2_F4 (p := 3) le_rfl hμ hcomp).elim
  ·
    have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
    have hn18 : (componentRoots (rootCharHom a) i).ncard = 18 := by
      rw [hncard]
      exact kacCount_F4_B3
    refine rationalLieType_of_f4Levi_class S hTor i v (J := f4LeviB3) (Or.inl rfl) ?_
      (hkindInner hr3 hn18) hQ
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviB3) (by decide)
      (fun j => by rw [mem_f4LeviB3]; revert j; decide)]
  ·
    have hr3 : compRank (componentRoots (rootCharHom a) i) = 3 := by rw [hrank]; rfl
    have hn18 : (componentRoots (rootCharHom a) i).ncard = 18 := by
      rw [hncard]
      exact kacCount_F4_C3
    refine rationalLieType_of_f4Levi_class S hTor i v (J := f4LeviC3) (Or.inr rfl) ?_
      (hkindInner hr3 hn18) hQ
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviC3) (by decide)
      (fun j => by rw [mem_f4LeviC3]; revert j; decide)]
  · exact (not_comp_eq_B4_F4 hμ hcomp).elim
  ·
    exfalso
    apply h1
    refine eq_one_of_simple_mem_class i (fun j => ?_)
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := Set.univ) (by decide)
      (fun j => by simp only [Set.mem_univ, iff_true]; revert j; decide)]
    exact ⟨v⁻¹ • Pi.single j 1, ⟨IsRoot.smul (isRoot_single _ j) v⁻¹, fun i hi =>
      (hi (Set.mem_univ i)).elim⟩, smul_inv_smul v _⟩

end Main

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
