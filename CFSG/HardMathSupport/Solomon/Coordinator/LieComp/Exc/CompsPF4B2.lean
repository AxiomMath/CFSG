module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPReduction
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.CompsPSp4Pair
import CFSG.RankThree.Chevalley.SteinbergCFEvenF4StandardParabolic

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.LieComp

open CFSG CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.Assembly.LowTwoRank CFSG.LieType.CurtisTits CFSG.ComponentClassification.CatLeafProof
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KE CFSG.Timmesfeld CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair
  symplecticBlockStandardPair_le_sup)
open scoped MatrixGroups Matrix

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

@[expose] def b2Node : Fin 2 → Fin (Tag.rank .F4) := ![f4Node 1, f4Node 2]

@[expose] def f4LeviB2 : Set (Fin (Tag.rank .F4)) := Set.range b2Node

theorem mem_f4LeviB2 (j : Fin (Tag.rank .F4)) : j ∈ f4LeviB2 ↔ j.val = 1 ∨ j.val = 2 := by
  unfold f4LeviB2
  rw [Set.mem_range]
  revert j
  decide

section Recog


theorem map_subtype_sup_b2 {K : Type} [Field K] :
    (rankOne (f4Datum K).rootGroup (f4Node 1) ⊔ rankOne (f4Datum K).rootGroup (f4Node 2)).map
      (adjointGroup .F4 K).subtype = subsystemGroup .F4 K f4LeviB2 := by
  rw [Subgroup.map_sup]
  simp only [f4Datum, map_subtype_rankOne_rootGroup]
  refine le_antisymm (sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_))
    ((Subgroup.closure_le _).2 ?_)
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_subsystemGroup (A := f4LeviB2) ⟨0, rfl⟩ c
    · exact yUnit_mem_subsystemGroup (A := f4LeviB2) ⟨0, rfl⟩ c
  · rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact xUnit_mem_subsystemGroup (A := f4LeviB2) ⟨1, rfl⟩ c
    · exact yUnit_mem_subsystemGroup (A := f4LeviB2) ⟨1, rfl⟩ c
  · rintro _ ⟨i, ⟨k, rfl⟩, c, rfl | rfl⟩
    · fin_cases k
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inl ⟨c, rfl⟩))
    · fin_cases k
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩))
      · exact Subgroup.mem_sup_right (Subgroup.subset_closure (Or.inr ⟨c, rfl⟩))

theorem innerRecog_of_sp2 {p f : ℕ} (hp : p.Prime) (hf : 0 < f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = p ^ f) (hK3 : 3 ≤ Nat.card K) {G : Type} [Group G]
    (Ψ : StatedSp 2 K →* G) (hker : Ψ.ker ≤ Subgroup.center (StatedSp 2 K))
    {H : Subgroup G} (hrange : Ψ.range = H) : InnerRecog p ↥H := by
  haveI : Fintype K := Fintype.ofFinite K
  have hch : ringChar K = p := ringChar_eq_of_natCard_eq_pow hp hK hf
  have hne : (2, Fintype.card K) ≠ (2, 2) := by
    intro h
    have : Fintype.card K = 2 := (Prod.mk.inj h).2
    rw [← Nat.card_eq_fintype_card] at this
    omega
  have hfd := spFactorFacts_holds K 2 (by norm_num) hne
  rw [hch] at hfd
  exact innerRecog_of_range hfd (spAltSixFacts_holds K 2 (by norm_num) hne) Ψ hker hrange

theorem innerRecog_f4_B2 {K : Type} [Field K] [Finite K] {p f : ℕ} (hp : p.Prime) (hf : 0 < f)
    (hK : Nat.card K = p ^ f) (hK3 : 3 ≤ Nat.card K) :
    InnerRecog p ↥(subsystemGroup .F4 K f4LeviB2) := by
  classical
  obtain ⟨W, hW⟩ : ∃ W, SymplecticBlockStandardPair K W
      (rankOne (f4Datum K).rootGroup (f4Node 1)) (rankOne (f4Datum K).rootGroup (f4Node 2)) := by
    by_cases hp2 : p = 2
    · subst hp2
      haveI : CharP K 2 := by
        have := ringChar_eq_of_natCard_eq_pow hp hK hf
        rw [← this]
        haveI : Fintype K := Fintype.ofFinite K
        exact ringChar.charP K
      have hK4 : 4 ≤ Nat.card K := by
        rw [hK] at hK3 ⊢
        rcases Nat.lt_or_ge f 2 with hf2 | hf2
        · interval_cases f
          omega
        · calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      exact f4_spPair_even hK4
    · obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
        (Dv := (f4Datum K).divisible) rfl
      obtain ⟨C, -, hC⟩ := f4_commutatorFormula K O
      have hE := f4_chevalleyExtras K O C hC
      exact exists_symplecticBlockStandardPair_rankOne_of_isQuasisimple
        (isQuasisimple_statedSp_two hK3) (two_ne_zero_of_natCard_eq_pow hp hp2 hf hK) hE rfl
        (i := f4Node 2) (j := f4Node 1) f4_cartan_21 f4_cartan_12
  have hle := symplecticBlockStandardPair_le_sup hW
  obtain ⟨θ, c, hrange, hker, -, -, hU, hV⟩ := hW
  have hUW : rankOne (f4Datum K).rootGroup (f4Node 1) ≤ W := by
    rw [← hU, ← hrange]
    exact Subgroup.map_le_range _ _
  have hVW : rankOne (f4Datum K).rootGroup (f4Node 2) ≤ W := by
    rw [← hV, ← hrange]
    exact Subgroup.map_le_range _ _
  have hWeq : W = rankOne (f4Datum K).rootGroup (f4Node 1) ⊔
      rankOne (f4Datum K).rootGroup (f4Node 2) := le_antisymm hle (sup_le hUW hVW)
  refine innerRecog_of_sp2 hp hf hK hK3 ((adjointGroup .F4 K).subtype.comp θ) ?_ ?_
  · intro x hx
    exact hker (Subtype.ext (MonoidHom.mem_ker.mp hx))
  · rw [MonoidHom.range_comp, hrange, hWeq, map_subtype_sup_b2]

theorem rationalLieType_of_f4B2_class {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup Tag.F4 L p₀) {a : Fin Tag.F4.rank → Lˣ}
    (hTor : rootDiagUnit Tag.F4 a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.F4)
    (hroots : componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2)
    (hinner : twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.F4.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)]))
    (hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :
    RationalLieType (ringChar L) (rationalComponent S.ρ S.Γ (rootCharHom a) i) := by
  classical
  refine rationalLieType_of_innerRecog_card S hTor i hinner (fun K' hfin hcardK' => ?_)
  have hcomp : componentRootSpan K' (rootCharHom a) i =
      rootSpan Tag.F4 K' ((fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2) := by
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
  have h3 : 3 ≤ Nat.card ↥K' := hcardK' ▸ hQ
  have hrec := innerRecog_f4_B2 hprime f.pos hK'card h3
  have hsub : subsystemGroup Tag.F4 ↥K' f4LeviB2 =
      rootSpan Tag.F4 ↥K' (parabolicRoots Tag.F4 f4LeviB2) :=
    CFSG.RankThree.Chevalley.subsystemGroup_eq_iSup_rootSubgroup (τ := Tag.F4) (J := f4LeviB2) ↥K'
  rw [hsub] at hrec
  exact innerRecog_rootSpan_smul v (fun α hα => hα.1) hrec

end Recog

section Reduce


theorem f4_nonA_casesP2 {p : ℕ} (hp : p.Prime) (hp2 : p % 2 = 1) {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.F4 L p₀) (hpL : ((p : ℕ) : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ p = 1)
    (h1 : rootDiagUnit Tag.F4 a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hnonA : ¬ (1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))) :
    (∃ v : WeylGroup Tag.F4,
      componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots Tag.F4 f4LeviB2 ∧
      compRank (componentRoots (rootCharHom a) i) = 2 ∧
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
    refine ⟨v, ?_, by rw [hrank]; rfl, by rw [hncard]; exact kacCount_F4_B2⟩
    rw [hroots, rootsOf_eq_parabolicRoots kacF4 facts_F4 (J := f4LeviB2) (by decide)
      (fun j => by rw [mem_f4LeviB2]; revert j; decide)]
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

@[expose] def ExcRationalLieTypesF4SmallP (p : ℕ) : Prop :=
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
          (componentRoots (rootCharHom a) i).ncard = 8 ∧
          ¬ (3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i))) ∨
        (compRank (componentRoots (rootCharHom a) i) = 3 ∧
          (componentRoots (rootCharHom a) i).ncard = 18 ∧
          ¬ (4 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)))) →
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        LieCompData (ringChar L) ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)

theorem excRationalLieTypesF4P_of_small {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : ExcRationalLieTypesF4SmallP p) : ExcRationalLieTypesF4P p := by
  intro L _ _ p₀ S a hT hap h1 i hA hinner hshape hq
  classical
  have hp2' : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
  have hTp := rootDiagUnit_pow_eq_one_of_forall hap
  rcases hshape with ⟨hr2, hn8⟩ | ⟨hr3, hn18, hQ⟩
  · by_cases hQ : 3 ≤ S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)
    · rcases f4_nonA_casesP2 hp hp2' S hpL hTp h1 i hA with ⟨v, hroots, -, -⟩ | ⟨v, J, -, -, hr, hn⟩
      · exact (rationalLieType_of_f4B2_class S hT i v hroots hinner hQ).lieCompData
      · omega
    · exact h L p₀ S a hT hap h1 i hA hinner (Or.inl ⟨hr2, hn8, hQ⟩) hq
  · exact h L p₀ S a hT hap h1 i hA hinner (Or.inr ⟨hr3, hn18, hQ⟩) hq

end Reduce

end CFSG.HardMathSupport.Solomon.Coordinator.LieComp
