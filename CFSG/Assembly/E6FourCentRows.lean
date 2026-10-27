module

public import CFSG.Assembly.E6FourCentSols

public section

namespace CFSG.Assembly

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.E6FourCentChk
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.LieType.SeitzGeneration
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open scoped Matrix


theorem e6Four_kernelRoots {L : Type} [Field L] (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    (v : Fin Tag.E6.rank → ZMod 5) :
    kernelRoots (rootCharHom (fun j => ζ ^ (v j).val)) =
      {γ | IsRoot Tag.E6 γ ∧ e6Pair v γ = 0} := by
  rw [kernelRoots_rootCharHom]
  ext γ
  simp only [Set.mem_setOf_eq]
  rw [e6Four_rootChar_eq_one_iff ζ hζ v γ]

private abbrev e6Chi {L : Type} [Field L] (ζ : Lˣ) (v : Fin Tag.E6.rank → ZMod 5) :
    Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ :=
  rootCharHom (fun j => ζ ^ (v j).val)

private abbrev e6Rel {L : Type} [Field L] (ζ : Lˣ) (v : Fin Tag.E6.rank → ZMod 5) :
    kernelRoots (e6Chi ζ v) → kernelRoots (e6Chi ζ v) → Prop :=
  fun x y => (x : Fin Tag.E6.rank → ℤ) ⬝ᵥ
    (Tag.E6.symmetrizedCartan *ᵥ (y : Fin Tag.E6.rank → ℤ)) ≠ 0

private theorem e6SolVec_zero : e6SolVec 0 = 0 := by
  funext i
  fin_cases i <;> decide

private noncomputable def rootIdx {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ) (x : kernelRoots χ) : ℕ :=
  Classical.choose (exists_e6RootVec x.2.1)

private theorem rootIdx_lt {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ) (x : kernelRoots χ) :
    rootIdx χ x < 72 :=
  (Classical.choose_spec (exists_e6RootVec x.2.1)).1

private theorem e6RootVec_rootIdx {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ) (x : kernelRoots χ) :
    e6RootVec (rootIdx χ x) = x.1 :=
  (Classical.choose_spec (exists_e6RootVec x.2.1)).2

private theorem rootIdx_eq {L : Type} [Field L]
    (χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* Lˣ) {x : kernelRoots χ} {j : ℕ}
    (hj : j < 72) (h : e6RootVec j = x.1) : rootIdx χ x = j :=
  e6RootVec_injOn (rootIdx_lt χ x) hj (by rw [e6RootVec_rootIdx, h])

private theorem kernelRoots_e6RootVec {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (v : Fin Tag.E6.rank → ZMod 5) {j : ℕ}
    (hj : j < 72) (hS : (e6SolMask v).testBit j = true) :
    e6RootVec j ∈ kernelRoots (e6Chi ζ v) := by
  refine ⟨isRoot_e6RootVec hj, ?_⟩
  exact (e6Four_rootChar_eq_one_iff ζ hζ v (e6RootVec j)).2 ((testBit_e6SolMask v hj).1 hS)

private theorem exists_index_of_kernelRoots {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (v : Fin Tag.E6.rank → ZMod 5)
    {γ : Fin Tag.E6.rank → ℤ} (hγ : γ ∈ kernelRoots (e6Chi ζ v)) :
    ∃ k, k < 72 ∧ e6RootVec k = γ ∧ (e6SolMask v).testBit k = true := by
  obtain ⟨k, hk, hkγ⟩ := exists_e6RootVec hγ.1
  refine ⟨k, hk, hkγ, ?_⟩
  rw [testBit_e6SolMask v hk, hkγ]
  exact (e6Four_rootChar_eq_one_iff ζ hζ v γ).1 hγ.2

private theorem testBit_rootIdx {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (v : Fin Tag.E6.rank → ZMod 5)
    (x : kernelRoots (e6Chi ζ v)) :
    (e6SolMask v).testBit (rootIdx (e6Chi ζ v) x) = true := by
  rw [testBit_e6SolMask v (rootIdx_lt (e6Chi ζ v) x), e6RootVec_rootIdx]
  exact (e6Four_rootChar_eq_one_iff ζ hζ v x.1).1 x.2.2

private theorem e6Symm (i j : Fin Tag.E6.rank) :
    Tag.E6.symmetrizedCartan i j = Tag.E6.symmetrizedCartan j i := by
  fin_cases i <;> fin_cases j <;> decide

private theorem e6_iform_comm (u v : Fin Tag.E6.rank → ℤ) : iform u v = iform v u := by
  simp only [iform]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [e6Symm j i]
  ring

private theorem adjLit_testBit_comm {a b : ℕ} (ha : a < 72) (hb : b < 72) :
    adjLit.testBit (72 * a + b) = true ↔ adjLit.testBit (72 * b + a) = true := by
  rw [adjLit_iff ha hb, adjLit_iff hb ha, dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform,
    e6_iform_comm]

private theorem reach_end_mem {A S : ℕ} {a b : ℕ} (ha : a < 72) (haS : S.testBit a = true)
    (h : Reach A S a b) : b < 72 ∧ S.testBit b = true := by
  induction h with
  | refl => exact ⟨ha, haS⟩
  | tail h' hbc ih => exact ⟨hbc.1, hbc.2.1⟩

private theorem reach_symm {S : ℕ} {a b : ℕ} (ha : a < 72) (haS : S.testBit a = true)
    (h : Reach adjLit S a b) : Reach adjLit S b a := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h' hbc ih =>
    obtain ⟨hb'72, hb'S⟩ := reach_end_mem ha haS h'
    exact Relation.ReflTransGen.head
      ⟨hb'72, hb'S, (adjLit_testBit_comm hb'72 hbc.1).1 hbc.2.2⟩ ih

private theorem reach_of_rel {L : Type} [Field L] (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    (v : Fin Tag.E6.rank → ZMod 5) {x y : kernelRoots (e6Chi ζ v)}
    (h : x.1 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ y.1) ≠ 0) :
    Reach adjLit (e6SolMask v) (rootIdx (e6Chi ζ v) x) (rootIdx (e6Chi ζ v) y) := by
  refine Relation.ReflTransGen.single ⟨rootIdx_lt (e6Chi ζ v) y, testBit_rootIdx ζ hζ v y, ?_⟩
  rw [adjLit_iff (rootIdx_lt (e6Chi ζ v) x) (rootIdx_lt (e6Chi ζ v) y),
    e6RootVec_rootIdx, e6RootVec_rootIdx]
  exact h

private theorem reach_of_eqvGen {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (v : Fin Tag.E6.rank → ZMod 5)
    {α γ : kernelRoots (e6Chi ζ v)} (h : Relation.EqvGen (e6Rel ζ v) α γ) :
    Reach adjLit (e6SolMask v) (rootIdx (e6Chi ζ v) α) (rootIdx (e6Chi ζ v) γ) := by
  induction h with
  | rel x y hxy => exact reach_of_rel ζ hζ v hxy
  | refl x => exact Relation.ReflTransGen.refl
  | symm x y _ ih =>
    exact reach_symm (rootIdx_lt (e6Chi ζ v) x) (testBit_rootIdx ζ hζ v x) ih
  | trans x y z _ _ ih1 ih2 => exact Relation.ReflTransGen.trans ih1 ih2

private theorem eqvGen_of_reach {L : Type} [Field L] (ζ : Lˣ)
    (hζ : IsPrimitiveRoot (ζ : L) 5) (v : Fin Tag.E6.rank → ZMod 5)
    {a b : ℕ} (ha : a < 72) (haS : (e6SolMask v).testBit a = true)
    (hb : b < 72) (hbS : (e6SolMask v).testBit b = true)
    (h : Reach adjLit (e6SolMask v) a b) :
    Relation.EqvGen (e6Rel ζ v)
      (⟨e6RootVec b, kernelRoots_e6RootVec ζ hζ v hb hbS⟩ : kernelRoots (e6Chi ζ v))
      (⟨e6RootVec a, kernelRoots_e6RootVec ζ hζ v ha haS⟩ : kernelRoots (e6Chi ζ v)) := by
  revert ha haS
  refine Relation.ReflTransGen.head_induction_on
    (motive := fun a _ => ∀ (ha : a < 72) (haS : (e6SolMask v).testBit a = true),
      Relation.EqvGen (e6Rel ζ v)
        (⟨e6RootVec b, kernelRoots_e6RootVec ζ hζ v hb hbS⟩ : kernelRoots (e6Chi ζ v))
        (⟨e6RootVec a, kernelRoots_e6RootVec ζ hζ v ha haS⟩ : kernelRoots (e6Chi ζ v)))
    h ?_ ?_
  · intro ha haS
    have he : (⟨e6RootVec b, kernelRoots_e6RootVec ζ hζ v hb hbS⟩ : kernelRoots (e6Chi ζ v)) =
        ⟨e6RootVec b, kernelRoots_e6RootVec ζ hζ v ha haS⟩ := Subtype.ext rfl
    rw [he]
    exact Relation.EqvGen.refl _
  · intro a c hac hcb ih ha haS
    have hstep : Relation.EqvGen (e6Rel ζ v)
        (⟨e6RootVec a, kernelRoots_e6RootVec ζ hζ v ha haS⟩ : kernelRoots (e6Chi ζ v))
        (⟨e6RootVec c, kernelRoots_e6RootVec ζ hζ v hac.1 hac.2.1⟩ :
          kernelRoots (e6Chi ζ v)) := by
      refine Relation.EqvGen.rel _ _ ?_
      have h' := hac.2.2
      rw [adjLit_iff ha hac.1] at h'
      simpa using h'
    exact Relation.EqvGen.trans _ _ _ (ih hac.1 hac.2.1) hstep.symm

theorem e6Four_exists_component_eq_kernelRoots_of_connected {L : Type} [Field L]
    (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5) (v : Fin Tag.E6.rank → ZMod 5)
    (hne : e6SolMask v ≠ 0)
    (hclosed : closedOK adjLit (e6SolMask v) (e6SolMask v) = true)
    (hconn : compOf adjLit (e6SolMask v) (e6SolMask v).log2 = e6SolMask v) :
    ∃ i : KernelComponent (rootCharHom (fun j => ζ ^ (v j).val)),
      componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i =
        kernelRoots (rootCharHom (fun j => ζ ^ (v j).val)) := by
  let k := (e6SolMask v).log2
  have hk : k < 72 := (Nat.log2_lt hne).mpr (e6SolMask_lt v)
  have hkS : (e6SolMask v).testBit k = true := by
    rw [← hconn]
    exact compOf_self adjLit (e6SolMask v) k hk
  let x : kernelRoots (e6Chi ζ v) :=
    ⟨e6RootVec k, kernelRoots_e6RootVec ζ hζ v hk hkS⟩
  refine ⟨⟦x⟧, ?_⟩
  ext γ
  constructor
  · exact fun h => h.1
  · intro hγ
    obtain ⟨j, hj, hjγ, hjS⟩ := exists_index_of_kernelRoots ζ hζ v hγ
    have hclosed' : closedOK adjLit (e6SolMask v)
        (compOf adjLit (e6SolMask v) k) = true := by
      rw [hconn]
      exact hclosed
    have hr : Reach adjLit (e6SolMask v) k j :=
      (compOf_iff adjLit (e6SolMask v) k hk hclosed' j).mp (by
        rw [hconn]
        exact hjS)
    have heq := eqvGen_of_reach ζ hζ v hk hkS hj hjS hr
    refine ⟨hγ, ?_⟩
    subst γ
    exact Quotient.sound heq

theorem e6Four_component_row {L : Type} [Field L] (ζ : Lˣ) (hζ : IsPrimitiveRoot (ζ : L) 5)
    {v : Fin Tag.E6.rank → ZMod 5} (hv : E6FourIsSol v) (hv0 : v ≠ 0)
    (i : KernelComponent (rootCharHom (fun j => ζ ^ (v j).val))) :
    ∃ c : ℕ, c < 2 ^ 72 ∧
      componentRoots (rootCharHom (fun j => ζ ^ (v j).val)) i = e6MaskRoots c ∧
        rowOK (e6SolMask v) c = true := by
  classical
  obtain ⟨n, hn625, hn_eq⟩ := exists_e6SolVec hv
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hv0 (hn_eq.symm.trans e6SolVec_zero)
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.2 hn0
  have hn624 : n ≤ 624 := by omega
  have hS_mem : e6SolMask v ∈ sigsLit := by
    rw [sigsLit_eq]
    refine List.mem_map.2 ⟨n, ?_, ?_⟩
    · rw [List.mem_range']
      exact ⟨n - 1, by omega, by omega⟩
    · exact congrArg e6SolMask hn_eq
  have hS72 : e6SolMask v < 2 ^ 72 := e6SolMask_lt v
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
  obtain ⟨k, hk72, hkγ, hkS⟩ := exists_index_of_kernelRoots ζ hζ v hγ
  obtain ⟨k0, hk0S, hreach, hrow⟩ := tableOK_spec hS_mem hS72 hkS
  have hk0_72 : k0 < 72 := by
    have hge : 2 ^ k0 ≤ e6SolMask v := Nat.ge_two_pow_of_testBit hk0S
    have hlt : 2 ^ k0 < 2 ^ 72 := lt_of_le_of_lt hge hS72
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
  have hclosed : closedOK adjLit (e6SolMask v) (compOf adjLit (e6SolMask v) k0) = true := by
    have h1 := hrow
    simp only [rowOK, Bool.and_eq_true] at h1
    exact h1.1
  have hcomp : ∀ j, (compOf adjLit (e6SolMask v) k0).testBit j = true ↔
      Reach adjLit (e6SolMask v) k0 j :=
    compOf_iff adjLit (e6SolMask v) k0 hk0_72 hclosed
  refine ⟨compOf adjLit (e6SolMask v) k0, compOf_lt adjLit (e6SolMask v) k0 hk0_72, ?_, hrow⟩
  ext α
  constructor
  · intro hα
    obtain ⟨hαK, hαi⟩ := hα
    obtain ⟨j, hj72, hjα, hjS⟩ := exists_index_of_kernelRoots ζ hζ v hαK
    have hEq : Relation.EqvGen (e6Rel ζ v) ⟨α, hαK⟩ ⟨γ, hγ⟩ := Quotient.exact hαi
    have hreach_αγ := reach_of_eqvGen ζ hζ v hEq
    have hj_eq : rootIdx (e6Chi ζ v) ⟨α, hαK⟩ = j := rootIdx_eq (e6Chi ζ v) hj72 hjα
    have hk_eq : rootIdx (e6Chi ζ v) ⟨γ, hγ⟩ = k := rootIdx_eq (e6Chi ζ v) hk72 hkγ
    rw [hj_eq, hk_eq] at hreach_αγ
    have hreach_kj : Reach adjLit (e6SolMask v) k j := reach_symm hj72 hjS hreach_αγ
    exact ⟨j, hj72, (hcomp j).2 (hreach.trans hreach_kj), hjα⟩
  · intro hα
    obtain ⟨j, hj72, hjc, hjα⟩ := hα
    rw [← hjα]
    have hreach_k0j : Reach adjLit (e6SolMask v) k0 j := (hcomp j).1 hjc
    have hjS : (e6SolMask v).testBit j = true := (reach_end_mem hk0_72 hk0S hreach_k0j).2
    refine ⟨kernelRoots_e6RootVec ζ hζ v hj72 hjS, ?_⟩
    have hsub : (⟨e6RootVec k, kernelRoots_e6RootVec ζ hζ v hk72 hkS⟩ :
        kernelRoots (e6Chi ζ v)) = ⟨γ, hγ⟩ := Subtype.ext hkγ
    rw [← hsub]
    refine Quotient.sound ?_
    have hstep_j : Relation.EqvGen (e6Rel ζ v)
        (⟨e6RootVec j, kernelRoots_e6RootVec ζ hζ v hj72 hjS⟩ : kernelRoots (e6Chi ζ v))
        (⟨e6RootVec k0, kernelRoots_e6RootVec ζ hζ v hk0_72 hk0S⟩ : kernelRoots (e6Chi ζ v)) :=
      eqvGen_of_reach ζ hζ v hk0_72 hk0S hj72 hjS hreach_k0j
    have hstep_k : Relation.EqvGen (e6Rel ζ v)
        (⟨e6RootVec k, kernelRoots_e6RootVec ζ hζ v hk72 hkS⟩ : kernelRoots (e6Chi ζ v))
        (⟨e6RootVec k0, kernelRoots_e6RootVec ζ hζ v hk0_72 hk0S⟩ : kernelRoots (e6Chi ζ v)) :=
      eqvGen_of_reach ζ hζ v hk0_72 hk0S hk72 hkS hreach
    exact Relation.EqvGen.trans _ _ _ hstep_j (Relation.EqvGen.symm _ _ hstep_k)

end CFSG.Assembly

end
