module

public import CFSG.ClassicalInvolution.Q3.Q3NSFuzzy
public import CFSG.ClassicalInvolution.Q3.Q3ALPre
public import CFSG.ClassicalInvolution.Q3.Q3PStage

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3NS

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.RouteD
open scoped MatrixGroups commutatorElement

section Gorenstein

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_of_alphaCore_eq_bot3 {J : Subgroup G} {z₁ z₂ : G}
    (hJ : IsClassicalMember3 J z₁) (hz₂ : z₂ ∈ trivialOnQuot J) (hz₂sq : z₂ * z₂ = 1)
    (hz₁ne : z₁ ≠ 1) (hα : alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) = ⊥) :
    ∀ x ∈ J, z₂ * x = x * z₂ := by
  intro x hx
  have hA : IsPGroup 2 (Subgroup.zpowers z₂) := isPGroup_zpowers_of_mul_self_eq_one hz₂sq
  have hAJ : Subgroup.zpowers z₂ ≤ trivialOnQuot J := Subgroup.zpowers_le.mpr hz₂
  obtain ⟨h, hh, n, hn, hxhn⟩ := exists_mem_inf_centralizer_mul hA hAJ hx
  have hn1 : n ∈ oddCoreIn (Subgroup.centralizer ({z₁} : Set G)) :=
    oddCoreIn_le_of_isSubnormal hJ.subnormal hn
  have hz₁F : z₁ ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure (by simp)
  have hz₂F : z₂ ∈ Subgroup.closure ({z₁, z₂} : Set G) := Subgroup.subset_closure (by simp)
  have hcomm : ⁅n, z₂⁆ ∈ alphaCore (Subgroup.closure ({z₁, z₂} : Set G)) :=
    commutator_le_alphaCore (Subgroup.commutator_mem_commutator
      (involutionOddCore_le_uCore hz₁F hz₁ne hn1) hz₂F)
  rw [hα, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm
  have hh' : z₂ * h = h * z₂ :=
    Subgroup.mem_centralizer_iff.mp hh.2 z₂ (Subgroup.mem_zpowers z₂)
  calc z₂ * x = z₂ * (h * n) := by rw [hxhn]
    _ = (z₂ * h) * n := by rw [mul_assoc]
    _ = (h * z₂) * n := by rw [hh']
    _ = h * (z₂ * n) := by rw [mul_assoc]
    _ = h * (n * z₂) := by rw [← hcomm]
    _ = x * z₂ := by rw [← mul_assoc, ← hxhn]

end Gorenstein

section Statements


@[expose] def NTNoFuzzyFrame3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTHyps3 K z →
    ∀ A : Subgroup G, ¬ FuzzyFrame3 (conjClass3 K) A

@[expose] def NTFuzzyBalance3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTHyps3 K z →
    ∀ A : Subgroup G, FuzzyFrame3 (conjClass3 K) A → RankThreeBalance A

@[expose] def NTFuzzyGeneration3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (K : Subgroup G) (z : G), NTHyps3 K z →
    ∀ A : Subgroup G, FuzzyFrame3 (conjClass3 K) A → rankTwoSpan A = ⊤

@[expose] def NTOddThreeFree3 : Prop :=
  Q3AL.OddThreeFreePre3 fun K _ => BootData3 (conjClass3 K) ∧ ¬ IndepTriple3 (conjClass3 K)

theorem ntNoCommImages3_of_uniq_nff (hU : NTUniqPair3) (hF : NTNoFuzzyFrame3) :
    NTNoCommImages3 := by
  intro G _ _ _ K z h N₁ N₂ n₁ n₂ fp
  obtain ⟨A, hA⟩ := fuzzyFrame3_of_fuzzyPair hU h.common fp
  exact hF G K z h A hA

end Statements

section Reduction


variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem ntNoFuzzyFrame3_of_balance_generation (h1 : NTFuzzyBalance3) (h2 : NTFuzzyGeneration3)
    (h3 : NTOddThreeFree3) : NTNoFuzzyFrame3 := by
  intro G _ _ _ K z h A hA
  have hbal := h1 G K z h A hA
  have hgen := h2 G K z h A hA
  obtain ⟨J, a, hJ, hAdef, hAe, hAc, hAt⟩ := hA
  have hΩ := h.common.inClass
  have hIH := h.common.lieSystems
  have hnab := h.common.nonab
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hsq : ∀ i, a i * a i = 1 := fun i => mul_self_eq_one_of_member (hJ i).2
  have hne1 : ∀ i, a i ≠ 1 := fun i => (hJ i).2.ne_one
  have haA : ∀ i, a i ∈ A := fun i => hAdef ▸ Subgroup.subset_closure ⟨i, rfl⟩
  have hcomm : ∀ i j, a i * a j = a j * a i := fun i j =>
    congrArg Subtype.val (hAe.1.is_comm.comm (⟨a i, haA i⟩ : A) ⟨a j, haA j⟩)
  have hrange : Set.range a = ({a 0, a 1, a 2} : Set G) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  have hdep : ¬ (a 0 = a 1 ∨ a 0 = a 2 ∨ a 1 = a 2 ∨ a 0 * a 1 = a 2) := fun hd => by
    have := card_closure_triple_le_four (hsq 0) (hsq 1) (hsq 2) (hcomm 0 1) (hcomm 0 2)
      (hcomm 1 2) hd
    rw [← hrange, ← hAdef, hAc] at this
    omega
  have hneq : ∀ i j : Fin 3, i ≠ j → a i ≠ a j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    all_goals first
      | exact absurd rfl hij
      | exact fun e => hdep (Or.inl e)
      | exact fun e => hdep (Or.inr (Or.inl e))
      | exact fun e => hdep (Or.inr (Or.inr (Or.inl e)))
      | exact fun e => hdep (Or.inl e.symm)
      | exact fun e => hdep (Or.inr (Or.inl e.symm))
      | exact fun e => hdep (Or.inr (Or.inr (Or.inl e.symm)))
  have hα : ∀ i j : Fin 3, i ≠ j → alphaCore (Subgroup.closure ({a i, a j} : Set G)) = ⊥ := by
    intro i j hij
    have hle : Subgroup.closure ({a i, a j} : Set G) ≤ A := (Subgroup.closure_le _).mpr (by
      rintro s (rfl | hs)
      · exact haA i
      · rw [Set.mem_singleton_iff.mp hs]
        exact haA j)
    have hcard : Nat.card (Subgroup.closure ({a i, a j} : Set G)) = 4 :=
      card_closure_pair_eq_four (hsq i) (hsq j) (hne1 i) (hne1 j) (hneq i j hij) (hcomm i j)
    exact (⟨hle, hbal, hgen⟩ : EdgeAxis3 (a i) (a j) A).alphaCore_eq_bot hnab
      ⟨hle, by rw [hcard]; norm_num⟩
  have hcent : ∀ i j : Fin 3, i ≠ j → ∀ x ∈ J i, a j * x = x * a j := fun i j hij =>
    mem_centralizer_of_alphaCore_eq_bot3 (hJ i).2 (hAt i (haA j)) (hsq j) (hne1 i) (hα i j hij)
  have hcentJ : ∀ i j : Fin 3, i ≠ j → J i ≤ Subgroup.centralizer ({a j} : Set G) :=
    fun i j hij x hx => Subgroup.mem_centralizer_singleton_iff.mpr (hcent i j hij x hx).symm
  have hcentI : ∀ i : Fin 3, J i ≤ Subgroup.centralizer ({a i} : Set G) :=
    fun i => isSubnormal_le (hJ i).2.subnormal
  have hnc : ∀ f : G, f ≠ 1 → f ∉ Subgroup.center G := fun f hf1 hfc =>
    not_subset_center_of_ne_one hnab hf1 (Set.singleton_subset_iff.mpr hfc)
  have hex : ∀ i : Fin 3, classicalInvolutionOddCore ↥(J i) = ⊥ := by
    intro i
    obtain ⟨j, hij⟩ : ∃ j : Fin 3, i ≠ j := by
      fin_cases i
      exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
    refine classicalInvolutionOddCore_eq_bot_of_deltaCore_eq_bot₃ hΩ.conjInvariant hIH (hJ i).1
      (hJ i).2 (Q3NT.le_centralizer_closure_pair (hcentI i) (hcentJ i j hij))
      (fun f _ hf1 => hnc f hf1) ?_
    exact le_bot_iff.mp (by simpa [hα i j hij] using (deltaCore_le_alphaCore
      (F := Subgroup.closure ({a i, a j} : Set G))))
  have hexact : ExactMembers3 (conjClass3 K) := by
    obtain ⟨b, hb⟩ := (hJ 0).1
    refine exactMembers3_of_conjugates (hex 0) fun L hL => ?_
    obtain ⟨c, rfl⟩ := hL
    refine ⟨c * b⁻¹, ?_⟩
    show conjSub c K = conjSub (c * b⁻¹) (J 0)
    rw [← hb, ← conjSub_mul]
    simp
  have h3z : Q3W.LocalOddThreeFree3 (conjClass3 K) z :=
    h3 G hnab K z h.common.cls h.common.below h.common.rank h.common.large h.common.delta
      ⟨h.data, h.noTriple⟩ hexact
  have h3a : ∀ j : Fin 3, Q3W.LocalOddThreeFree3 (conjClass3 K) (a j) := by
    intro j
    obtain ⟨g, -, hg⟩ := conjClass3_involution h.common.cls (hJ j).1 (hJ j).2
    rw [hg]
    exact Q3W.localOddThreeFree3_conj hΩ.conjInvariant g z h3z
  have hC : ∀ i j : Fin 3, i ≠ j → Commutes (J j) (J i) := fun i j hij =>
    Q3AL.commutes_of_exact_threeFree hMFZ hnab hIH (hJ j).1 (hJ i).1 (hJ j).2 (hJ i).2
      (hneq j i (Ne.symm hij)) (hcentJ i j hij) (hex j) (h3a j)
  have hsymm : ∀ {P Q : Subgroup G}, Commutes P Q → Commutes Q P :=
    fun hPQ y hy x hx => (hPQ x hx y hy).symm
  have T : ExactTriple (J 0) (J 1) (J 2) (a 0) (a 1) (a 2) :=
    { mem₁ := (hJ 0).2.mem
      mem₂ := (hJ 1).2.mem
      mem₃ := (hJ 2).2.mem
      central₁ := fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hcentI 0 hk)
      central₂ := fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hcentI 1 hk)
      central₃ := fun k hk => Subgroup.mem_centralizer_singleton_iff.mp (hcentI 2 hk)
      sq₁ := hsq 0
      sq₂ := hsq 1
      sq₃ := hsq 2
      ne_one₁ := hne1 0
      ne_one₂ := hne1 1
      ne_one₃ := hne1 2
      comm₁₂ := hC 1 0 (by decide)
      comm₁₃ := hC 2 0 (by decide)
      comm₂₃ := hC 2 1 (by decide)
      ne₁₂ := hneq 0 1 (by decide)
      ne₁₃ := hneq 0 2 (by decide)
      ne₂₃ := hneq 1 2 (by decide) }
  exact h.noTriple (IndepTriple3.of_exactTriple T
    (fun e => hdep (Or.inr (Or.inr (Or.inr e)))) (hJ 0) (hJ 1) (hJ 2))

theorem ntNoCommImages3_of_uniq_balance_generation (hU : NTUniqPair3) (h1 : NTFuzzyBalance3)
    (h2 : NTFuzzyGeneration3) (h3 : NTOddThreeFree3) : NTNoCommImages3 :=
  ntNoCommImages3_of_uniq_nff hU (ntNoFuzzyFrame3_of_balance_generation h1 h2 h3)

theorem ntResiduals3_of_fuzzy (hU : NTUniqPair3) (h1 : NTFuzzyBalance3) (h2 : NTFuzzyGeneration3)
    (h3 : NTOddThreeFree3) (twinsCommute : NTTwinsCommute3) (noAllA1 : NTNoAllA1_3)
    (noM11 : NTNoM11_3) (noG2D4 : NTNoG2D4_3) (noM3Twin : NTNoM3Twin_3)
    (noSmallSingle : NTNoSmallSingle_3) (noManyTwins : NTNoManyTwins_3) : NTResiduals3 :=
  ⟨ntNoCommImages3_of_uniq_balance_generation hU h1 h2 h3, twinsCommute, noAllA1, noM11, noG2D4,
    noM3Twin, noSmallSingle, noManyTwins⟩

end Reduction

end CFSG.ClassicalInvolution.Q3.Q3NS
