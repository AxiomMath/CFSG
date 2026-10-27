module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.UpperE7
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofComponentLift
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddCentralFixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2I163
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.SubsystemRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.TwoLocalLevi
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2U5Fam
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7Iso
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L122AProved
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InTorus
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotCentralizerYF3Exact
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClassesRoots
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotPositionB
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.C1PackS1531Top
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.InternalSecFF
public import CFSG.Quasithin.EmptyFaithful.R3cBlocks
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S146A2
public import CFSG.Quasithin.EmptyFaithful.S146ThreeB
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.S153D44
public import CFSG.Quasithin.EmptyFaithful.S153G27
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.EmptyFaithful.T1515cE
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.EmptyFaithful.T1531Final
public import CFSG.Quasithin.EmptyFaithful.T1531InspStmt
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
public import CFSG.Quasithin.SteinbergBKHigherElementaryThompson
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012Two
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.RankThree.Asc83Table.PermTables
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2
public import CFSG.RankThree.Chevalley.SteinbergBUF4B2QuarticDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicFourTools
public import CFSG.RankThree.PartOne.KE.E7FiveBlock
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.S15K.FamilyBlock
public import CFSG.RankThree.PartOne.S15K.FamilyHerm
public import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
public import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.PartOne.KE

def e7PairCheck (i j : Fin 7) : Bool :=
  (List.finRange 126).all fun m =>
    !(List.finRange 7).all (fun k => decide (k = i ∨ k = j ∨ e7RootVec m k = 0)) ||
    decide (e7RootVec m i = 0) || decide (e7RootVec m j = 0)

theorem e7PairCheck_correct {i j : Fin 7} (h : e7PairCheck i j = true) :
    ∀ γ : Fin Tag.E7.rank → ℤ, IsRoot Tag.E7 γ →
      (∀ k : Fin Tag.E7.rank, k ≠ i → k ≠ j → γ k = 0) →
      γ i = 0 ∨ γ j = 0 := by
  intro γ hγ hk
  obtain ⟨m, rfl⟩ := CFSG.RankThree.PartOne.KE.isRoot_iff_exists_e7RootVec.1 hγ
  rw [e7PairCheck, List.all_eq_true] at h
  have hm := h m (List.mem_finRange m)
  have hall : (List.finRange 7).all
      (fun k : Fin 7 => decide (k = i ∨ k = j ∨ e7RootVec m k = 0)) = true := by
    rw [List.all_eq_true]
    intro k _
    by_cases hki : k = i
    · exact decide_eq_true (Or.inl hki)
    · by_cases hkj : k = j
      · exact decide_eq_true (Or.inr (Or.inl hkj))
      · exact decide_eq_true (Or.inr (Or.inr (hk k hki hkj)))
  rw [hall] at hm
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at hm
  exact hm

theorem mem_a5Nodes_iff' (j : Fin Tag.E7.rank) :
    j ∈ a5Nodes Tag.E7 ↔ (j.val = 1 ∨ j.val = 3 ∨ j.val = 4 ∨ j.val = 5 ∨
      j.val = 6) := by
  rw [CFSG.RankThree.PartOne.KA5L.mem_a5Nodes_iff]

theorem fin_eq_of_val {b : Fin Tag.E7.rank} {k : ℕ} (hk : k < Tag.E7.rank)
    (h : b.val = k) : b = (⟨k, hk⟩ : Fin Tag.E7.rank) :=
  Fin.ext (by simpa using h)

macro "e7pc" i:num j:num : term =>
  `(e7PairCheck_correct (i := (⟨$i, by decide⟩ : Fin 7)) (j := (⟨$j, by decide⟩ : Fin 7))
    (by decide +kernel))

theorem commute_A1_0_A5 {K : Type} [Field K] :
    ∀ x ∈ subsystemGroup Tag.E7 K ({e7Index 0} : Set (Fin Tag.E7.rank)),
    ∀ y ∈ subsystemGroup Tag.E7 K (a5Nodes Tag.E7), Commute x y := by
  refine commute_subsystemGroup (τ := .E7) (K := K) ?_
  intro a ha b hb
  have ha' : a = e7Index 0 := by simpa using ha
  subst ha'
  rw [mem_a5Nodes_iff'] at hb
  rcases hb with h | h | h | h | h
  · have hb1 : b = (⟨1, by decide⟩ : Fin Tag.E7.rank) := fin_eq_of_val (by decide) (by simpa using h)
    subst hb1
    refine ⟨by decide, ?_⟩
    exact e7pc 0 1
  · have hb1 : b = (⟨3, by decide⟩ : Fin Tag.E7.rank) := fin_eq_of_val (by decide) (by simpa using h)
    subst hb1
    refine ⟨by decide, ?_⟩
    exact e7pc 0 3
  · have hb1 : b = (⟨4, by decide⟩ : Fin Tag.E7.rank) := fin_eq_of_val (by decide) (by simpa using h)
    subst hb1
    refine ⟨by decide, ?_⟩
    exact e7pc 0 4
  · have hb1 : b = (⟨5, by decide⟩ : Fin Tag.E7.rank) := fin_eq_of_val (by decide) (by simpa using h)
    subst hb1
    refine ⟨by decide, ?_⟩
    exact e7pc 0 5
  · have hb1 : b = (⟨6, by decide⟩ : Fin Tag.E7.rank) := fin_eq_of_val (by decide) (by simpa using h)
    subst hb1
    refine ⟨by decide, ?_⟩
    exact e7pc 0 6

theorem commute_sup_right {G : Type*} [Group G] {A B C : Subgroup G}
    (hAB : ∀ x ∈ A, ∀ y ∈ B, Commute x y) (hAC : ∀ x ∈ A, ∀ y ∈ C, Commute x y) :
    ∀ x ∈ A, ∀ y ∈ B ⊔ C, Commute x y := by
  intro x hx y hy
  have h1 : B ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (hAB x hx y hy).symm.eq
  have h2 : C ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (hAC x hx y hy).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (sup_le h1 h2 hy)).symm

theorem commute_A1_1_A2_13 {K : Type} [Field K] :
    ∀ x ∈ subsystemGroup Tag.E7 K ({e7Index 1} : Set (Fin Tag.E7.rank)),
    ∀ y ∈ subsystemGroup Tag.E7 K support13, Commute x y := by
  refine commute_subsystemGroup (τ := .E7) (K := K) ?_
  intro a ha b hb
  have ha' : a = e7Index 1 := by simpa using ha
  subst ha'
  rw [CFSG.RankThree.PartOne.KE.support13] at hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl
  · exact ⟨by decide, e7pc 1 0⟩
  · exact ⟨by decide, e7pc 1 2⟩

theorem commute_A1_1_A3_456 {K : Type} [Field K] :
    ∀ x ∈ subsystemGroup Tag.E7 K ({e7Index 1} : Set (Fin Tag.E7.rank)),
    ∀ y ∈ subsystemGroup Tag.E7 K
      ({CFSG.RankThree.PartOne.KA5L.a5chain 2, CFSG.RankThree.PartOne.KA5L.a5chain 3,
        CFSG.RankThree.PartOne.KA5L.a5chain 4} : Set (Fin Tag.E7.rank)), Commute x y := by
  refine commute_subsystemGroup (τ := .E7) (K := K) ?_
  intro a ha b hb
  have ha' : a = e7Index 1 := by simpa using ha
  subst ha'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl
  · exact ⟨by decide, e7pc 1 4⟩
  · exact ⟨by decide, e7pc 1 5⟩
  · exact ⟨by decide, e7pc 1 6⟩

theorem commute_A2_56_A4 {K : Type} [Field K] :
    ∀ x ∈ subsystemGroup Tag.E7 K
      ({CFSG.RankThree.PartOne.KA5L.a5chain 3, CFSG.RankThree.PartOne.KA5L.a5chain 4} :
        Set (Fin Tag.E7.rank)),
    ∀ y ∈ subsystemGroup Tag.E7 K
      ({e7Index 0, e7Index 1, e7Index 2, e7Index 3} : Set (Fin Tag.E7.rank)),
      Commute x y := by
  refine commute_subsystemGroup (τ := .E7) (K := K) ?_
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨by decide, e7pc 5 0⟩
  · exact ⟨by decide, e7pc 5 1⟩
  · exact ⟨by decide, e7pc 5 2⟩
  · exact ⟨by decide, e7pc 5 3⟩
  · exact ⟨by decide, e7pc 6 0⟩
  · exact ⟨by decide, e7pc 6 1⟩
  · exact ⟨by decide, e7pc 6 2⟩
  · exact ⟨by decide, e7pc 6 3⟩

theorem commute_A1_6_D5 {K : Type} [Field K] :
    ∀ x ∈ subsystemGroup Tag.E7 K ({e7Index 6} : Set (Fin Tag.E7.rank)),
    ∀ y ∈ subsystemGroup Tag.E7 K
      ({e7Index 0, e7Index 1, e7Index 2, e7Index 3, e7Index 4} : Set (Fin Tag.E7.rank)),
      Commute x y := by
  refine commute_subsystemGroup (τ := .E7) (K := K) ?_
  intro a ha b hb
  have ha' : a = e7Index 6 := by simpa using ha
  subst ha'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by decide, e7pc 6 0⟩
  · exact ⟨by decide, e7pc 6 1⟩
  · exact ⟨by decide, e7pc 6 2⟩
  · exact ⟨by decide, e7pc 6 3⟩
  · exact ⟨by decide, e7pc 6 4⟩

theorem not_dvd_card_inf_subsystemGroup {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hpq : ¬ p ∣ Nat.card K - 1)
    {J₁ J₂ : Set (Fin Tag.E7.rank)}
    (hcomm : ∀ x ∈ subsystemGroup Tag.E7 K J₁, ∀ y ∈ subsystemGroup Tag.E7 K J₂,
      Commute x y) :
    ¬ p ∣ Nat.card ↥(subsystemGroup Tag.E7 K J₁ ⊓ subsystemGroup Tag.E7 K J₂) := by
  haveI : Fintype K := Fintype.ofFinite K
  have hgcd : (Nat.card K - 1).gcd 2 = 1 := by
    obtain ⟨n, -, hK⟩ := FiniteField.card K 2
    have hKn : Nat.card K = 2 ^ (n : ℕ) := by
      rw [← Fintype.card_eq_nat_card]; exact hK
    rw [hKn]
    rw [Nat.gcd_comm]
    exact (Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one n.pos)).gcd_eq_one
  have hT : Nat.card (torusGroup Tag.E7 K) = (Nat.card K - 1) ^ 7 := by
    have h := CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_E7 (K := K)
    rw [hgcd, mul_one] at h
    exact h
  have hle : subsystemGroup Tag.E7 K J₁ ⊓ subsystemGroup Tag.E7 K J₂ ≤
      torusGroup Tag.E7 K := by
    rintro z ⟨hz1, hz2⟩
    have hz : (⟨z, hz1⟩ : subsystemGroup Tag.E7 K J₁) ∈
        Subgroup.center (subsystemGroup Tag.E7 K J₁) := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (hcomm w w.2 z hz2).eq
    exact supportedTorus_le_torusGroup J₁
      ((mem_center_subsystemGroup_iff (g := ⟨z, hz1⟩)).1 hz).1
  intro hd
  have hdvd0 : Nat.card ↥(subsystemGroup Tag.E7 K J₁ ⊓ subsystemGroup Tag.E7 K J₂) ∣
      Nat.card ↥(torusGroup Tag.E7 K) :=
    Subgroup.card_dvd_of_le (H := subsystemGroup Tag.E7 K J₁ ⊓ subsystemGroup Tag.E7 K J₂)
      (K := torusGroup Tag.E7 K) hle
  rw [hT] at hdvd0
  exact hpq (hp.dvd_of_dvd_pow (hd.trans hdvd0))

theorem card_le_pow_four_subsystemGroup_e7A1A5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K {j : Fin Tag.E7.rank | j.val ≠ 2})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 4 := by
  have hsub : ({j : Fin Tag.E7.rank | j.val ≠ 2} : Set (Fin Tag.E7.rank)) ⊆
      {e7Index 0} ∪ a5Nodes Tag.E7 := by
    intro j hj
    by_cases h0 : j.val = 0
    · left
      exact Fin.ext (by simpa [e7Index] using h0)
    · right
      rw [mem_a5Nodes_iff']
      fin_cases j <;> simp_all [a5Nodes]
  have hE' : E ≤ subsystemGroup Tag.E7 K ({e7Index 0} ∪ a5Nodes Tag.E7) :=
    hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hsub)
  rw [CFSG.StandardType.F4Rest.subsystemGroup_union] at hE'
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp
    (commute_A1_0_A5 (K := K))
    (not_dvd_card_inf_subsystemGroup hp hpq (commute_A1_0_A5 (K := K)))
    (bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e7node hp hp2 hpq (e7Index 0) hF hFel))
    (bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_three_subsystemGroup_e7a5 hp hp2 hpq hF hFel))
    hE' hEel
  exact h.trans (by norm_num : p ^ (1 + 3) ≤ p ^ 4)

theorem support13_union_A3_subset_e7a6 :
    (support13 ∪ ({CFSG.RankThree.PartOne.KA5L.a5chain 2,
      CFSG.RankThree.PartOne.KA5L.a5chain 3,
      CFSG.RankThree.PartOne.KA5L.a5chain 4} : Set (Fin Tag.E7.rank))) ⊆ e7a6support := by
  intro j hj
  rw [mem_e7a6support]
  rcases hj with hj | hj
  · rw [CFSG.RankThree.PartOne.KE.support13] at hj
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    rcases hj with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hj
    rcases hj with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

theorem commute_A1_1_sup_A2_A3 {K : Type} [Field K] :
    ∀ x ∈ subsystemGroup Tag.E7 K ({e7Index 1} : Set (Fin Tag.E7.rank)),
    ∀ y ∈ subsystemGroup Tag.E7 K
      (support13 ∪ ({CFSG.RankThree.PartOne.KA5L.a5chain 2,
        CFSG.RankThree.PartOne.KA5L.a5chain 3,
        CFSG.RankThree.PartOne.KA5L.a5chain 4} : Set (Fin Tag.E7.rank))),
      Commute x y := by
  rw [CFSG.StandardType.F4Rest.subsystemGroup_union]
  exact commute_sup_right (commute_A1_1_A2_13 (K := K)) (commute_A1_1_A3_456 (K := K))

theorem card_le_pow_three_subsystemGroup_e7A2A3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K
      (support13 ∪ ({CFSG.RankThree.PartOne.KA5L.a5chain 2,
        CFSG.RankThree.PartOne.KA5L.a5chain 3,
        CFSG.RankThree.PartOne.KA5L.a5chain 4} : Set (Fin Tag.E7.rank))))
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 3 :=
  card_le_pow_three_subsystemGroup_e7a6 hp hp2 hpq
    (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono support13_union_A3_subset_e7a6)) hEel

theorem card_le_pow_five_subsystemGroup_e7A1A2A3 {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K {j : Fin Tag.E7.rank | j.val ≠ 3})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 5 := by
  have hsub : ({j : Fin Tag.E7.rank | j.val ≠ 3} : Set (Fin Tag.E7.rank)) ⊆
      {e7Index 1} ∪ (support13 ∪ ({CFSG.RankThree.PartOne.KA5L.a5chain 2,
        CFSG.RankThree.PartOne.KA5L.a5chain 3,
        CFSG.RankThree.PartOne.KA5L.a5chain 4} : Set (Fin Tag.E7.rank))) := by
    intro j hj
    by_cases h1 : j.val = 1
    · left
      exact fin_eq_of_val (by decide) (by simpa using h1)
    · right
      simp only [Set.mem_union, CFSG.RankThree.PartOne.KE.support13, Set.mem_insert_iff,
        Set.mem_singleton_iff]
      fin_cases j <;>
        first
          | exact Or.inl (Or.inl rfl)
          | exact Or.inl (Or.inr rfl)
          | exact Or.inr (Or.inl rfl)
          | exact Or.inr (Or.inr (Or.inl rfl))
          | exact Or.inr (Or.inr (Or.inr rfl))
          | simp_all
  have hE' : E ≤ subsystemGroup Tag.E7 K
      ({e7Index 1} ∪ (support13 ∪ ({CFSG.RankThree.PartOne.KA5L.a5chain 2,
        CFSG.RankThree.PartOne.KA5L.a5chain 3,
        CFSG.RankThree.PartOne.KA5L.a5chain 4} : Set (Fin Tag.E7.rank)))) :=
    hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hsub)
  rw [CFSG.StandardType.F4Rest.subsystemGroup_union] at hE'
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp
    (commute_A1_1_sup_A2_A3 (K := K))
    (not_dvd_card_inf_subsystemGroup hp hpq (commute_A1_1_sup_A2_A3 (K := K)))
    (bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e7node hp hp2 hpq (e7Index 1) hF hFel))
    (bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_three_subsystemGroup_e7A2A3 hp hp2 hpq hF hFel))
    hE' hEel
  exact h.trans (by
    show p ^ 4 ≤ p ^ 5
    exact Nat.pow_le_pow_right hp.pos (by norm_num))

theorem card_le_pow_five_subsystemGroup_e7A2A4 {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ n + 1) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K {j : Fin Tag.E7.rank | j.val ≠ 4})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 5 := by
  have hsub : ({j : Fin Tag.E7.rank | j.val ≠ 4} : Set (Fin Tag.E7.rank)) ⊆
      ({CFSG.RankThree.PartOne.KA5L.a5chain 3, CFSG.RankThree.PartOne.KA5L.a5chain 4} :
        Set (Fin Tag.E7.rank)) ∪
      {e7Index 0, e7Index 1, e7Index 2, e7Index 3} := by
    intro j hj
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases j <;>
      first
        | exact Or.inl (Or.inl rfl)
        | exact Or.inl (Or.inr rfl)
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr (Or.inl rfl))
        | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
        | simp_all
  have hE' : E ≤ subsystemGroup Tag.E7 K
      (({CFSG.RankThree.PartOne.KA5L.a5chain 3, CFSG.RankThree.PartOne.KA5L.a5chain 4} :
        Set (Fin Tag.E7.rank)) ∪ {e7Index 0, e7Index 1, e7Index 2, e7Index 3}) :=
    hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hsub)
  rw [CFSG.StandardType.F4Rest.subsystemGroup_union] at hE'
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp
    (commute_A2_56_A4 (K := K))
    (not_dvd_card_inf_subsystemGroup hp hpq (commute_A2_56_A4 (K := K)))
    (bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e7a2_56 hp hp2 hpq hF hFel))
    (bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_four_subsystemGroup_e7A4 hK hp hp2 hd hF hFel))
    hE' hEel
  exact h.trans (le_refl _)

theorem card_le_pow_five_subsystemGroup_e7A1D5 {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ n + 1) (hpq : ¬ p ∣ Nat.card K - 1)
    {E : Subgroup (ModGL Tag.E7 K)}
    (hE : E ≤ subsystemGroup Tag.E7 K {j : Fin Tag.E7.rank | j.val ≠ 5})
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 5 := by
  have hsub : ({j : Fin Tag.E7.rank | j.val ≠ 5} : Set (Fin Tag.E7.rank)) ⊆
      {e7Index 6} ∪ {e7Index 0, e7Index 1, e7Index 2, e7Index 3, e7Index 4} := by
    intro j hj
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
    fin_cases j <;>
      first
        | exact Or.inl rfl
        | exact Or.inr (Or.inl rfl)
        | exact Or.inr (Or.inr (Or.inl rfl))
        | exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        | simp_all
  have hE' : E ≤ subsystemGroup Tag.E7 K
      ({e7Index 6} ∪ {e7Index 0, e7Index 1, e7Index 2, e7Index 3, e7Index 4}) :=
    hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hsub)
  rw [CFSG.StandardType.F4Rest.subsystemGroup_union] at hE'
  have h := card_le_pow_add_of_le_sup_of_not_dvd_inf (p := p) hp
    (commute_A1_6_D5 (K := K))
    (not_dvd_card_inf_subsystemGroup hp hpq (commute_A1_6_D5 (K := K)))
    (bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_one_subsystemGroup_e7node hp hp2 hpq (e7Index 6) hF hFel))
    (bound_subgroup_of_ambient (fun F hF hFel =>
      card_le_pow_four_subsystemGroup_e7D5 hK hp hp2 hd hF hFel))
    hE' hEel
  exact h.trans (le_refl _)

theorem rk2_levi_explicit (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ (F : Type) [Field F] [Finite F] [CharP F 2], p ∣ Nat.card F + 1 →
    ∀ (i : Fin Tag.E7.rank), i ≠ (0 : Fin 7) → i ≠ (1 : Fin 7) → i ≠ (6 : Fin 7) →
      ∀ E : Subgroup (ModGL Tag.E7 F), E ≤ subsystemGroup Tag.E7 F {j | j ≠ i} →
        IsElemAbelian p E → Nat.card E ≤ p ^ 6 :=
  fun F hF hFin hCh hd i hi0 hi1 hi6 E hE hEel => by
  letI : Field F := hF
  letI : Finite F := hFin
  haveI : CharP F 2 := hCh
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨n, -, hK⟩ := FiniteField.card F 2
  have hKn : Nat.card F = 2 ^ (n : ℕ) := by
    rw [← Fintype.card_eq_nat_card]; exact hK
  have hd' : p ∣ 2 ^ (n : ℕ) + 1 := by rw [← hKn]; exact hd
  have hpq : ¬ p ∣ Nat.card F - 1 := by
    intro h1
    have h1' : p ∣ 2 ^ (n : ℕ) - 1 := by rwa [hKn] at h1
    have h1'' : rk2Ord p n = 1 := rk2Ord_eq_one_iff.2 h1'
    have h2 : rk2Ord p n = 2 := (rk2Ord_eq_two_iff hp hp2).2 hd'
    omega
  have h0 : i.val ≠ 0 := fun h => hi0 (fin_eq_of_val (by decide) h)
  have h1 : i.val ≠ 1 := fun h => hi1 (fin_eq_of_val (by decide) h)
  have h6 : i.val ≠ 6 := fun h => hi6 (fin_eq_of_val (by decide) h)
  have hlt7 : i.val < 7 := lt_of_lt_of_le i.isLt (le_of_eq (by rfl : Tag.E7.rank = 7))
  have hival : i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 := by omega
  rcases hival with h2 | h3 | h4 | h5
  · have hi : i = e7Index 2 := fin_eq_of_val (by decide) h2
    have hset : ({j : Fin Tag.E7.rank | j ≠ i} : Set (Fin Tag.E7.rank)) =
        {j : Fin Tag.E7.rank | j.val ≠ 2} := by
      ext j
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
      constructor
      · intro h hval
        exact h (by rw [hi]; exact fin_eq_of_val (by decide) hval)
      · intro h heq
        exact h (by rw [heq, hi]; rfl)
    rw [hset] at hE
    exact (card_le_pow_four_subsystemGroup_e7A1A5 hp hp2 hpq hE hEel).trans (by
      show p ^ 4 ≤ p ^ 6
      exact Nat.pow_le_pow_right hp.pos (by norm_num))
  · have hi : i = e7Index 3 := fin_eq_of_val (by decide) h3
    have hset : ({j : Fin Tag.E7.rank | j ≠ i} : Set (Fin Tag.E7.rank)) =
        {j : Fin Tag.E7.rank | j.val ≠ 3} := by
      ext j
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
      constructor
      · intro h hval
        exact h (by rw [hi]; exact fin_eq_of_val (by decide) hval)
      · intro h heq
        exact h (by rw [heq, hi]; rfl)
    rw [hset] at hE
    exact (card_le_pow_five_subsystemGroup_e7A1A2A3 hp hp2 hpq hE hEel).trans (by
      show p ^ 5 ≤ p ^ 6
      exact Nat.pow_le_pow_right hp.pos (by norm_num))
  · have hi : i = e7Index 4 := fin_eq_of_val (by decide) h4
    have hset : ({j : Fin Tag.E7.rank | j ≠ i} : Set (Fin Tag.E7.rank)) =
        {j : Fin Tag.E7.rank | j.val ≠ 4} := by
      ext j
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
      constructor
      · intro h hval
        exact h (by rw [hi]; exact fin_eq_of_val (by decide) hval)
      · intro h heq
        exact h (by rw [heq, hi]; rfl)
    rw [hset] at hE
    exact (card_le_pow_five_subsystemGroup_e7A2A4 hKn hp hp2 hd' hpq hE hEel).trans (by
      show p ^ 5 ≤ p ^ 6
      exact Nat.pow_le_pow_right hp.pos (by norm_num))
  · have hi : i = e7Index 5 := fin_eq_of_val (by decide) h5
    have hset : ({j : Fin Tag.E7.rank | j ≠ i} : Set (Fin Tag.E7.rank)) =
        {j : Fin Tag.E7.rank | j.val ≠ 5} := by
      ext j
      rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
      constructor
      · intro h hval
        exact h (by rw [hi]; exact fin_eq_of_val (by decide) hval)
      · intro h heq
        exact h (by rw [heq, hi]; rfl)
    rw [hset] at hE
    exact (card_le_pow_five_subsystemGroup_e7A1D5 hKn hp hp2 hd' hpq hE hEel).trans (by
      show p ^ 5 ≤ p ^ 6
      exact Nat.pow_le_pow_right hp.pos (by norm_num))

theorem levi_card_le_six_explicit {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    (hLev : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], p ∣ Nat.card F + 1 →
      ∀ (i : Fin Tag.E7.rank), i ≠ (0 : Fin 7) → i ≠ (1 : Fin 7) → i ≠ (6 : Fin 7) →
        ∀ E : Subgroup (ModGL Tag.E7 F), E ≤ subsystemGroup Tag.E7 F {j | j ≠ i} →
          IsElemAbelian p E → Nat.card E ≤ p ^ 6)
    {J : Set (Fin Tag.E7.rank)} (hJ : J ≠ Set.univ)
    {E : Subgroup (ModGL Tag.E7 K)} (hE : E ≤ subsystemGroup Tag.E7 K J)
    (hEel : IsElemAbelian p E) : Nat.card E ≤ p ^ 6 := by
  haveI : Fintype K := Fintype.ofFinite K
  have hpq : ¬ p ∣ Nat.card K - 1 :=
    CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos (by have := hp.two_le; omega) hd
  obtain ⟨i, hi⟩ : ∃ i, i ∉ J := by
    by_contra hall
    push Not at hall
    exact hJ (Set.eq_univ_of_forall hall)
  by_cases hi0 : i = (0 : Fin 7)
  · have hJ0 : J ⊆ {j | j ≠ (0 : Fin 7)} := by
      intro j hj hji
      exact hi (hi0.symm ▸ (hji ▸ hj))
    exact card_le_pow_six_subsystemGroup_e7D6 hp hp2 hd
      (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ0)) hEel
  · by_cases hi1 : i = (1 : Fin 7)
    · subst hi1
      have hJ1 : J ⊆ e7a6support := by
        intro j hj
        have hj1 : j ≠ (1 : Fin 7) := fun h => hi (h ▸ hj)
        rw [mem_e7a6support]
        fin_cases j
        · exact Or.inl rfl
        · exact absurd rfl hj1
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      exact card_le_pow_six_subsystemGroup_e7a6 hp hp2 hpq
        (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono hJ1)) hEel
    · by_cases hi6 : i = (6 : Fin 7)
      · subst hi6
        obtain ⟨n, -, hK⟩ := FiniteField.card K 2
        have hKn : Nat.card K = 2 ^ (n : ℕ) := by
          rw [← Fintype.card_eq_nat_card]; exact hK
        have hd' : p ∣ 2 ^ (n : ℕ) + 1 := by rw [← hKn]; exact hd
        exact (card_le_pow_four_subsystemGroup_e7E6 hKn hp hp2 hd'
          (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono (fun j hj hji => hi (hji ▸ hj)))) hEel).trans
          (Nat.pow_le_pow_right hp.pos (by norm_num : 4 ≤ 6))
      · exact hLev K hd i hi0 hi1 hi6 E
          (hE.trans (CFSG.StandardType.F4Rest.subsystemGroup_mono (fun j hj hji => hi (hji ▸ hj)))) hEel

theorem twoLocalRank_le_six_explicit {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hd : p ∣ Nat.card K + 1)
    (hLev : ∀ (F : Type) [Field F] [Finite F] [CharP F 2], p ∣ Nat.card F + 1 →
      ∀ (i : Fin Tag.E7.rank), i ≠ (0 : Fin 7) → i ≠ (1 : Fin 7) → i ≠ (6 : Fin 7) →
        ∀ E : Subgroup (ModGL Tag.E7 F), E ≤ subsystemGroup Tag.E7 F {j | j ≠ i} →
          IsElemAbelian p E → Nat.card E ≤ p ^ 6) :
    GLATwoLocalRank p (adjointGroup Tag.E7 K) ≤ 6 :=
  twoLocalRank_le_of_elemAbelian_bound hp fun R E hR hR2 hER hE =>
    twoLocal_card_le_of_levi' hp hp2
      (CFSG.RankThree.PartOne.S15K.not_dvd_sub_one_of_dvd_add_one Nat.card_pos
        (by have := hp.two_le; omega) hd)
      (fun J hJ E hE hEel => levi_card_le_six_explicit hp hp2 hd hLev hJ hE hEel) hR hR2 hER hE

theorem rk2_up_e7 {K : Type} [Group K] [Finite K] {lab : GLALabel} (hK : Rk2IsLabel K lab)
    (ht : lab.tag = .E7) (hn : 2 ≤ lab.n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hd : p ∣ 2 ^ lab.n + 1) : GLATwoLocalRank p K < rk2LieRank lab := by
  obtain ⟨hQ, -, hM⟩ := rk2_model_of_isLabel hK
  have hM' : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .E7 0 2 lab.n :=
    lieModel_of_markedModel_E7 ht hM
  obtain ⟨-, F, hF, hFin, hFcard, ⟨φ⟩⟩ := hM'.chevalleyExceptionalModel
    (by decide : StatedLieTag.E7 ∈ CFSG.Blueprint.chevalleyExceptionalTags)
  letI : Field F := hF
  letI : Finite F := hFin
  have hn1 : 1 ≤ lab.n := by omega
  haveI : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (k := lab.n) hn1 hFcard
  have hQ' : CFSG.IsQuasisimple K := (CFSG.Foundations.SteinbergCA.quasisimple_iff K).2.2.1.2 hQ
  have hZ : Subgroup.center K = ⊥ :=
    CFSG.HardMathSupport.Meierfrankenfeld.Proving.E7Curtis.center_eq_bot_of_E7 hQ' hn1 hFcard φ
  let χ : AdjointQuotient .E7 F ≃* adjointGroup Tag.E7 F :=
    (QuotientGroup.quotientMulEquivOfEq
      (center_adjointGroup_eq_bot (τ := Tag.E7) (K := F))).trans QuotientGroup.quotientBot
  let eK : K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq (by rw [hZ]))
  let e : K ≃* adjointGroup Tag.E7 F := (eK.trans φ).trans χ
  have hGL : GLATwoLocalRank p K = GLATwoLocalRank p (adjointGroup Tag.E7 F) :=
    le_antisymm (rk2_twoLocal_equiv_le hp e) (rk2_twoLocal_equiv_le hp e.symm)
  have hdF : p ∣ Nat.card F + 1 := by rw [hFcard]; exact hd
  have hbound := twoLocalRank_le_six_explicit (K := F) hp hp2 hdF (rk2_levi_explicit p hp hp2)
  have h7 : rk2LieRank lab = 7 := by rw [rk2LieRank, ht]
  rw [hGL, h7]
  exact lt_of_le_of_lt hbound (by norm_num)

end CFSG.LocalAnalysis.GLTheoremA
