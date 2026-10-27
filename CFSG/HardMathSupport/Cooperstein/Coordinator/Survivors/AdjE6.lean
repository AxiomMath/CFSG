module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.AdjType
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.Weyl

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

@[expose] def e6Theta0 : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

@[expose] abbrev e6node20 : Fin Tag.E6.rank := ⟨1, by decide⟩

theorem e6_check_two : ∀ i : Fin Tag.E6.rank,
    List.ofFn (Pi.single i 1 + Pi.single i 1 : Fin Tag.E6.rank → ℤ) ∉ Tag.E6.artifactRoots := by
  decide +kernel

theorem e6_check_string : ∀ k < Tag.E6.rootCount, ∀ i : Fin Tag.E6.rank,
    (Tag.rootCertificate Tag.E6).root k = Pi.single i 1 ∨
      (Tag.rootCertificate Tag.E6).root k = -Pi.single i 1 ∨
        (Tag.stringData Tag.E6).up k i + (Tag.stringData Tag.E6).down k i ≤ 1 := by
  decide +kernel

theorem e6_check_succ : ∀ k < Tag.E6.rootCount, (Tag.rootCertificate Tag.E6).root k = e6Theta0 ∨
    (∃ j : Fin Tag.E6.rank, (Tag.rootCertificate Tag.E6).root k = -Pi.single j 1) ∨
      ∃ i : Fin Tag.E6.rank, (Tag.rootCertificate Tag.E6).root k ≠ Pi.single i 1 ∧
        (Tag.rootCertificate Tag.E6).root k ≠ -Pi.single i 1 ∧
          1 ≤ (Tag.stringData Tag.E6).up k i := by
  decide +kernel

@[expose] def e6Theta : Fin TwistTag.E6.tag.rank → ℤ := e6Theta0

@[expose] abbrev e6node2 : Fin TwistTag.E6.tag.rank := e6node20

theorem adjHyp_E6 : AdjHyp TwistTag.E6.tag e6Theta :=
  AdjHyp.of_checks e6_check_two e6_check_string e6_check_succ

theorem e6_theta_mem : List.ofFn e6Theta0 ∈ Tag.E6.artifactRoots := by decide +kernel

theorem e6_check_not_succ : ∀ i : Fin Tag.E6.rank,
    List.ofFn (e6Theta0 + Pi.single i 1) ∉ Tag.E6.artifactRoots := by decide +kernel

theorem e6_check_sub : List.ofFn (e6Theta0 - Pi.single e6node20 1) ∈ Tag.E6.artifactRoots := by
  decide +kernel

theorem e6_check_ne : (∀ i : Fin Tag.E6.rank, e6Theta0 ≠ Pi.single i 1) ∧
    (∀ i : Fin Tag.E6.rank, e6Theta0 ≠ -Pi.single i 1) ∧
    (e6Theta0 - Pi.single e6node20 1 ≠ Pi.single e6node20 1) ∧
    (e6Theta0 - Pi.single e6node20 1 ≠ -Pi.single e6node20 1) := by
  decide +kernel

theorem e6_check_reflect : (∀ i : Fin Tag.E6.rank, i ≠ e6node20 → reflect .E6 i e6Theta0 = e6Theta0) ∧
    reflect .E6 e6node20 e6Theta0 = e6Theta0 - Pi.single e6node20 1 := by
  decide +kernel

theorem e6_check_weight : ∀ s : Fin Tag.E6.rank,
    ∑ j, Tag.E6.cartan s j * e6Theta0 j = if s = e6node20 then 1 else 0 := by
  decide +kernel

theorem adjTop_E6 : AdjTop TwistTag.E6.tag e6Theta e6node2 where
  root := isRoot_iff_mem_artifactRoots.2 e6_theta_mem
  hyp := adjHyp_E6
  not_succ i := fun h => e6_check_not_succ i (isRoot_iff_mem_artifactRoots.1 h)
  ne_single := e6_check_ne.1
  ne_neg := e6_check_ne.2.1
  reflect_ne := e6_check_reflect.1
  reflect_node := e6_check_reflect.2
  root_sub := isRoot_iff_mem_artifactRoots.2 e6_check_sub
  sub_ne_single := e6_check_ne.2.2.1
  sub_ne_neg := e6_check_ne.2.2.2
  weight := e6_check_weight

theorem cartan6_symm (i j : Fin Tag.E6.rank) : Tag.E6.cartan i j = Tag.E6.cartan j i := by
  have h : ∀ i j : Fin Tag.E6.rank, Tag.E6.cartan i j - Tag.E6.cartan j i = 0 := by decide +kernel
  exact sub_eq_zero.1 (h i j)

theorem cartan6_vals : ∀ i j : Fin Tag.E6.rank,
    (Tag.E6.cartan i j - 2) * (Tag.E6.cartan i j + 1) * Tag.E6.cartan i j = 0 := by
  decide +kernel

@[expose] def e6Omega3 : Fin Tag.E6.rank → Fin Tag.E6.rank → ℤ :=
  ![![4, 3, 5, 6, 4, 2], ![3, 6, 6, 9, 6, 3], ![5, 6, 10, 12, 8, 4], ![6, 9, 12, 18, 12, 6],
    ![4, 6, 8, 12, 10, 5], ![2, 3, 4, 6, 5, 4]]

theorem e6Omega3_mul_cartan : ∀ l j : Fin Tag.E6.rank,
    ∑ c, e6Omega3 c l * Tag.E6.cartan c j = if l = j then 3 else 0 := by
  decide +kernel

theorem natAbs_cartan6_cast {F : Type} [Field F] [CharP F 2] (i j : Fin Tag.E6.rank) :
    (((Tag.E6.cartan i j).natAbs : ℕ) : F) = ((Tag.E6.cartan i j : ℤ) : F) := by
  have h : Tag.E6.cartan i j = 2 ∨ Tag.E6.cartan i j = -1 ∨ Tag.E6.cartan i j = 0 := by
    have := cartan6_vals i j
    rcases mul_eq_zero.1 this with h1 | h1
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · left; linarith
      · right; left; linarith
    · right; right; exact h1
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rcases h with h | h | h <;> rw [h]
  · simp [h2]
  · simp [CharTwo.neg_eq]
  · simp

theorem cartan6_mod_two_inj {F : Type} [Field F] [CharP F 2] : ∀ x : Fin Tag.E6.rank → F,
    (∀ i, ∑ j, ((Tag.E6.cartan j i).natAbs : F) * x j = 0) → x = 0 := by
  intro x hx
  funext l
  have h1 : ∀ c, ∑ j, ((Tag.E6.cartan c j : ℤ) : F) * x j = 0 := by
    intro c
    rw [← hx c]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [natAbs_cartan6_cast, cartan6_symm]
  have h3 : (3 : F) * x l = 0 := by
    have key : ∑ c, ((e6Omega3 c l : ℤ) : F) * ∑ j, ((Tag.E6.cartan c j : ℤ) : F) * x j = 0 :=
      Finset.sum_eq_zero fun c _ => by rw [h1 c, mul_zero]
    have e : ∑ c, ((e6Omega3 c l : ℤ) : F) * ∑ j, ((Tag.E6.cartan c j : ℤ) : F) * x j =
        ∑ j, (∑ c, ((e6Omega3 c l : ℤ) : F) * ((Tag.E6.cartan c j : ℤ) : F)) * x j := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring
    rw [e] at key
    have hΩ : ∀ j : Fin Tag.E6.rank,
        ∑ c, ((e6Omega3 c l : ℤ) : F) * ((Tag.E6.cartan c j : ℤ) : F) =
          if l = j then 3 else 0 := by
      intro j
      have := congrArg (fun z : ℤ => (z : F)) (e6Omega3_mul_cartan l j)
      simp only [Int.cast_sum, Int.cast_mul] at this
      rw [this]
      split_ifs <;> simp
    simp only [hΩ, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at key
    exact key
  have h4 : (3 : F) = 1 := by
    have : (3 : F) = 1 + 2 := by norm_num
    rw [this, CharTwo.two_eq_zero, add_zero]
  rw [h4, one_mul] at h3
  exact h3

section Rep

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem fixed_E6 {v : RootModule TwistTag.E6.tag K} (hv : ∀ i, Dop TwistTag.E6.tag K i v = 0) :
    v = coordR v e6Theta • rootVec TwistTag.E6.tag K e6Theta := by
  have h := eq_decomp_of_Dop adjHyp_E6 adjTop_E6.root hv
  have hx : (fun j => v (Sum.inl j)) = 0 :=
    cartan6_mod_two_inj _ (cartan_cond_of_Dop adjHyp_E6 hv)
  have h0 : ∑ j, v (Sum.inl j) • hVec TwistTag.E6.tag K j = 0 :=
    Finset.sum_eq_zero fun j _ => by rw [congrFun hx j]; simp
  rw [h0, add_zero] at h
  exact h

theorem rootVec_theta_ne_zero : rootVec TwistTag.E6.tag K e6Theta ≠ 0 := by
  rw [rootVec_eq_single adjTop_E6.root]
  intro h
  have := congrArg (fun v : RootModule TwistTag.E6.tag K => v (Sum.inr ⟨e6Theta, adjTop_E6.root⟩)) h
  rw [Finsupp.single_eq_same, Finsupp.zero_apply] at this
  exact one_ne_zero this

instance nontrivialRootModuleE6 : Nontrivial (RootModule TwistTag.E6.tag K) :=
  ⟨⟨rootVec TwistTag.E6.tag K e6Theta, 0, rootVec_theta_ne_zero⟩⟩

theorem finrank_adj78 : Module.finrank K (RootModule TwistTag.E6.tag K) = 78 := by
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_fin,
    Nat.card_eq_fintype_card (α := {v : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag v}), card_isRoot]
  rfl

end Rep

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
