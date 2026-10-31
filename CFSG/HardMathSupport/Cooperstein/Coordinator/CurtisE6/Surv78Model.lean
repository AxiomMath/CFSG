module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Surv78Type
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.ChevTypeLD

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw

@[expose] def e6Theta0 : Fin Tag.E6.rank → ℤ := ![1, 2, 2, 3, 2, 1]

abbrev e6node20 : Fin Tag.E6.rank := ⟨1, by decide⟩

@[expose] def e6ThetaWords : List (List (Fin Tag.E6.rank)) :=
  ([[2, 3, 4, 5, 1, 3, 4, 2, 3, 1], [3, 4, 5, 2, 3, 4, 0, 2, 3, 1], [3, 4, 5, 1, 3, 4, 0, 2, 3, 1],
    [4, 5, 2, 1, 3, 4, 0, 2, 3, 1], [5, 3, 2, 1, 3, 4, 0, 2, 3, 1], [4, 3, 2, 1, 3, 4, 0, 2, 3, 1]] :
    List (List (Fin 6)))

theorem e6_words_check : ∀ j : Fin Tag.E6.rank,
    (e6ThetaWords.getD j []).foldr (reflect .E6) e6Theta0 = Pi.single j 1 := by
  decide +kernel

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

abbrev e6node2 : Fin TwistTag.E6.tag.rank := e6node20

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

variable (K) in
@[expose] def adj78 : Representation K ↥(adjointGroup TwistTag.E6.tag K) (RootModule TwistTag.E6.tag K) :=
  adjRep TwistTag.E6.tag K

@[expose] def adjDatum78 : CurtisDatum ↥(adjointGroup TwistTag.E6.tag K) (coxeterSystem TwistTag.E6.tag)
    2 :=
  chevDatumLD TwistTag.E6 K 2 e6LongestData

theorem xC_mem_U78 (i : Fin TwistTag.E6.tag.rank) : xC TwistTag.E6.tag K i 1 ∈ (adjDatum78 (K := K)).U :=
  (adjDatum78 (K := K)).X_le i (xC_mem_X_LD i 1)

theorem fixU_le_line78 {v : RootModule TwistTag.E6.tag K} (hv : v ∈ (adjDatum78 (K := K)).fixU (adj78 K)) :
    ∃ c : K, v = c • rootVec TwistTag.E6.tag K e6Theta := by
  refine ⟨coordR v e6Theta, fixed_E6 fun i => ?_⟩
  have h := ((adjDatum78 (K := K)).mem_fixU _).1 hv _ (xC_mem_U78 i)
  rw [adj78, adjRep_xC] at h
  rw [Dop_apply, h, sub_self]

theorem rootVec_theta_ne_zero : rootVec TwistTag.E6.tag K e6Theta ≠ 0 := by
  rw [rootVec_eq_single adjTop_E6.root]
  intro h
  have := congrArg (fun v : RootModule TwistTag.E6.tag K => v (Sum.inr ⟨e6Theta, adjTop_E6.root⟩)) h
  rw [Finsupp.single_eq_same, Finsupp.zero_apply] at this
  exact one_ne_zero this

instance nontrivialRootModuleE6 : Nontrivial (RootModule TwistTag.E6.tag K) :=
  ⟨⟨rootVec TwistTag.E6.tag K e6Theta, 0, rootVec_theta_ne_zero⟩⟩

theorem rootVec_theta_mem_fixU :
    rootVec TwistTag.E6.tag K e6Theta ∈ (adjDatum78 (K := K)).fixU (adj78 K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1
    ((adjDatum78 (K := K)).fixU_ne_bot (p := 2) (adj78 K))
  obtain ⟨c, rfl⟩ := fixU_le_line78 hx
  have hc : c ≠ 0 := by rintro rfl; exact hx0 (zero_smul _ _)
  have := Submodule.smul_mem _ c⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

variable (K) in
@[expose] def adjChi78 (g : ↥(adjointGroup TwistTag.E6.tag K)) : K :=
  coordR (adj78 K g (rootVec TwistTag.E6.tag K e6Theta)) e6Theta

theorem adjChi78_dC (s : Fin TwistTag.E6.tag.rank) (t : Kˣ) :
    adjChi78 K (dC TwistTag.E6.tag K s t) = ((t ^ (if s = e6node2 then (1 : ℤ) else 0) : Kˣ) : K) := by
  unfold adjChi78
  rw [adj78, adjRep_dC_theta adjTop_E6 s t, coordR_smul, coordR_rootVec adjTop_E6.root, if_pos rfl,
    mul_one]

theorem adj78_H (h : ↥(adjointGroup TwistTag.E6.tag K)) (hh : h ∈ (adjDatum78 (K := K)).H) :
    adj78 K h (rootVec TwistTag.E6.tag K e6Theta) = adjChi78 K h • rootVec TwistTag.E6.tag K e6Theta := by
  obtain ⟨c, hc⟩ := fixU_le_line78 ((adjDatum78 (K := K)).act_H_mem_fixU (adj78 K) hh
    rootVec_theta_mem_fixU)
  have : adjChi78 K h = c := by
    unfold adjChi78
    rw [hc, coordR_smul, coordR_rootVec adjTop_E6.root, if_pos rfl, mul_one]
  rw [this, hc]

theorem adj78_heckeT_theta (s : Fin TwistTag.E6.tag.rank) [Fintype K] :
    (adjDatum78 (K := K)).heckeT (adj78 K) s (rootVec TwistTag.E6.tag K e6Theta) =
      ∑ c : K, adjRep TwistTag.E6.tag K (xC TwistTag.E6.tag K s c * nC TwistTag.E6.tag K s) (rootVec TwistTag.E6.tag K e6Theta) := by
  unfold adjDatum78
  rw [heckeT_chevDatumLD]
  rfl

theorem adj78_isChevTypeLD :
    IsChevTypeLD TwistTag.E6 K 2 e6LongestData (adj78 K) (rootVec TwistTag.E6.tag K e6Theta) (adjChi78 K)
      (Finset.univ.erase e6node2) := by
  have := Fintype.ofFinite K
  refine ⟨rootVec_theta_mem_fixU, rootVec_theta_ne_zero, adj78_H, fun s => ?_⟩
  by_cases hs : s = e6node2
  · subst hs
    refine ⟨fun h => absurd rfl (Finset.mem_erase.1 h).1, fun h => ?_⟩
    exfalso
    obtain ⟨h1, h2⟩ := h
    have h1' : ∀ u : Kˣ, (u : K) = 1 := fun u => by
      have := h1 u
      rwa [adjChi78_dC, if_pos rfl, zpow_one] at this
    have h3 := (adj78_heckeT_theta (K := K) e6node2).trans (adj_heckeSum_node adjTop_E6)
    have h4 : (∑ c : K, c) • rootVec TwistTag.E6.tag K e6Theta = 0 := h3.symm.trans h2
    rw [sum_eq_one_of_units_eq_one h1', one_smul] at h4
    exact rootVec_theta_ne_zero h4
  · refine ⟨fun _ => ⟨fun u => ?_, ?_⟩, fun _ => Finset.mem_erase.2 ⟨hs, Finset.mem_univ _⟩⟩
    · rw [adjChi78_dC, if_neg hs, zpow_zero]
      rfl
    · exact (adj78_heckeT_theta s).trans (adj_heckeSum_of_ne adjTop_E6 hs)

theorem finrank_adj78 : Module.finrank K (RootModule TwistTag.E6.tag K) = 78 := by
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_fin,
    Nat.card_eq_fintype_card (α := {v : Fin TwistTag.E6.tag.rank → ℤ // IsRoot TwistTag.E6.tag v}), card_isRoot]
  rfl

end Rep

end CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.Min
