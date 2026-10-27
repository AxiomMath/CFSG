module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PartnerLayer

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
  CFSG.ClassicalGroups.Unitary
open scoped MatrixGroups
open Matrix

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

omit [Finite K] [CharP K p] in
theorem entry_zero_aux (h2 : (2 : K) ≠ 0) {x s t : K} (h : x * s = t * x)
    (hst : s = 1 ∧ t = -1 ∨ s = -1 ∧ t = 1) : x = 0 := by
  rcases hst with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have : (2 : K) * x = 0 := by linear_combination h
    exact (mul_eq_zero.mp this).resolve_left h2
  · have : (2 : K) * x = 0 := by linear_combination -h
    exact (mul_eq_zero.mp this).resolve_left h2

theorem suMat_entry_zero_of_commutes (h2 : (2 : K) ≠ 0) {g : Su K p f (5 + 1)}
    (h₂ : g * zEltU K p f (nodePair 5 2 (by norm_num)) =
      zEltU K p f (nodePair 5 2 (by norm_num)) * g)
    (h₃ : g * zEltU K p f (nodePair 5 3 (by norm_num)) =
      zEltU K p f (nodePair 5 3 (by norm_num)) * g)
    (h₄ : g * zEltU K p f (nodePair 5 4 (by norm_num)) =
      zEltU K p f (nodePair 5 4 (by norm_num)) * g) :
    ∀ j k : Fin (5 + 1), j ≠ k → (2 ≤ j.val ∨ 2 ≤ k.val) → suMat g j k = 0 := by
  have e : ∀ a (ha : a < 5),
      g * zEltU K p f (nodePair 5 a ha) = zEltU K p f (nodePair 5 a ha) * g →
      ∀ j k : Fin (5 + 1), suMat g j k * (if k ∈ (nodePair 5 a ha).1 then (-1 : K) else 1) =
        (if j ∈ (nodePair 5 a ha).1 then (-1 : K) else 1) * suMat g j k := by
    intro a ha h j k
    have := congrFun (congrFun (congrArg suMat h) j) k
    rw [suMat_mul, suMat_mul, suMat_zEltU] at this
    simpa [zMat, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  intro j k hjk hjk2
  have e2 := e 2 (by norm_num) h₂ j k
  have e3 := e 3 (by norm_num) h₃ j k
  have e4 := e 4 (by norm_num) h₄ j k
  fin_cases j <;> fin_cases k
  all_goals first
    | exact absurd rfl hjk
    | (exfalso; revert hjk2; simp; done)
    | (refine entry_zero_aux h2 e2 ?_; simp [nodePair, natPair]; done)
    | (refine entry_zero_aux h2 e3 ?_; simp [nodePair, natPair]; done)
    | (refine entry_zero_aux h2 e4 ?_; simp [nodePair, natPair])

theorem suMat_diag_eq_one_of_perfect {ρ : Subgroup (Su K p f (5 + 1))} (hρ : ρ ≤ ⁅ρ, ρ⁆)
    (l : Fin (5 + 1)) (hz : ∀ g ∈ ρ, ∀ k : Fin (5 + 1), k ≠ l → suMat g l k = 0) :
    ∀ g ∈ ρ, suMat g l l = 1 := by
  have hperf : Group.IsPerfect ↥ρ := Subgroup.isPerfect_iff.mpr (le_antisymm
    (Subgroup.commutator_le.mpr fun a ha b hb => by
      rw [commutatorElement_def]
      exact ρ.mul_mem (ρ.mul_mem (ρ.mul_mem ha hb) (ρ.inv_mem ha)) (ρ.inv_mem hb)) hρ)
  let χ : ρ →* K :=
    { toFun := fun g => suMat g.1 l l
      map_one' := by simp [suMat_one]
      map_mul' := fun g h => by
        show suMat (g.1 * h.1) l l = suMat g.1 l l * suMat h.1 l l
        rw [suMat_mul, Matrix.mul_apply, Finset.sum_eq_single l]
        · intro k _ hk
          rw [hz g.1 g.2 k hk, zero_mul]
        · intro h
          exact absurd (Finset.mem_univ l) h }
  intro g hg
  have h1 := Abelianization.commutator_subset_ker (χ.toHomUnits)
    (Group.IsPerfect.mem_commutator (G := ↥ρ) (g := ⟨g, hg⟩))
  have h2 : χ.toHomUnits ⟨g, hg⟩ = 1 := h1
  have h3 := congrArg Units.val h2
  exact h3

theorem le_range_blockEmb_of_le_centralizer_zElt (h2 : (2 : K) ≠ 0)
    {ρ : Subgroup (Su K p f (5 + 1))} (hρ : ρ ≤ ⁅ρ, ρ⁆)
    (h₂ : ρ ≤ Subgroup.centralizer ({zEltU K p f (nodePair 5 2 (by norm_num))} : Set _))
    (h₃ : ρ ≤ Subgroup.centralizer ({zEltU K p f (nodePair 5 3 (by norm_num))} : Set _))
    (h₄ : ρ ≤ Subgroup.centralizer ({zEltU K p f (nodePair 5 4 (by norm_num))} : Set _)) :
    ρ ≤ (blockEmb K p f (5 + 1) 2 0 (by norm_num)).range := by
  have hz : ∀ g ∈ ρ, ∀ j k : Fin (5 + 1), j ≠ k → (2 ≤ j.val ∨ 2 ≤ k.val) → suMat g j k = 0 :=
    fun g hg => suMat_entry_zero_of_commutes h2 (Subgroup.mem_centralizer_singleton_iff.mp (h₂ hg))
      (Subgroup.mem_centralizer_singleton_iff.mp (h₃ hg))
      (Subgroup.mem_centralizer_singleton_iff.mp (h₄ hg))
  intro g hg
  rw [mem_range_blockEmb_iff]
  intro l hl
  have hl2 : 2 ≤ l.val := by omega
  have hdiag := suMat_diag_eq_one_of_perfect hρ l
    (fun g hg k hk => hz g hg l k (Ne.symm hk) (Or.inl hl2)) g hg
  funext a
  rw [smul_def, Matrix.mulVec_single_one]
  by_cases hal : a = l
  · subst hal
    rw [Pi.single_eq_same]
    exact hdiag
  · rw [Pi.single_eq_of_ne hal]
    exact hz g hg a l hal (Or.inr hl2)

theorem range_blockEmb_zero_eq_LcU (h2 : (2 : K) ≠ 0) :
    (blockEmb K p f (5 + 1) 2 0 (by norm_num)).range =
      LcU K p f (nodePair 5 0 (by norm_num)) := by
  rw [range_blockEmb_eq_longRootGroupSU h2 (by norm_num : 0 + 2 ≤ 5 + 1),
    negBlock_eq_zMat (by norm_num : 0 + 2 ≤ 5 + 1)]
  rfl

theorem eq_LcU_of_le_centralizer_zElt (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2)
    {ρ : Subgroup (Su K p f (5 + 1))} {i : Su K p f (5 + 1)}
    (hρi : IsLongRootSU2 K p f (by norm_num : 2 ≤ 5 + 1) ρ i) (hperf : ρ ≤ ⁅ρ, ρ⁆)
    (h₂ : ρ ≤ Subgroup.centralizer ({zEltU K p f (nodePair 5 2 (by norm_num))} : Set _))
    (h₃ : ρ ≤ Subgroup.centralizer ({zEltU K p f (nodePair 5 3 (by norm_num))} : Set _))
    (h₄ : ρ ≤ Subgroup.centralizer ({zEltU K p f (nodePair 5 4 (by norm_num))} : Set _)) :
    ρ = LcU K p f (nodePair 5 0 (by norm_num)) := by
  have h2 : (2 : K) ≠ 0 := two_ne_zero_of_charP_ne_two hp
  have hle := le_range_blockEmb_of_le_centralizer_zElt h2 hperf h₂ h₃ h₄
  rw [range_blockEmb_zero_eq_LcU h2] at hle
  have hL0 := isLongRootSU2_LcU (p := p) (f := f) h2 (by norm_num : 2 ≤ 5 + 1)
    (nodePair 5 0 (by norm_num))
  have hi : i = zEltU K p f (nodePair 5 0 (by norm_num)) :=
    hL0.eq_of_orderOf_eq_two hK hp (hle hρi.mem) (hρi.isClassicalSL2 hK hp).orderOf_eq_two
  rw [hρi.eq_longRootGroupSU h2, hi, ← hL0.eq_longRootGroupSU h2]

end Model

section Link

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {z : G}

omit [Finite G] in
theorem UNodes.mem_centralizingMembers_mul {m : ℕ} (c : UCtx p f m Ω K z) (nd : UNodes c)
    {a : ℕ} (ha : a < m) (h : a = 0 ∨ 2 ≤ a) :
    nd.j a ∈ centralizingMembers Ω {z * nd.w 0} := by
  have h0 : 0 < m := by omega
  refine ⟨(nd.mem a ha).1, ?_⟩
  refine (le_centralizer_pair_mul_iff (nd.mem a ha).2).mpr ?_
  rcases h with rfl | h2
  · exact le_centralizer_of_isClassicalMember (nd.isCl 0 h0)
  · exact le_centralizer_of_commutes (commutes_symm (nd.far 0 h0 a ha (by omega)))
      (nd.isCl 0 h0).mem

omit [Finite G] in
theorem UNodes.K_mem_centralizingMembers_mul {m : ℕ} (c : UCtx p f m Ω K z) (nd : UNodes c)
    (hm : 0 < m) : K ∈ centralizingMembers Ω {z * nd.w 0} :=
  ⟨c.hK, (le_centralizer_pair_mul_iff (le_centralizer_of_isClassicalMember c.hz)).mpr
    (le_centralizer_of_commutes (nd.commK 0 hm) (nd.isCl 0 hm).mem)⟩

theorem linked_of_visible (c : UCtx p f 5 Ω K z) (nd : UNodes c) {β : Subgroup G}
    (hβ : β ∈ centralizingMembers Ω {z * nd.w 0}) (hnK : ¬ Commutes K β)
    (hn0 : ¬ Commutes β (nd.j 0)) (hn3 : ¬ Commutes β (nd.j 3)) :
    ∀ R ∈ centralizingMembers Ω {z * nd.w 0, z}, Linked Ω (z * nd.w 0) K R := by
  intro R hR
  have hKx := UNodes.K_mem_centralizingMembers_mul c nd (by norm_num : 0 < 5)
  have hj : ∀ a (ha : a < 5), (a = 0 ∨ 2 ≤ a) → nd.j a ∈ centralizingMembers Ω {z * nd.w 0} :=
    fun a ha h => UNodes.mem_centralizingMembers_mul c nd ha h
  have hK0 : Linked Ω (z * nd.w 0) K (nd.j 0) :=
    (Linked.single ⟨hKx, hβ, hnK⟩).trans (Linked.single ⟨hβ, hj 0 (by norm_num) (Or.inl rfl), hn0⟩)
  have hK3 : Linked Ω (z * nd.w 0) K (nd.j 3) :=
    (Linked.single ⟨hKx, hβ, hnK⟩).trans
      (Linked.single ⟨hβ, hj 3 (by norm_num) (Or.inr (by norm_num)), hn3⟩)
  have hK2 : Linked Ω (z * nd.w 0) K (nd.j 2) :=
    hK3.trans (Linked.single (NCEdge.symm ⟨hj 2 (by norm_num) (Or.inr le_rfl),
      hj 3 (by norm_num) (Or.inr (by norm_num)), nd.adj 2 (by norm_num)⟩))
  have hK4 : Linked Ω (z * nd.w 0) K (nd.j 4) :=
    hK3.trans (Linked.single ⟨hj 3 (by norm_num) (Or.inr (by norm_num)),
      hj 4 (by norm_num) (Or.inr (by norm_num)), nd.adj 3 (by norm_num)⟩)
  have hRx := (mem_centralizingMembers_pair.mp hR).1
  obtain ⟨hRz, hRw⟩ := mem_centralizingMembers_pair.mp (centralizingMembers_mul_iff.mp hR)
  have hstep : ∀ a (ha : a < 5), 2 ≤ a → Linked Ω (z * nd.w 0) K (nd.j a) →
      ¬ Commutes R (nd.j a) → Linked Ω (z * nd.w 0) K R := fun a ha h2a hKa hnc =>
    hKa.trans (Linked.single ⟨hj a ha (Or.inr h2a), hRx, fun hc => hnc (commutes_symm hc)⟩)
  by_cases hRK : R = K
  · subst hRK
    exact Relation.ReflTransGen.refl
  obtain ⟨ρ, hρT, hRρ⟩ := typeU_exists_root_of_ne c.hp2 c.hq c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.d
    hRz hRK
  obtain ⟨i, hi⟩ := hρT
  have hperf : ρ ≤ ⁅ρ, ρ⁆ := (Subgroup.isPerfect_iff.mp (c.isPerfect_of_isLongRootSU2 hi)).ge
  have hρle : ∀ a (ha : a < 5), Commutes R (nd.j a) →
      ρ ≤ Subgroup.centralizer ({zEltU (GaloisField p (2 * f)) p f (nodePair 5 a ha)} : Set _) :=
    fun a ha hc => (UNodes.le_centralizer_iff_root_node c nd ha hRz hperf hRρ).mp
      (le_centralizer_of_commutes hc (nd.isCl a ha).mem)
  by_cases h2 : Commutes R (nd.j 2)
  · by_cases h3 : Commutes R (nd.j 3)
    · by_cases h4 : Commutes R (nd.j 4)
      · have hρ0 := eq_LcU_of_le_centralizer_zElt c.card_eq c.hp2 hi hperf
          (hρle 2 (by norm_num) h2) (hρle 3 (by norm_num) h3) (hρle 4 (by norm_num) h4)
        have hR0 : R = nd.j 0 := locImg_injOn c.hΩ c.hP1 hRz (nd.mem 0 (by norm_num))
          (by rw [hRρ, hρ0, nd.img 0 (by norm_num)])
        rw [hR0]
        exact hK0
      · exact hstep 4 (by norm_num) (by norm_num) hK4 h4
    · exact hstep 3 (by norm_num) (by norm_num) hK3 h3
  · exact hstep 2 (by norm_num) le_rfl hK2 h2

end Link

end CFSG.ClassicalInvolution.RouteD.NonClassical
