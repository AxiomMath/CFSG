module

public import CFSG.LieType.Chevalley.EvenTrialityOrbitParametrization
public import CFSG.LieType.Chevalley.EvenRootCommutatorD4

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem commutator_list_prod_of_central {G : Type*} [Group G] {Z : Subgroup G}
    (hZ : ∀ x ∈ Z, ∀ y ∈ Z, Commute x y) (zs ws : List G)
    (hzZ : ∀ z ∈ zs, ∀ c ∈ Z, Commute z c) (hwZ : ∀ w ∈ ws, ∀ c ∈ Z, Commute w c)
    (hzw : ∀ z ∈ zs, ∀ w ∈ ws, ⁅z, w⁆ ∈ Z) :
    ⁅zs.prod, ws.prod⁆ ∈ Z ∧
      ⁅zs.prod, ws.prod⁆ = (zs.map fun z => (ws.map fun w => ⁅z, w⁆).prod).prod := by
  have inner : ∀ z ∈ zs, ⁅z, ws.prod⁆ ∈ Z ∧ ⁅z, ws.prod⁆ = (ws.map fun w => ⁅z, w⁆).prod := by
    intro z hz
    induction ws with
    | nil => simp
    | cons w ws ih =>
      obtain ⟨hm, he⟩ := ih (fun w' h c hc => hwZ w' (List.mem_cons_of_mem _ h) c hc)
        (fun z' hz' w' h => hzw z' hz' w' (List.mem_cons_of_mem _ h))
      have hzw0 := hzw z hz w List.mem_cons_self
      have e : ⁅z, w * ws.prod⁆ = ⁅z, w⁆ * (w * ⁅z, ws.prod⁆ * w⁻¹) := by
        simp only [commutatorElement_def]
        group
      have hc : w * ⁅z, ws.prod⁆ * w⁻¹ = ⁅z, ws.prod⁆ := by
        rw [(hwZ w List.mem_cons_self _ hm).eq, mul_inv_cancel_right]
      rw [List.prod_cons, e, hc, List.map_cons, List.prod_cons, ← he]
      exact ⟨mul_mem hzw0 hm, rfl⟩
  induction zs with
  | nil => simp
  | cons z zs ih =>
    obtain ⟨hm, he⟩ := ih (fun z' h c hc => hzZ z' (List.mem_cons_of_mem _ h) c hc)
      (fun z' h w hw => hzw z' (List.mem_cons_of_mem _ h) w hw)
      (fun z' h => inner z' (List.mem_cons_of_mem _ h))
    obtain ⟨hm1, he1⟩ := inner z List.mem_cons_self
    have e : ⁅z * zs.prod, ws.prod⁆ = (z * ⁅zs.prod, ws.prod⁆ * z⁻¹) * ⁅z, ws.prod⁆ := by
      simp only [commutatorElement_def]
      group
    have hc : z * ⁅zs.prod, ws.prod⁆ * z⁻¹ = ⁅zs.prod, ws.prod⁆ := by
      rw [(hzZ z List.mem_cons_self _ hm).eq, mul_inv_cancel_right]
    rw [List.prod_cons, e, hc, (hZ _ hm _ hm1).eq, List.map_cons, List.prod_cons, ← he1, ← he]
    exact ⟨mul_mem hm1 hm, rfl⟩

@[expose] def d4IsRootB (v : Fin TwistTag.D4.tag.rank → ℤ) : Bool :=
  (List.range TwistTag.D4.tag.rootCertificate.roots.length).any fun k =>
    decide (TwistTag.D4.tag.rootCertificate.root k = v)

theorem d4IsRootB_iff {v : Fin TwistTag.D4.tag.rank → ℤ} :
    d4IsRootB v = true ↔ IsRoot TwistTag.D4.tag v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check _)]
  simp only [d4IsRootB, List.any_eq_true, List.mem_range, decide_eq_true_eq]

@[expose] def d4CommB (α β : Fin TwistTag.D4.tag.rank → ℤ) : Bool :=
  d4IsRootB α && d4IsRootB β && decide (α ≠ β) && decide (α ≠ -β) && !d4IsRootB (α + β)

@[expose] def d4SumB (α β γ : Fin TwistTag.D4.tag.rank → ℤ) : Bool :=
  d4IsRootB α && d4IsRootB β && decide (α ≠ β) && decide (α ≠ -β) && decide (α + β = γ) &&
    d4IsRootB γ

section Pairs

variable {K : Type} [Field K] [CharP K 2]

theorem commute_of_d4CommB
    {α β : Fin TwistTag.D4.tag.rank → ℤ} (h : d4CommB α β = true)
    (s t : K) : Commute (pinnedX TwistTag.D4.tag K α s) (pinnedX TwistTag.D4.tag K β t) := by
  simp only [d4CommB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨hα, hβ⟩, hne⟩, hne'⟩, hn⟩ := h
  have hn' : ¬IsRoot TwistTag.D4.tag (α + β) := fun hr => by
    rw [← d4IsRootB_iff, hn] at hr
    exact Bool.false_ne_true hr
  exact commutatorElement_eq_one_iff_mul_comm.1 ((d4_even_root_pair_relations (R := K)
    (d4IsRootB_iff.1 hα) (d4IsRootB_iff.1 hβ) hne hne' s t).2 hn')

theorem commutator_of_d4SumB
    {α β γ : Fin TwistTag.D4.tag.rank → ℤ} (h : d4SumB α β γ = true)
    (s t : K) : ⁅pinnedX TwistTag.D4.tag K α s, pinnedX TwistTag.D4.tag K β t⁆ =
      pinnedX TwistTag.D4.tag K γ (s * t) := by
  simp only [d4SumB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hα, hβ⟩, hne⟩, hne'⟩, hsum⟩, hγ⟩ := h
  subst hsum
  exact (d4_even_root_pair_relations (R := K) (d4IsRootB_iff.1 hα) (d4IsRootB_iff.1 hβ) hne
    hne' s t).1 (d4IsRootB_iff.1 hγ)

omit [CharP K 2] in
theorem commute_of_mem_rootSpan
    {τ : Tag} {S T : Set (Fin τ.rank → ℤ)}
    (h : ∀ α ∈ S, ∀ β ∈ T, ∀ s t : K, Commute (pinnedX τ K α s) (pinnedX τ K β t))
    {g g' : ModGL τ K} (hg : g ∈ rootSpan τ K S) (hg' : g' ∈ rootSpan τ K T) : Commute g g' := by
  rw [rootSpan_eq_closure] at hg hg'
  have h1 : ∀ x ∈ {g | ∃ α ∈ S, ∃ c : K, pinnedX τ K α c = g}, ∀ y ∈ Subgroup.closure
      {g | ∃ β ∈ T, ∃ c : K, pinnedX τ K β c = g}, Commute x y := by
    intro x hx y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨α, hα, s, rfl⟩ := hx
      obtain ⟨β, hβ, t, rfl⟩ := hy
      exact h α hα β hβ s t
    | one => exact Commute.one_right x
    | mul y z _ _ hy hz => exact hy.mul_right hz
    | inv y _ hy => exact hy.inv_right
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx g' hg'
  | one => exact Commute.one_left g'
  | mul x y _ _ hx hy => exact hx.mul_left hy
  | inv x _ hx => exact hx.inv_left

end Pairs

section OrbitProducts

variable {K : Type} [Field K] [CharP K 2]

omit [CharP K 2] in
theorem commute_pinnedX_self
    {τ : Tag} (α : Fin τ.rank → ℤ) (a b : K) :
    Commute (pinnedX τ K α a) (pinnedX τ K α b) := by
  rw [Commute, SemiconjBy, ← pinnedX_add, ← pinnedX_add, add_comm]

omit [CharP K 2] in
theorem commute_rootSubgroup
    {τ : Tag} (α : Fin τ.rank → ℤ) :
    ∀ x ∈ rootSubgroup τ K α, ∀ y ∈ rootSubgroup τ K α, Commute x y := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := mem_rootSubgroup.1 hx
  obtain ⟨b, rfl⟩ := mem_rootSubgroup.1 hy
  exact commute_pinnedX_self α a b

theorem commutator_trialityOrbitProd
    {α β γ : Fin TwistTag.D4.tag.rank → ℤ} (σ : K →+* K)
    (hs : d4SumB α β γ = true ∧
      d4SumB (permLattice TwistTag.D4.perm α) (permLattice TwistTag.D4.perm β) γ = true ∧
      d4SumB (permLattice (TwistTag.D4.perm ^ 2) α) (permLattice (TwistTag.D4.perm ^ 2) β) γ = true)
    (hc : d4CommB α (permLattice TwistTag.D4.perm β) = true ∧
      d4CommB α (permLattice (TwistTag.D4.perm ^ 2) β) = true ∧
      d4CommB (permLattice TwistTag.D4.perm α) β = true ∧
      d4CommB (permLattice TwistTag.D4.perm α) (permLattice (TwistTag.D4.perm ^ 2) β) = true ∧
      d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) β = true ∧
      d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) (permLattice TwistTag.D4.perm β) = true)
    (hz : d4CommB α γ = true ∧ d4CommB (permLattice TwistTag.D4.perm α) γ = true ∧
      d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) γ = true ∧ d4CommB β γ = true ∧
      d4CommB (permLattice TwistTag.D4.perm β) γ = true ∧
      d4CommB (permLattice (TwistTag.D4.perm ^ 2) β) γ = true)
    (s t : K) :
    ⁅(trialityOrbitProd K σ α s : ModGL TwistTag.D4.tag K),
        (trialityOrbitProd K σ β t : ModGL TwistTag.D4.tag K)⁆ =
      pinnedX TwistTag.D4.tag K γ (s * t + σ s * σ t + σ (σ s) * σ (σ t)) := by
  obtain ⟨hs0, hs1, hs2⟩ := hs
  obtain ⟨hc01, hc02, hc10, hc12, hc20, hc21⟩ := hc
  obtain ⟨hz0, hz1, hz2, hw0, hw1, hw2⟩ := hz
  set zs := [pinnedX TwistTag.D4.tag K α s,
    pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm α) (σ s),
    pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) α) (σ (σ s))]
  set ws := [pinnedX TwistTag.D4.tag K β t,
    pinnedX TwistTag.D4.tag K (permLattice TwistTag.D4.perm β) (σ t),
    pinnedX TwistTag.D4.tag K (permLattice (TwistTag.D4.perm ^ 2) β) (σ (σ t))]
  have ez : (trialityOrbitProd K σ α s : ModGL TwistTag.D4.tag K) = zs.prod := by
    simp only [coe_trialityOrbitProd, zs, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have ew : (trialityOrbitProd K σ β t : ModGL TwistTag.D4.tag K) = ws.prod := by
    simp only [coe_trialityOrbitProd, ws, List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  have hZc : ∀ (δ : Fin TwistTag.D4.tag.rank → ℤ), d4CommB δ γ = true → ∀ a : K,
      ∀ c ∈ rootSubgroup TwistTag.D4.tag K γ, Commute (pinnedX TwistTag.D4.tag K δ a) c := by
    intro δ hδ a c hcm
    obtain ⟨d, rfl⟩ := mem_rootSubgroup.1 hcm
    exact commute_of_d4CommB hδ a d
  have h1 : ∀ {x y : ModGL TwistTag.D4.tag K}, Commute x y → ⁅x, y⁆ = 1 := fun h =>
    commutatorElement_eq_one_iff_mul_comm.2 h
  have key := commutator_list_prod_of_central (commute_rootSubgroup γ) zs ws
    (by
      intro z hz c hcm
      simp only [zs, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl | rfl | rfl
      · exact hZc _ hz0 _ c hcm
      · exact hZc _ hz1 _ c hcm
      · exact hZc _ hz2 _ c hcm)
    (by
      intro w hw c hcm
      simp only [ws, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · exact hZc _ hw0 _ c hcm
      · exact hZc _ hw1 _ c hcm
      · exact hZc _ hw2 _ c hcm)
    (by
      intro z hz w hw
      simp only [zs, ws, List.mem_cons, List.not_mem_nil, or_false] at hz hw
      rcases hz with rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl
      · rw [commutator_of_d4SumB hs0]
        exact mem_rootSubgroup.2 ⟨_, rfl⟩
      · rw [h1 (commute_of_d4CommB hc01 _ _)]
        exact Subgroup.one_mem _
      · rw [h1 (commute_of_d4CommB hc02 _ _)]
        exact Subgroup.one_mem _
      · rw [h1 (commute_of_d4CommB hc10 _ _)]
        exact Subgroup.one_mem _
      · rw [commutator_of_d4SumB hs1]
        exact mem_rootSubgroup.2 ⟨_, rfl⟩
      · rw [h1 (commute_of_d4CommB hc12 _ _)]
        exact Subgroup.one_mem _
      · rw [h1 (commute_of_d4CommB hc20 _ _)]
        exact Subgroup.one_mem _
      · rw [h1 (commute_of_d4CommB hc21 _ _)]
        exact Subgroup.one_mem _
      · rw [commutator_of_d4SumB hs2]
        exact mem_rootSubgroup.2 ⟨_, rfl⟩)
  rw [ez, ew, key.2]
  simp only [zs, ws, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    commutator_of_d4SumB hs0, commutator_of_d4SumB hs1, commutator_of_d4SumB hs2,
    h1 (commute_of_d4CommB hc01 _ _), h1 (commute_of_d4CommB hc02 _ _),
    h1 (commute_of_d4CommB hc10 _ _), h1 (commute_of_d4CommB hc12 _ _),
    h1 (commute_of_d4CommB hc20 _ _), h1 (commute_of_d4CommB hc21 _ _), one_mul]
  rw [← pinnedX_add, ← pinnedX_add, add_assoc]

end OrbitProducts

@[expose] def trialityPairCheck (α β γ : Fin TwistTag.D4.tag.rank → ℤ) : Bool :=
  d4SumB α β γ &&
    d4SumB (permLattice TwistTag.D4.perm α) (permLattice TwistTag.D4.perm β) γ &&
    d4SumB (permLattice (TwistTag.D4.perm ^ 2) α) (permLattice (TwistTag.D4.perm ^ 2) β) γ &&
    d4CommB α (permLattice TwistTag.D4.perm β) &&
    d4CommB α (permLattice (TwistTag.D4.perm ^ 2) β) &&
    d4CommB (permLattice TwistTag.D4.perm α) β &&
    d4CommB (permLattice TwistTag.D4.perm α) (permLattice (TwistTag.D4.perm ^ 2) β) &&
    d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) β &&
    d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) (permLattice TwistTag.D4.perm β) &&
    d4CommB α γ && d4CommB (permLattice TwistTag.D4.perm α) γ &&
    d4CommB (permLattice (TwistTag.D4.perm ^ 2) α) γ && d4CommB β γ &&
    d4CommB (permLattice TwistTag.D4.perm β) γ &&
    d4CommB (permLattice (TwistTag.D4.perm ^ 2) β) γ

theorem trialityPairCheck_14 : trialityPairCheck (trialityRoot 0) (trialityRoot 3)
    (trialityRoot 4) = true := by
  decide +kernel

theorem trialityPairCheck_34 : trialityPairCheck (trialityRoot 2) (trialityRoot 3)
    (trialityRoot 5) = true := by
  decide +kernel

theorem triality_sum_25 : d4SumB (trialityRoot 1) (trialityRoot 4) (trialityRoot 5) = true := by
  decide +kernel

@[expose] def trialityCommPairs : List (Fin 6 × Fin 6) :=
  [(0, 4), (0, 5), (1, 2), (1, 3), (1, 5), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

theorem trialityOrbit_comm : ∀ p ∈ trialityCommPairs, ∀ α ∈ trialityOrbit p.1,
    ∀ β ∈ trialityOrbit p.2, d4CommB α β = true := by
  decide +kernel

section Main

variable {K : Type} [Field K] [CharP K 2]

theorem commutator_trialityOrbitProd_of_check
    {α β γ : Fin TwistTag.D4.tag.rank → ℤ}
    (h : trialityPairCheck α β γ = true) (σ : K →+* K) (s t : K) :
    ⁅(trialityOrbitProd K σ α s : ModGL TwistTag.D4.tag K),
        (trialityOrbitProd K σ β t : ModGL TwistTag.D4.tag K)⁆ =
      pinnedX TwistTag.D4.tag K γ (s * t + σ s * σ t + σ (σ s) * σ (σ t)) := by
  simp only [trialityPairCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hs0, hs1⟩, hs2⟩, hc01⟩, hc02⟩, hc10⟩, hc12⟩, hc20⟩, hc21⟩, hz0⟩, hz1⟩,
    hz2⟩, hw0⟩, hw1⟩, hw2⟩ := h
  exact commutator_trialityOrbitProd σ ⟨hs0, hs1, hs2⟩ ⟨hc01, hc02, hc10, hc12, hc20, hc21⟩
    ⟨hz0, hz1, hz2, hw0, hw1, hw2⟩ s t

omit [CharP K 2] in
theorem coe_commutatorElement_adjoint (x y : adjointGroup TwistTag.D4.tag K) :
    ((⁅x, y⁆ : adjointGroup TwistTag.D4.tag K) : ModGL TwistTag.D4.tag K) =
      ⁅(x : ModGL TwistTag.D4.tag K), (y : ModGL TwistTag.D4.tag K)⁆ :=
  rfl

theorem commute_trialityOrbit
    {p : Fin 6 × Fin 6} (hp : p ∈ trialityCommPairs)
    {g g' : ModGL TwistTag.D4.tag K}
    (hg : g ∈ rootSpan TwistTag.D4.tag K (trialityOrbit p.1 : Set (Fin TwistTag.D4.tag.rank → ℤ)))
    (hg' : g' ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit p.2 : Set (Fin TwistTag.D4.tag.rank → ℤ))) : Commute g g' :=
  commute_of_mem_rootSpan (fun α hα β hβ s t =>
    commute_of_d4CommB (trialityOrbit_comm p hp α hα β hβ) s t) hg hg'

omit [CharP K 2] in
theorem pinnedX_mem_rootSpan_trialityOrbit
    (j : Fin 6) (c : K) :
    pinnedX TwistTag.D4.tag K (trialityRoot j) c ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit j : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
  pinnedX_mem_rootSpan (TwistTag.D4.self_mem_diagramOrbit (trialityRoot j)) c

end Main

section Form

variable (K : Type) [Field K] (σ : K →+* K)

theorem coe_trialityTrace (hσ : σ ^ 3 = 1) (c : K) :
    (trialityTrace K σ hσ c : K) = c + σ c + σ (σ c) :=
  rfl

theorem trialityFixedField_smul (c : trialityFixedField K σ) (s : K) : c • s = (c : K) * s :=
  rfl

@[expose] def trialityTraceForm (hσ : σ ^ 3 = 1) :
    LinearMap.BilinForm (trialityFixedField K σ) K :=
  LinearMap.mk₂ (trialityFixedField K σ) (fun s t => trialityTrace K σ hσ (s * t))
    (fun s₁ s₂ t => Subtype.ext (by
      simp only [coe_trialityTrace, Subfield.coe_add, add_mul, map_add]
      ring))
    (fun c s t => Subtype.ext (by
      simp only [smul_eq_mul, MulMemClass.coe_mul, coe_trialityTrace, trialityFixedField_smul,
        map_mul, mem_trialityFixedField.1 c.2]
      ring))
    (fun s t₁ t₂ => Subtype.ext (by
      simp only [coe_trialityTrace, Subfield.coe_add, mul_add, map_add]
      ring))
    (fun c s t => Subtype.ext (by
      simp only [smul_eq_mul, MulMemClass.coe_mul, coe_trialityTrace, trialityFixedField_smul,
        map_mul, mem_trialityFixedField.1 c.2]
      ring))

theorem trialityTraceForm_apply (hσ : σ ^ 3 = 1) (s t : K) :
    trialityTraceForm K σ hσ s t = trialityTrace K σ hσ (s * t) :=
  rfl

theorem trialityTrace_one [CharP K 2] (hσ : σ ^ 3 = 1) : trialityTrace K σ hσ 1 = 1 := by
  refine Subtype.ext ?_
  rw [coe_trialityTrace, map_one, map_one, Subfield.coe_one]
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  linear_combination h2

theorem trialityTraceForm_nondegenerate [CharP K 2] (hσ : σ ^ 3 = 1) :
    (trialityTraceForm K σ hσ).Nondegenerate := by
  refine ⟨fun s hs => ?_, fun t ht => ?_⟩
  · by_contra h0
    have h := hs s⁻¹
    rw [trialityTraceForm_apply, mul_inv_cancel₀ h0, trialityTrace_one] at h
    exact one_ne_zero h
  · by_contra h0
    have h := ht t⁻¹
    rw [trialityTraceForm_apply, inv_mul_cancel₀ h0, trialityTrace_one] at h
    exact one_ne_zero h

end Form

theorem even_triality_trace_commutators
    (K : Type) [Field K] [CharP K 2] (σ : K →+* K)
    (hσ : σ ^ 3 = 1) :
    (∀ s t : K, ⁅trialityX₁ K σ s, trialityX₄ K σ t⁆ =
      trialityX₅ K σ (trialityTrace K σ hσ (s * t))) ∧
    (∀ s t : K, ⁅trialityX₃ K σ s, trialityX₄ K σ t⁆ =
      trialityX₆ K σ (trialityTrace K σ hσ (s * t))) ∧
    (∀ b e : trialityFixedField K σ, ⁅trialityX₂ K σ b, trialityX₅ K σ e⁆ =
      trialityX₆ K σ (b * e)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₁ K σ a) (trialityX₅ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₁ K σ a) (trialityX₆ K σ b)) ∧
    (∀ (a : trialityFixedField K σ) (b : K), Commute (trialityX₂ K σ a) (trialityX₃ K σ b)) ∧
    (∀ (a : trialityFixedField K σ) (b : K), Commute (trialityX₂ K σ a) (trialityX₄ K σ b)) ∧
    (∀ a b : trialityFixedField K σ, Commute (trialityX₂ K σ a) (trialityX₆ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₃ K σ a) (trialityX₅ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₃ K σ a) (trialityX₆ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₄ K σ a) (trialityX₅ K σ b)) ∧
    (∀ (a : K) (b : trialityFixedField K σ), Commute (trialityX₄ K σ a) (trialityX₆ K σ b)) ∧
    (∀ a b : trialityFixedField K σ, Commute (trialityX₅ K σ a) (trialityX₆ K σ b)) ∧
    (∀ s t : K, trialityTraceForm K σ hσ s t = trialityTrace K σ hσ (s * t)) ∧
    (trialityTraceForm K σ hσ).Nondegenerate := by
  have hT : ∀ s t : K, s * t + σ s * σ t + σ (σ s) * σ (σ t) =
      (trialityTrace K σ hσ (s * t) : K) := fun s t => by
    rw [coe_trialityTrace, map_mul, map_mul]
  have hcomm : ∀ {p : Fin 6 × Fin 6}, p ∈ trialityCommPairs →
      ∀ {x y : adjointGroup TwistTag.D4.tag K},
        (x : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
          (trialityOrbit p.1 : Set (Fin TwistTag.D4.tag.rank → ℤ)) →
        (y : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
          (trialityOrbit p.2 : Set (Fin TwistTag.D4.tag.rank → ℤ)) → Commute x y :=
    fun hp _ _ hx hy => Subtype.ext (commute_trialityOrbit hp hx hy)
  have m1 : ∀ a : K, (trialityX₁ K σ a : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit 0 : Set (Fin TwistTag.D4.tag.rank → ℤ)) := trialityOrbitProd_mem_rootSpan σ
  have m3 : ∀ a : K, (trialityX₃ K σ a : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit 2 : Set (Fin TwistTag.D4.tag.rank → ℤ)) := trialityOrbitProd_mem_rootSpan σ
  have m4 : ∀ a : K, (trialityX₄ K σ a : ModGL TwistTag.D4.tag K) ∈ rootSpan TwistTag.D4.tag K
      (trialityOrbit 3 : Set (Fin TwistTag.D4.tag.rank → ℤ)) := trialityOrbitProd_mem_rootSpan σ
  have m2 : ∀ a : trialityFixedField K σ, (trialityX₂ K σ a : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit 1 : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
    fun a => pinnedX_mem_rootSpan_trialityOrbit 1 _
  have m5 : ∀ a : trialityFixedField K σ, (trialityX₅ K σ a : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit 4 : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
    fun a => pinnedX_mem_rootSpan_trialityOrbit 4 _
  have m6 : ∀ a : trialityFixedField K σ, (trialityX₆ K σ a : ModGL TwistTag.D4.tag K) ∈
      rootSpan TwistTag.D4.tag K (trialityOrbit 5 : Set (Fin TwistTag.D4.tag.rank → ℤ)) :=
    fun a => pinnedX_mem_rootSpan_trialityOrbit 5 _
  refine ⟨fun s t => Subtype.ext ?_, fun s t => Subtype.ext ?_, fun b e => Subtype.ext ?_,
    fun a b => hcomm (p := (0, 4)) (by decide) (m1 a) (m5 b),
    fun a b => hcomm (p := (0, 5)) (by decide) (m1 a) (m6 b),
    fun a b => hcomm (p := (1, 2)) (by decide) (m2 a) (m3 b),
    fun a b => hcomm (p := (1, 3)) (by decide) (m2 a) (m4 b),
    fun a b => hcomm (p := (1, 5)) (by decide) (m2 a) (m6 b),
    fun a b => hcomm (p := (2, 4)) (by decide) (m3 a) (m5 b),
    fun a b => hcomm (p := (2, 5)) (by decide) (m3 a) (m6 b),
    fun a b => hcomm (p := (3, 4)) (by decide) (m4 a) (m5 b),
    fun a b => hcomm (p := (3, 5)) (by decide) (m4 a) (m6 b),
    fun a b => hcomm (p := (4, 5)) (by decide) (m5 a) (m6 b),
    trialityTraceForm_apply K σ hσ, trialityTraceForm_nondegenerate K σ hσ⟩
  · rw [coe_commutatorElement_adjoint]
    exact (commutator_trialityOrbitProd_of_check trialityPairCheck_14 σ s t).trans
      (congrArg _ (hT s t))
  · rw [coe_commutatorElement_adjoint]
    exact (commutator_trialityOrbitProd_of_check trialityPairCheck_34 σ s t).trans
      (congrArg _ (hT s t))
  · rw [coe_commutatorElement_adjoint]
    exact commutator_of_d4SumB triality_sum_25 (b : K) (e : K)

end CFSG.LieType.Chevalley
