module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.D4Rigidity
public import CFSG.HardMathSupport.Lang.E6Descent.OuterFixed27D4AmbientFixed

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.FieldGraphFieldPointwise
open CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent
open CFSG.LocalAnalysis.ComponentInitial

set_option linter.unusedSectionVars false


section Field

variable {K : Type} [Field K] [Finite K]

theorem mem_zpowers_of_forall_fixedFieldImage (σ : K ≃+* K)
    {β : MulAut (adjointGroup Tag.D4 K)}
    (hβ : ∀ j : adjointGroup Tag.D4 K,
      (j : ModGL Tag.D4 K) ∈ fixedFieldImage Tag.D4 σ → β j = j) :
    β ∈ Subgroup.zpowers (entrywiseAdjointAut Tag.D4 σ) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  have hn₀ := canonicalRep_mem_fixedFieldImage (K := K) σ w₀
  have hu := regularElt_mem_fixedFieldImage (K := K) σ
  have hβA : β ∈ unipotentPairAut Tag.D4 K :=
    mem_unipotentPairAut_of_fix_regular hw₀
      (n₀ := ⟨_, canonicalRep_mem_adjointGroup _ K w₀⟩) (u := regularElt K) rfl
      regularElt_mem_posUnipotent (fun j => by rw [rootCoord_regularElt]; exact one_ne_zero)
      (hβ _ hu) (hβ _ (mul_mem (mul_mem hn₀ hu) (inv_mem hn₀)))
  obtain ⟨π, hπ⟩ := exists_perm_map_simple hβA
  have hπ1 : ∀ i, π i = i := by
    intro i
    have hx : adjX Tag.D4 K i 1 ∈ (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom :=
      Subgroup.mem_map.2
        ⟨adjX Tag.D4 K i 1, ⟨1, rfl⟩, hβ _ (xUnit_mem_fixedFieldImage i (map_one σ))⟩
    rw [(hπ i).1] at hx
    exact eq_of_mem_simplePosSubgroup_xUnit_one hx
  have hε : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map β.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    have h := hπ i
    rw [hπ1 i] at h
    rw [pow_zero, Equiv.Perm.one_apply]
    exact h
  obtain ⟨a, φ, hβeq⟩ := exists_normalAut_mul_graph hε
  rw [d4Graph_zero, mul_one] at hβeq
  subst hβeq
  obtain rfl := eq_one_of_exactNormalAut_zero_fix (hβ _ hu)
  rw [exactNormalAut_one_zero_eq] at hβ ⊢
  have hφ : φ ∈ Subgroup.zpowers σ := by
    refine CFSG.ComponentClassification.UnbalancedCatalog.mem_zpowers_of_fixed fun c hc => ?_
    have h1 := hβ (adjX Tag.D4 K ⟨0, by decide⟩ c) (xUnit_mem_fixedFieldImage _ hc)
    rw [entrywiseAdjointAut_adjX] at h1
    exact adjX_injective _ h1
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hφ
  exact Subgroup.mem_zpowers_iff.2
    ⟨n, (map_zpow (entrywiseAdjointAutHom (τ := Tag.D4)) σ n).symm⟩

end Field

section Perm

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def permOf (β : unipotentPairAut Tag.D4 K) : Equiv.Perm (Fin Tag.D4.rank) :=
  (exists_perm_map_simple β.2).choose

theorem permOf_spec (β : unipotentPairAut Tag.D4 K) (i : Fin Tag.D4.rank) :
    (simplePosSubgroup Tag.D4 K i).map (β : MulAut (adjointGroup Tag.D4 K)).toMonoidHom =
        simplePosSubgroup Tag.D4 K (permOf β i) ∧
      (simpleNegSubgroup Tag.D4 K i).map (β : MulAut (adjointGroup Tag.D4 K)).toMonoidHom =
        simpleNegSubgroup Tag.D4 K (permOf β i) :=
  (exists_perm_map_simple β.2).choose_spec i

theorem permOf_eq {β : unipotentPairAut Tag.D4 K} {π : Equiv.Perm (Fin Tag.D4.rank)}
    (h : ∀ i, (simplePosSubgroup Tag.D4 K i).map
      (β : MulAut (adjointGroup Tag.D4 K)).toMonoidHom = simplePosSubgroup Tag.D4 K (π i)) :
    permOf β = π :=
  perm_map_simple_unique (fun i => (permOf_spec β i).1) h

@[expose] noncomputable def permHom :
    unipotentPairAut Tag.D4 K →* Equiv.Perm (Fin Tag.D4.rank) where
  toFun := permOf
  map_one' := permOf_eq fun i => by
    change (simplePosSubgroup Tag.D4 K i).map (1 : MulAut (adjointGroup Tag.D4 K)).toMonoidHom = _
    rw [map_mulAut_one]
    rfl
  map_mul' β β' := permOf_eq fun i => by
    change (simplePosSubgroup Tag.D4 K i).map
      ((β : MulAut (adjointGroup Tag.D4 K)) * (β' : MulAut (adjointGroup Tag.D4 K))).toMonoidHom = _
    rw [map_toMonoidHom_mul_mulAut, (permOf_spec β' i).1, (permOf_spec β _).1]
    rfl

theorem permHom_apply (β : unipotentPairAut Tag.D4 K) : permHom β = permOf β := rfl

end Perm

section GraphField

variable {K : Type} [Field K] [Finite K]

@[expose] noncomputable def alphaOne (σ : K ≃+* K) : MulAut (adjointGroup Tag.D4 K) :=
  exactNormalAut Tag.D4 K 1 σ 0 * d4Graph K 1

theorem alphaOne_mem (σ : K ≃+* K) : alphaOne σ ∈ unipotentPairAut Tag.D4 K :=
  mul_mem (exactNormalAut_mem 1 σ 0) (d4Graph_mem 1)

theorem alphaOne_adjX (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    alphaOne σ (adjX Tag.D4 K i c) = adjX Tag.D4 K (d4Rho i) (σ c) := by
  rw [alphaOne, normalGraph_apply_adjX]
  simp

theorem alphaOne_adjY (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    alphaOne σ (adjY Tag.D4 K i c) = adjY Tag.D4 K (d4Rho i) (σ c) := by
  rw [alphaOne, MulAut.mul_apply, d4Graph_adjY, exactNormalAut_adjY]
  simp [exactPerm_D4]

theorem permOf_alphaOne (σ : K ≃+* K) : permOf ⟨alphaOne σ, alphaOne_mem σ⟩ = d4Rho := by
  refine permOf_eq fun i => ?_
  exact map_simplePosSubgroup_of_adjX (f := σ) σ.surjective (alphaOne_adjX σ i)

theorem coe_twistedEntrywiseAut_one_D4 (σ : K ≃+* K) (u : adjointGroup Tag.D4 K) :
    (Subtype.val (twistedEntrywiseAut TwistTag.D4 1 σ u) : ModGL Tag.D4 K) =
      d4P K * Units.map (entrywiseHom σ.toRingHom) (u : ModGL Tag.D4 K) * (d4P K)⁻¹ := by
  have h := coe_twistedEntrywiseAut TwistTag.D4 (1 : ℤ) σ u
  rw [zpow_one] at h
  exact h

theorem twistedEntrywiseAut_one_adjX' (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    twistedEntrywiseAut TwistTag.D4 1 σ (adjX Tag.D4 K i c) = adjX Tag.D4 K (d4Rho i) (σ c) := by
  refine Subtype.ext ?_
  have h1 := coe_twistedEntrywiseAut_one_D4 σ (adjX Tag.D4 K i c)
  have h2 := diagramMap_pow_mul_xUnit_mul_inv TwistTag.D4 K 1 i (σ c)
  simp only [pow_one] at h2
  have h3 : Units.map (entrywiseHom σ.toRingHom) (xUnit Tag.D4 K i c) =
      xUnit Tag.D4 K i (σ c) := units_map_entrywiseHom_xUnit σ.toRingHom i c
  refine h1.trans ?_
  show d4P K * Units.map (entrywiseHom σ.toRingHom) (xUnit Tag.D4 K i c) * (d4P K)⁻¹ =
    xUnit Tag.D4 K (d4Rho i) (σ c)
  rw [h3]
  exact h2

theorem twistedEntrywiseAut_one_adjY' (σ : K ≃+* K) (i : Fin Tag.D4.rank) (c : K) :
    twistedEntrywiseAut TwistTag.D4 1 σ (adjY Tag.D4 K i c) = adjY Tag.D4 K (d4Rho i) (σ c) := by
  refine Subtype.ext ?_
  have h1 := coe_twistedEntrywiseAut_one_D4 σ (adjY Tag.D4 K i c)
  have h2 := diagramMap_pow_mul_yUnit_mul_inv TwistTag.D4 K 1 i (σ c)
  simp only [pow_one] at h2
  have h3 : Units.map (entrywiseHom σ.toRingHom) (yUnit Tag.D4 K i c) =
      yUnit Tag.D4 K i (σ c) := units_map_entrywiseHom_yUnit σ.toRingHom i c
  refine h1.trans ?_
  show d4P K * Units.map (entrywiseHom σ.toRingHom) (yUnit Tag.D4 K i c) * (d4P K)⁻¹ =
    yUnit Tag.D4 K (d4Rho i) (σ c)
  rw [h3]
  exact h2

theorem twistedEntrywiseAut_one_eq (σ : K ≃+* K) :
    twistedEntrywiseAut TwistTag.D4 1 σ = alphaOne σ :=
  mulAut_ext_adjX_adjY (τ := Tag.D4) (K := K)
    (fun i c => (twistedEntrywiseAut_one_adjX' σ i c).trans (alphaOne_adjX σ i c).symm)
    (fun i c => (twistedEntrywiseAut_one_adjY' σ i c).trans (alphaOne_adjY σ i c).symm)

theorem alphaOne_fix (σ : K ≃+* K) {j : adjointGroup Tag.D4 K}
    (hj : (j : ModGL Tag.D4 K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
    alphaOne σ j = j := by
  rw [← twistedEntrywiseAut_one_eq]
  have h : j ∈ CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup
      (twistedEntrywiseAut TwistTag.D4 1 σ) := by
    rw [fixedSubgroup_twistedEntrywiseAut_one]
    exact Subgroup.mem_subgroupOf.2 (graphFixedRootGroup_le _ _ _ hj)
  exact h

theorem alphaOne_zpow_fix (σ : K ≃+* K) {j : adjointGroup Tag.D4 K}
    (hj : (j : ModGL Tag.D4 K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (n : ℤ) :
    (alphaOne σ ^ n) j = j := by
  have h : alphaOne σ ∈ MulAction.stabilizer (MulAut (adjointGroup Tag.D4 K)) j := by
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
    exact alphaOne_fix σ hj
  have h' := Subgroup.zpow_mem _ h n
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h'

theorem rootCoord_outer_orbit (j : Fin Tag.D4.rank) (a b c : K) :
    rootCoord (single_pos j) (xUnit Tag.D4 K 0 a * xUnit Tag.D4 K 1 b * xUnit Tag.D4 K 3 c) =
      (if (0 : Fin Tag.D4.rank) = j then a else 0) + (if (1 : Fin Tag.D4.rank) = j then b else 0) +
        (if (3 : Fin Tag.D4.rank) = j then c else 0) := by
  have h := rootCoord_single_list_prod (K := K) j [0, 1, 3]
    (fun i : Fin Tag.D4.rank => if i = 0 then a else if i = 1 then b else c)
  simp (config := { decide := true }) only [List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, List.sum_cons, List.sum_nil, mul_one, if_true, if_false] at h
  rw [mul_assoc, h]
  simp only [add_assoc, add_zero]

theorem exactNormalAut_zero_eq_one_of_forall_graphFixedRootGroup (σ : K ≃+* K)
    (hσ : ∀ c, σ (σ (σ c)) = c) {a : Fin Tag.D4.rank → Kˣ} {φ : K ≃+* K}
    (h : ∀ j : adjointGroup Tag.D4 K,
      (j : ModGL Tag.D4 K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom →
        exactNormalAut Tag.D4 K a φ 0 j = j) :
    exactNormalAut Tag.D4 K a φ 0 = 1 := by
  obtain rfl := eq_one_of_exactNormalAut_zero_fix
    (h _ (regularElt_mem_graphFixedRootGroup σ.toRingHom))
  rw [exactNormalAut_one_zero_eq] at h ⊢
  suffices hφ : φ = 1 by rw [hφ, entrywiseAdjointAut_one]
  refine RingEquiv.ext fun c => ?_
  show φ c = c
  have hc : c ∈ orbitField TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ := by
    rw [mem_orbitField, show (TwistTag.D4.orbit ⟨0, by decide⟩).card = 3 by decide]
    simp only [pow_succ, pow_zero, one_mul, RingHom.mul_def, RingHom.id_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom]
    exact hσ c
  set x : adjointGroup Tag.D4 K := orbitX TwistTag.D4 K σ.toRingHom ⟨0, by decide⟩ ⟨c, hc⟩ with hx
  have h1 : entrywiseAdjointAut Tag.D4 φ x = x :=
    h x (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      (orbitX_mem_graphFixedPosUnipotent TwistTag.D4 σ.toRingHom ⟨0, by decide⟩ ⟨c, hc⟩))
  have hxc : ((x : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) = xUnit Tag.D4 K 0 c *
      xUnit Tag.D4 K 1 (σ c) * xUnit Tag.D4 K 3 (σ (σ c)) :=
    CFSG.RankThree.Chevalley.coe_orbitX_D4_outer σ.toRingHom ⟨c, hc⟩
  have h2 := congrArg (fun g : adjointGroup Tag.D4 K =>
    rootCoord (single_pos (0 : Fin Tag.D4.rank)) (g : ModGL Tag.D4 K)) h1
  simp only [coe_entrywiseAdjointAut, hxc, map_mul, units_map_entrywiseHom_xUnit,
    rootCoord_outer_orbit] at h2
  have hr : Tag.D4.rank ≠ 1 := by decide
  simpa [hr] using h2

theorem d4Rho_centralizer (π : Equiv.Perm (Fin Tag.D4.rank)) (h : π * d4Rho = d4Rho * π) :
    π = 1 ∨ π = d4Rho ∨ π = d4Rho ^ 2 := by
  have key : ∀ π : Equiv.Perm (Fin 4),
      π * (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) =
        (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) * π →
      π = 1 ∨ π = (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ∨
        π = (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ^ 2 := by
    decide +kernel
  exact key π h

theorem mem_zpowers_of_forall_graphFixedRootGroup (σ : K ≃+* K) (hσ : ∀ c, σ (σ (σ c)) = c)
    {β : MulAut (adjointGroup Tag.D4 K)} (hcomm : β * alphaOne σ = alphaOne σ * β)
    (hfix : ∀ j : adjointGroup Tag.D4 K,
      (j : ModGL Tag.D4 K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom → β j = j) :
    β ∈ Subgroup.zpowers (alphaOne σ) := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨w₁, hw₁, h₁⟩ := TwistTag.exists_reversesSigns_mem_relWeylTwist TwistTag.D4
  rw [h₁.eq (reversesSigns_of_forall_length_le hw₀)] at hw₁
  have hn₀ : canonicalRep (coxeterSystem Tag.D4) K w₀ ∈
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom := canonicalRep_mem_graphFixedRootGroup hw₁
  have hu := regularElt_mem_graphFixedRootGroup (K := K) σ.toRingHom
  have hβA : β ∈ unipotentPairAut Tag.D4 K :=
    mem_unipotentPairAut_of_fix_regular hw₀
      (n₀ := ⟨_, canonicalRep_mem_adjointGroup _ K w₀⟩) (u := regularElt K) rfl
      regularElt_mem_posUnipotent (fun j => by rw [rootCoord_regularElt]; exact one_ne_zero)
      (hfix _ hu) (hfix _ (mul_mem (mul_mem hn₀ hu) (inv_mem hn₀)))
  set b : unipotentPairAut Tag.D4 K := ⟨β, hβA⟩ with hb
  set a₁ : unipotentPairAut Tag.D4 K := ⟨alphaOne σ, alphaOne_mem σ⟩ with ha₁
  have hba : b * a₁ = a₁ * b := Subtype.ext hcomm
  have hpa : permHom a₁ = d4Rho := permOf_alphaOne σ
  have hπ : permOf b * d4Rho = d4Rho * permOf b := by
    have h := congrArg permHom hba
    rw [map_mul, map_mul, hpa] at h
    exact h
  obtain ⟨k, -, hπk⟩ : ∃ k : ℕ, k < 3 ∧ permOf b = d4Rho ^ k := by
    rcases d4Rho_centralizer _ hπ with h | h | h
    · exact ⟨0, by norm_num, by simpa using h⟩
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨2, by norm_num, h⟩
  set δ : unipotentPairAut Tag.D4 K := b * (a₁ ^ k)⁻¹ with hδ
  have hδperm : permOf δ = 1 := by
    have h : permHom δ = 1 := by
      rw [hδ, map_mul, map_inv, map_pow, hpa]
      show permOf b * (d4Rho ^ k)⁻¹ = 1
      rw [hπk]
      exact mul_inv_cancel _
    exact h
  have hε : ∀ i, (simplePosSubgroup Tag.D4 K i).map
          (δ : MulAut (adjointGroup Tag.D4 K)).toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map (δ : MulAut (adjointGroup Tag.D4 K)).toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ 0) i) := by
    intro i
    have h := permOf_spec δ i
    rw [hδperm] at h
    simpa using h
  obtain ⟨a, φ, hδeq⟩ := exists_normalAut_mul_graph hε
  rw [d4Graph_zero, mul_one] at hδeq
  have hδfix : ∀ j : adjointGroup Tag.D4 K,
      (j : ModGL Tag.D4 K) ∈ graphFixedRootGroup TwistTag.D4 K σ.toRingHom →
        exactNormalAut Tag.D4 K a φ 0 j = j := by
    intro j hj
    rw [← hδeq]
    have hcoe : ((δ : unipotentPairAut Tag.D4 K) : MulAut (adjointGroup Tag.D4 K)) =
        β * (alphaOne σ ^ k)⁻¹ := by
      rw [hδ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
    have h3 : (alphaOne σ ^ k)⁻¹ j = j := by
      rw [← zpow_natCast, ← zpow_neg]
      exact alphaOne_zpow_fix σ hj _
    rw [hcoe, MulAut.mul_apply, h3]
    exact hfix j hj
  have h1 := exactNormalAut_zero_eq_one_of_forall_graphFixedRootGroup σ hσ hδfix
  rw [← hδeq] at h1
  have hcoe : ((δ : unipotentPairAut Tag.D4 K) : MulAut (adjointGroup Tag.D4 K)) =
      β * (alphaOne σ ^ k)⁻¹ := by
    rw [hδ, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow]
  rw [hcoe, mul_inv_eq_one] at h1
  rw [h1]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k

end GraphField

end CFSG.HardMathSupport.Dickson.DefCharOuter.Export.SporthD4
