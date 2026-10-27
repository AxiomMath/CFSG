module

public import CFSG.LieType.Chevalley.C2E6RootRestrictionA
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplitRootData

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin QuadraticMap

@[expose] def jD : Fin 4 → Fin Tag.E6.rank := (![1, 3, 2, 4] : Fin 4 → Fin 6)

@[expose] def rootD : Fin 8 → Fin Tag.E6.rank → ℤ := (
  ![![1, 0, 1, 1, 1, 1], ![1, 1, 1, 1, 1, 1], ![1, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 2, 1],
    ![1, 1, 2, 2, 1, 1], ![1, 1, 2, 2, 2, 1], ![1, 1, 2, 3, 2, 1], ![1, 2, 2, 3, 2, 1]] :
    Fin 8 → Fin 6 → ℤ)

@[expose] def natD : Fin 8 → Fin 4 ⊕ Fin 4 :=
  ![.inr 0, .inr 1, .inr 2, .inl 3, .inr 3, .inl 2, .inl 1, .inl 0]

@[expose] def natWeight : Fin 4 ⊕ Fin 4 → Fin 4 → ℤ
  | .inl i, k => ∑ l, OrthogonalSplit.eps 4 i l * OrthogonalSplit.simpleRoot 4 k l
  | .inr i, k => -∑ l, OrthogonalSplit.eps 4 i l * OrthogonalSplit.simpleRoot 4 k l

@[expose] def posCenter : Fin 4 → Fin 4 ⊕ Fin 4 := ![.inl 0, .inl 1, .inl 2, .inl 2]

@[expose] def posParam : Fin 4 → Fin 4 ⊕ Fin 4 := ![.inr 1, .inr 2, .inr 3, .inl 3]

@[expose] def negCenter : Fin 4 → Fin 4 ⊕ Fin 4 := ![.inl 1, .inl 2, .inl 3, .inr 3]

@[expose] def negParam : Fin 4 → Fin 4 ⊕ Fin 4 := ![.inr 0, .inr 1, .inr 2, .inr 2]

theorem exists_e6Root_eq_rootD : ∀ j : Fin 8, ∃ k : Fin 72, e6Root k = rootD j := by
  decide +kernel

theorem rootD_zero_five : ∀ j : Fin 8, rootD j (i6 0) = 1 ∧ rootD j (i6 5) = 1 := by decide

theorem exists_rootD_eq_e6Root : ∀ k : Fin 72, e6Root k (i6 0) = 1 → e6Root k (i6 5) = 1 →
    ∃ j : Fin 8, rootD j = e6Root k := by
  decide +kernel

theorem rootD_injective : Function.Injective rootD := by
  intro j j' h
  revert j j'
  decide

theorem natD_injective : Function.Injective natD := by
  intro j j' h
  revert j j'
  decide

theorem exists_natD_eq : ∀ s : Fin 4 ⊕ Fin 4, ∃ j, natD j = s := by decide

theorem weight_rootD : ∀ (j : Fin 8) (k : Fin 4),
    rootWeight (jD k) (rootD j) = natWeight (natD j) k := by
  decide +kernel

theorem eq_natD_of_weight : ∀ (j : Fin 8) (s : Fin 4 ⊕ Fin 4),
    (∀ k, rootWeight (jD k) (rootD j) = natWeight s k) → s = natD j := by
  decide +kernel

theorem raise_rootD : ∀ (j : Fin 8) (k : Fin 4),
    ((∃ j', rootD j' = rootD j + Pi.single (jD k) 1) ↔
      (natD j = (posCenter k).swap ∨ natD j = (posParam k).swap)) := by
  decide

theorem raise_natD : ∀ (j j' : Fin 8) (k : Fin 4), rootD j' = rootD j + Pi.single (jD k) 1 →
    (natD j = (posCenter k).swap ∧ natD j' = posParam k) ∨
      (natD j = (posParam k).swap ∧ natD j' = posCenter k) := by
  decide

theorem lower_rootD : ∀ (j : Fin 8) (k : Fin 4),
    ((∃ j', rootD j' = rootD j - Pi.single (jD k) 1) ↔
      (natD j = (negCenter k).swap ∨ natD j = (negParam k).swap)) := by
  decide

theorem lower_natD : ∀ (j j' : Fin 8) (k : Fin 4), rootD j' = rootD j - Pi.single (jD k) 1 →
    (natD j = (negCenter k).swap ∧ natD j' = negParam k) ∨
      (natD j = (negParam k).swap ∧ natD j' = negCenter k) := by
  decide

theorem center_param_ne : ∀ k : Fin 4,
    (posCenter k).swap ≠ (posParam k).swap ∧ (negCenter k).swap ≠ (negParam k).swap := by
  decide

theorem rootD_ne_single : ∀ (j : Fin 8) (k : Fin 4),
    rootD j ≠ Pi.single (jD k) 1 ∧ rootD j ≠ -Pi.single (jD k) 1 := by
  decide

theorem diag_rootD : ∀ j : Fin 8, ∃ j', rootD j' = rhoL (rootD j) ∧
    natD j' = Equiv.swap (.inl 3) (.inr 3) (natD j) := by
  decide

theorem isRoot_rootD (j : Fin 8) : IsRoot Tag.E6 (rootD j) := by
  obtain ⟨k, hk⟩ := exists_e6Root_eq_rootD j
  rw [← hk]
  exact isRoot_e6Root k

theorem exists_rootD_eq
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h0 : α (0 : Fin 6) = 1) (h5 : α (5 : Fin 6) = 1) : ∃ j, rootD j = α := by
  obtain ⟨k, rfl⟩ := exists_e6Root_eq hα
  exact exists_rootD_eq_e6Root k h0 h5

abbrev vecD (j : Fin 8) : RootModule Tag.E6 K := rootVec Tag.E6 K (rootD j)

theorem moduleD_eq_span
    : moduleD = Submodule.span K (Set.range vecD) := by
  rw [moduleD]
  congr 1
  ext v
  constructor
  · rintro ⟨α, hα, h0, h5, rfl⟩
    obtain ⟨j, rfl⟩ := exists_rootD_eq hα h0 h5
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨rootD j, isRoot_rootD j, (rootD_zero_five j).1, (rootD_zero_five j).2, rfl⟩

theorem vecD_mem (j : Fin 8) : vecD j ∈ moduleD := by
  rw [moduleD_eq_span]
  exact Submodule.subset_span ⟨j, rfl⟩

theorem linearIndependent_vecD : LinearIndependent K vecD := by
  have h := (Finsupp.basisSingleOne (R := K) (ι := Label Tag.E6)).linearIndependent.comp
    (fun j => (Sum.inr ⟨rootD j, isRoot_rootD j⟩ : Label Tag.E6))
    (fun j j' h => rootD_injective (by simpa using h))
  convert h using 1
  funext j
  simp [vecD, rootVec_eq_single (isRoot_rootD j)]

@[expose] def basisD : Module.Basis (Fin 8) K moduleD :=
  (Module.Basis.span linearIndependent_vecD).map (LinearEquiv.ofEq _ _ moduleD_eq_span.symm)

theorem basisD_apply
    (j : Fin 8) : basisD j = ⟨vecD j, vecD_mem j⟩ := by
  apply Subtype.ext
  simp [basisD, Module.Basis.span_apply]

@[expose] def eD : Fin 8 ≃ Fin 4 ⊕ Fin 4 :=
  Equiv.ofBijective natD ⟨natD_injective, exists_natD_eq⟩

@[expose] def phiD : moduleD ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  basisD.equiv (Pi.basisFun K (Fin 4 ⊕ Fin 4)) eD

theorem phiD_vecD
    (j : Fin 8) : phiD ⟨vecD j, vecD_mem j⟩ = Pi.single (natD j) 1 := by
  rw [← basisD_apply, phiD, Module.Basis.equiv_apply, Pi.basisFun_apply]
  rfl

theorem phiD_rootVec
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) (h0 : α (0 : Fin 6) = 1)
    (h5 : α (5 : Fin 6) = 1) (hmem : rootVec Tag.E6 K α ∈ moduleD) (s : Fin 4 ⊕ Fin 4)
    (hs : ∀ k : Fin 4, rootWeight (jD k) α = natWeight s k) :
    phiD ⟨rootVec Tag.E6 K α, hmem⟩ = Pi.single s 1 := by
  obtain ⟨j, rfl⟩ := exists_rootD_eq hα h0 h5
  rw [eq_natD_of_weight j s hs]
  exact phiD_vecD j

theorem existsUnique_natWeight
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h0 : α (0 : Fin 6) = 1) (h5 : α (5 : Fin 6) = 1) :
    ∃! s : Fin 4 ⊕ Fin 4, ∀ k : Fin 4, rootWeight (jD k) α = natWeight s k := by
  obtain ⟨j, rfl⟩ := exists_rootD_eq hα h0 h5
  exact ⟨natD j, weight_rootD j, fun s hs => eq_natD_of_weight j s hs⟩

theorem orthElementaryMap_single (p q s : Fin 4 ⊕ Fin 4) (t : K) :
    orthElementaryMap (quadPlus 4 K) (Pi.single p 1) (t • Pi.single q 1) (Pi.single s 1) =
      Pi.single s 1 + (if p.swap = s then t • Pi.single q 1 else 0) -
        (if q.swap = s then t • Pi.single p 1 else 0) := by
  rw [orthElementaryMap_apply, polar_single, polar_smul_right, polar_single,
    QuadraticMap.map_smul, CFSG.ClassicalGroups.Orthogonal.quadPlus_single, smul_zero, zero_mul,
    zero_smul, sub_zero]
  congr 1
  · congr 1
    split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]
  · split_ifs with h
    · subst h
      simp
    · simp [Ne.symm h]

theorem simpleRoot_zero : OrthogonalSplit.simpleRoot 4 0 =
    OrthogonalSplit.eps 4 0 - OrthogonalSplit.eps 4 1 := by decide

theorem simpleRoot_one : OrthogonalSplit.simpleRoot 4 1 =
    OrthogonalSplit.eps 4 1 - OrthogonalSplit.eps 4 2 := by decide

theorem simpleRoot_two : OrthogonalSplit.simpleRoot 4 2 =
    OrthogonalSplit.eps 4 2 - OrthogonalSplit.eps 4 3 := by decide

theorem simpleRoot_three : OrthogonalSplit.simpleRoot 4 3 =
    OrthogonalSplit.eps 4 2 + OrthogonalSplit.eps 4 3 := by decide

theorem rootElt_simpleRoot (k : Fin 4) (c : K) :
    ((rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus 4 K) (Pi.single (posCenter k) 1)
        ((-c) • Pi.single (posParam k) 1) := by
  fin_cases k
  · rw [show (⟨0, _⟩ : Fin 4) = 0 from rfl, simpleRoot_zero, rootElt_eps_sub_eps (by decide)]
    rfl
  · rw [show (⟨1, _⟩ : Fin 4) = 1 from rfl, simpleRoot_one, rootElt_eps_sub_eps (by decide)]
    rfl
  · rw [show (⟨2, _⟩ : Fin 4) = 2 from rfl, simpleRoot_two, rootElt_eps_sub_eps (by decide)]
    rfl
  · rw [show (⟨3, _⟩ : Fin 4) = 3 from rfl, simpleRoot_three, rootElt_eps_add_eps (by decide)]
    rfl

theorem rootElt_neg_simpleRoot (k : Fin 4) (c : K) :
    ((rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
      (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) =
      orthElementaryMap (quadPlus 4 K) (Pi.single (negCenter k) 1)
        ((-c) • Pi.single (negParam k) 1) := by
  fin_cases k
  · rw [show (⟨0, _⟩ : Fin 4) = 0 from rfl, simpleRoot_zero, neg_sub, sub_eq_neg_add,
      rootElt_neg_eps_add_eps (by decide)]
    rfl
  · rw [show (⟨1, _⟩ : Fin 4) = 1 from rfl, simpleRoot_one, neg_sub, sub_eq_neg_add,
      rootElt_neg_eps_add_eps (by decide)]
    rfl
  · rw [show (⟨2, _⟩ : Fin 4) = 2 from rfl, simpleRoot_two, neg_sub, sub_eq_neg_add,
      rootElt_neg_eps_add_eps (by decide)]
    rfl
  · rw [show (⟨3, _⟩ : Fin 4) = 3 from rfl, simpleRoot_three, neg_add, ← sub_eq_add_neg,
      rootElt_neg_eps_sub_eps (by decide)]
    rfl

theorem xOp_vecD
    (j : Fin 8) (k : Fin 4) (c : K) :
    xOp Tag.E6 K (jD k) c (vecD j) =
      vecD j + c • rootVec Tag.E6 K (rootD j + Pi.single (jD k) 1) :=
  xOp_rootVec_E6 (jD k) c (isRoot_rootD j) (rootD_ne_single j k).1 (rootD_ne_single j k).2

theorem yOp_vecD
    (j : Fin 8) (k : Fin 4) (c : K) :
    yOp Tag.E6 K (jD k) c (vecD j) =
      vecD j + c • rootVec Tag.E6 K (rootD j - Pi.single (jD k) 1) :=
  yOp_rootVec_E6 (jD k) c (isRoot_rootD j) (rootD_ne_single j k).1 (rootD_ne_single j k).2

theorem jD_ne_zero_five (k : Fin 4) : jD k ≠ i6 0 ∧ jD k ≠ i6 5 := by
  revert k
  decide

theorem raiseD_or (j : Fin 8) (k : Fin 4) :
    (∃ j', rootD j' = rootD j + Pi.single (jD k) 1) ∨
      ¬IsRoot Tag.E6 (rootD j + Pi.single (jD k) 1) := by
  by_cases h : IsRoot Tag.E6 (rootD j + Pi.single (jD k) 1)
  · obtain ⟨h0, h5⟩ := rootD_zero_five j
    obtain ⟨hne0, hne5⟩ := jD_ne_zero_five k
    refine Or.inl (exists_rootD_eq h ?_ ?_)
    · show (rootD j + Pi.single (jD k) 1 : Fin Tag.E6.rank → ℤ) (i6 0) = 1
      rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hne0), add_zero]
      exact h0
    · show (rootD j + Pi.single (jD k) 1 : Fin Tag.E6.rank → ℤ) (i6 5) = 1
      rw [Pi.add_apply, Pi.single_eq_of_ne (Ne.symm hne5), add_zero]
      exact h5
  · exact Or.inr h

theorem lowerD_or (j : Fin 8) (k : Fin 4) :
    (∃ j', rootD j' = rootD j - Pi.single (jD k) 1) ∨
      ¬IsRoot Tag.E6 (rootD j - Pi.single (jD k) 1) := by
  by_cases h : IsRoot Tag.E6 (rootD j - Pi.single (jD k) 1)
  · obtain ⟨h0, h5⟩ := rootD_zero_five j
    obtain ⟨hne0, hne5⟩ := jD_ne_zero_five k
    refine Or.inl (exists_rootD_eq h ?_ ?_)
    · show (rootD j - Pi.single (jD k) 1 : Fin Tag.E6.rank → ℤ) (i6 0) = 1
      rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hne0), sub_zero]
      exact h0
    · show (rootD j - Pi.single (jD k) 1 : Fin Tag.E6.rank → ℤ) (i6 5) = 1
      rw [Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hne5), sub_zero]
      exact h5
  · exact Or.inr h

theorem rootVec_raiseD_mem (j : Fin 8) (k : Fin 4) :
    rootVec Tag.E6 K (rootD j + Pi.single (jD k) 1) ∈ moduleD := by
  rcases raiseD_or j k with ⟨j', hj'⟩ | h
  · rw [← hj']
    exact vecD_mem j'
  · rw [rootVec_eq_zero_of_not h]
    exact Submodule.zero_mem _

theorem rootVec_lowerD_mem (j : Fin 8) (k : Fin 4) :
    rootVec Tag.E6 K (rootD j - Pi.single (jD k) 1) ∈ moduleD := by
  rcases lowerD_or j k with ⟨j', hj'⟩ | h
  · rw [← hj']
    exact vecD_mem j'
  · rw [rootVec_eq_zero_of_not h]
    exact Submodule.zero_mem _

theorem moduleD_le_comap {f : Module.End K (RootModule Tag.E6 K)}
    (hf : ∀ j, f (vecD j) ∈ moduleD) : ∀ v ∈ moduleD, f v ∈ moduleD := by
  intro v hv
  have : moduleD ≤ moduleD.comap f := by
    conv_lhs => rw [moduleD_eq_span]
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hf j
  exact this hv

theorem xOp_mem_moduleD
    (k : Fin 4) (c : K) :
    ∀ v ∈ moduleD, xOp Tag.E6 K (jD k) c v ∈ moduleD :=
  moduleD_le_comap fun j => by
    rw [xOp_vecD]
    exact moduleD.add_mem (vecD_mem j) (moduleD.smul_mem c (rootVec_raiseD_mem j k))

theorem yOp_mem_moduleD
    (k : Fin 4) (c : K) :
    ∀ v ∈ moduleD, yOp Tag.E6 K (jD k) c v ∈ moduleD :=
  moduleD_le_comap fun j => by
    rw [yOp_vecD]
    exact moduleD.add_mem (vecD_mem j) (moduleD.smul_mem c (rootVec_lowerD_mem j k))

theorem phiD_add_smul
    {a b : RootModule Tag.E6 K} (ha : a ∈ moduleD) (hb : b ∈ moduleD) (c : K)
    (h : a + c • b ∈ moduleD) :
    phiD ⟨a + c • b, h⟩ = phiD ⟨a, ha⟩ + c • phiD ⟨b, hb⟩ := by
  rw [← map_smul, ← map_add]
  rfl

theorem orthElementaryMap_single_K {p q s : Fin 4 ⊕ Fin 4} (hpq : p.swap ≠ q.swap) (c : K) :
    orthElementaryMap (quadPlus 4 K) (Pi.single p 1) ((-c) • Pi.single q 1) (Pi.single s 1) =
      Pi.single s 1 + (if s = p.swap then c • Pi.single q 1
        else if s = q.swap then c • Pi.single p 1 else 0) := by
  rw [orthElementaryMap_single]
  by_cases h1 : s = p.swap
  · subst h1
    rw [ite_eq_left rfl, ite_eq_right (fun h => hpq h.symm), ite_eq_left rfl, sub_zero, neg_K]
  · rw [ite_eq_right (Ne.symm h1), ite_eq_right h1, add_zero]
    by_cases h2 : s = q.swap
    · subst h2
      rw [ite_eq_left rfl, ite_eq_left rfl, sub_eq_add_neg, neg_smul, neg_neg]
    · rw [ite_eq_right (Ne.symm h2), ite_eq_right h2, sub_zero, add_zero]

theorem phiD_shift
    {j : Fin 8} {e : Fin Tag.E6.rank → ℤ} {p q : Fin 4 ⊕ Fin 4}
    (hpq : p.swap ≠ q.swap) (c : K)
    (hraise : (∃ j', rootD j' = rootD j + e) ↔ (natD j = p.swap ∨ natD j = q.swap))
    (hnat : ∀ j', rootD j' = rootD j + e →
      (natD j = p.swap ∧ natD j' = q) ∨ (natD j = q.swap ∧ natD j' = p))
    (hor : (∃ j', rootD j' = rootD j + e) ∨ ¬IsRoot Tag.E6 (rootD j + e))
    (hmem : rootVec Tag.E6 K (rootD j + e) ∈ moduleD) :
    Pi.single (natD j) 1 + c • phiD ⟨rootVec Tag.E6 K (rootD j + e), hmem⟩ =
      Pi.single (natD j) 1 + (if natD j = p.swap then c • Pi.single q 1
        else if natD j = q.swap then c • Pi.single p 1 else 0) := by
  congr 1
  rcases hor with ⟨j', hj'⟩ | hnot
  · have hv : (⟨rootVec Tag.E6 K (rootD j + e), hmem⟩ : moduleD) = ⟨vecD j', vecD_mem j'⟩ :=
      Subtype.ext (show rootVec Tag.E6 K (rootD j + e) = vecD j' by rw [← hj'])
    rw [hv, phiD_vecD]
    rcases hnat j' hj' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [ite_eq_left h1, h2]
    · rw [ite_eq_right (fun h => hpq (h1.symm.trans h).symm), ite_eq_left h1, h2]
  · have hv : (⟨rootVec Tag.E6 K (rootD j + e), hmem⟩ : moduleD) = 0 :=
      Subtype.ext (show rootVec Tag.E6 K (rootD j + e) = 0 from rootVec_eq_zero_of_not hnot)
    have hno : ¬(natD j = p.swap ∨ natD j = q.swap) := by
      rw [← hraise]
      rintro ⟨j', hj'⟩
      exact hnot (hj' ▸ isRoot_rootD j')
    push Not at hno
    rw [hv, map_zero, smul_zero, ite_eq_right hno.1, ite_eq_right hno.2]

theorem phiD_xOp
    (k : Fin 4) (c : K) {v : RootModule Tag.E6 K} (hv : v ∈ moduleD) :
    phiD ⟨xOp Tag.E6 K (jD k) c v, xOp_mem_moduleD k c v hv⟩ =
      rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c (phiD ⟨v, hv⟩) := by
  have key : phiD.toLinearMap ∘ₗ (xOp Tag.E6 K (jD k) c).restrict (xOp_mem_moduleD k c) =
      ((rootElt 4 K (OrthogonalSplit.simpleRoot 4 k) c : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
        (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) ∘ₗ phiD.toLinearMap := by
    refine basisD.ext fun j => ?_
    have hR := LinearMap.congr_fun (rootElt_simpleRoot k c) (Pi.single (natD j) 1)
    rw [LinearEquiv.coe_coe] at hR
    rw [LinearMap.comp_apply, LinearMap.comp_apply, basisD_apply, LinearMap.restrict_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, phiD_vecD, hR,
      orthElementaryMap_single_K (center_param_ne k).1]
    have hx : (⟨xOp Tag.E6 K (jD k) c (vecD j), xOp_mem_moduleD k c _ (vecD_mem j)⟩ : moduleD) =
        ⟨vecD j + c • rootVec Tag.E6 K (rootD j + Pi.single (jD k) 1),
          moduleD.add_mem (vecD_mem j) (moduleD.smul_mem c (rootVec_raiseD_mem j k))⟩ :=
      Subtype.ext (xOp_vecD j k c)
    rw [hx, phiD_add_smul (vecD_mem j) (rootVec_raiseD_mem j k), phiD_vecD]
    exact phiD_shift (center_param_ne k).1 c (raise_rootD j k) (fun j' => raise_natD j j' k)
      (raiseD_or j k) _
  exact congrArg (fun F : moduleD →ₗ[K] (Fin 4 ⊕ Fin 4 → K) => F ⟨v, hv⟩) key

theorem phiD_yOp
    (k : Fin 4) (c : K) {v : RootModule Tag.E6 K} (hv : v ∈ moduleD) :
    phiD ⟨yOp Tag.E6 K (jD k) c v, yOp_mem_moduleD k c v hv⟩ =
      rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c (phiD ⟨v, hv⟩) := by
  have key : phiD.toLinearMap ∘ₗ (yOp Tag.E6 K (jD k) c).restrict (yOp_mem_moduleD k c) =
      ((rootElt 4 K (-OrthogonalSplit.simpleRoot 4 k) c : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] _) :
        (Fin 4 ⊕ Fin 4 → K) →ₗ[K] _) ∘ₗ phiD.toLinearMap := by
    refine basisD.ext fun j => ?_
    have hR := LinearMap.congr_fun (rootElt_neg_simpleRoot k c) (Pi.single (natD j) 1)
    rw [LinearEquiv.coe_coe] at hR
    rw [LinearMap.comp_apply, LinearMap.comp_apply, basisD_apply, LinearMap.restrict_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, phiD_vecD, hR,
      orthElementaryMap_single_K (center_param_ne k).2]
    have hy : (⟨yOp Tag.E6 K (jD k) c (vecD j), yOp_mem_moduleD k c _ (vecD_mem j)⟩ : moduleD) =
        ⟨vecD j + c • rootVec Tag.E6 K (rootD j - Pi.single (jD k) 1),
          moduleD.add_mem (vecD_mem j) (moduleD.smul_mem c (rootVec_lowerD_mem j k))⟩ :=
      Subtype.ext (yOp_vecD j k c)
    rw [hy, phiD_add_smul (vecD_mem j) (rootVec_lowerD_mem j k), phiD_vecD]
    simp only [sub_eq_add_neg]
    have hraise := lower_rootD j k
    have hnat := fun j' => lower_natD j j' k
    have hor := lowerD_or j k
    simp only [sub_eq_add_neg] at hraise hnat hor
    exact phiD_shift (center_param_ne k).2 c hraise hnat hor _
  exact congrArg (fun F : moduleD →ₗ[K] (Fin 4 ⊕ Fin 4 → K) => F ⟨v, hv⟩) key

theorem exists_jD_of_mem_setD {i : Fin Tag.E6.rank} (hi : i ∈ setD) : ∃ k, jD k = i := by
  simp only [setD] at hi
  rcases hi with rfl | rfl | rfl | rfl
  exacts [⟨0, rfl⟩, ⟨2, rfl⟩, ⟨1, rfl⟩, ⟨3, rfl⟩]

theorem mem_moduleD_of_mem_groupD
    {g : ModGL Tag.E6 K} (hg : g ∈ groupD) :
    ∀ v ∈ moduleD, (g : Module.End K (RootModule Tag.E6 K)) v ∈ moduleD := by
  refine mem_of_mem_subsystemGroup (fun i hi c => ?_) (fun i hi c => ?_) hg
  · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
    exact xOp_mem_moduleD k c
  · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
    exact yOp_mem_moduleD k c

@[expose] def swapE4F4 : (Fin 4 ⊕ Fin 4 → K) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K) :=
  LinearEquiv.funCongrLeft K K (Equiv.swap (.inl 3) (.inr 3))

theorem swapE4F4_single (s : Fin 4 ⊕ Fin 4) :
    swapE4F4 (Pi.single s (1 : K)) = Pi.single (Equiv.swap (.inl 3) (.inr 3) s) 1 := by
  funext x
  simp [swapE4F4, Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem diagramMap_vecD (j : Fin 8) :
    diagE6 (vecD j) = rootVec Tag.E6 K (rhoL (rootD j)) :=
  diagramMap_rootVec TwistTag.E6 K (rootD j) (isRoot_rootD j)

theorem diagramMap_mem_moduleD : ∀ v ∈ moduleD, diagE6 v ∈ moduleD :=
  moduleD_le_comap fun j => by
    rw [diagramMap_vecD]
    obtain ⟨j', hj', -⟩ := diag_rootD j
    rw [← hj']
    exact vecD_mem j'

theorem phiD_diagramMap {v : RootModule Tag.E6 K} (hv : v ∈ moduleD) :
    phiD ⟨diagE6 v, diagramMap_mem_moduleD v hv⟩ = swapE4F4 (phiD ⟨v, hv⟩) := by
  have key : phiD.toLinearMap ∘ₗ diagE6.restrict diagramMap_mem_moduleD =
      swapE4F4.toLinearMap ∘ₗ phiD.toLinearMap := by
    refine basisD.ext fun j => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, basisD_apply, LinearMap.restrict_apply]
    obtain ⟨j', hj', hnat⟩ := diag_rootD j
    have : (⟨diagE6 (vecD j), diagramMap_mem_moduleD _ (vecD_mem j)⟩ : moduleD) =
        ⟨vecD j', vecD_mem j'⟩ :=
      Subtype.ext (show diagE6 (vecD j) = vecD j' by rw [diagramMap_vecD, ← hj'])
    refine (congrArg phiD this).trans ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, phiD_vecD, phiD_vecD, swapE4F4_single, hnat]
  exact congrArg (fun F : moduleD →ₗ[K] (Fin 4 ⊕ Fin 4 → K) => F ⟨v, hv⟩) key

end CFSG.LieType.Chevalley.C2E6Std
