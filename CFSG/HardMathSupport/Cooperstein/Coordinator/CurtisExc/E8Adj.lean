module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.E8AdjOps
public import CFSG.LieType.Chevalley.CoordinateFieldBaseChange

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

open CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CoxeterSystem

@[expose] def thetaWords : List (List (Fin Tag.E8.rank)) :=
  ([[2, 3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
   [3, 4, 5, 6, 7, 2, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
   [3, 4, 5, 6, 7, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
   [4, 5, 6, 7, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
   [5, 6, 7, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
   [6, 7, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
   [7, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7],
   [6, 5, 4, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7]] : List (List (Fin 8)))

theorem thetaWords_check : ∀ j : Fin Tag.E8.rank,
    (thetaWords.getD j []).foldr reflectL (List.ofFn e8Theta) = List.ofFn (Pi.single j 1) := by
  decide +kernel

theorem foldr_thetaWords (j : Fin Tag.E8.rank) :
    (thetaWords.getD j []).foldr (reflect .E8) e8Theta = Pi.single j 1 := by
  refine List.ofFn_injective ?_
  rw [ofFn_foldr_reflect, thetaWords_check]


theorem weylElt_one_rootVec {F : Type} [Field F] [CharP F 2]
    (i : Fin Tag.E8.rank) {α : Fin Tag.E8.rank → ℤ}
    (hα : IsRoot .E8 α) :
    (weylElt .E8 F i 1 : Module.End F (AdjMod F)) (rootVec .E8 F α) =
      rootVec .E8 F (reflect .E8 i α) := by
  rw [weylElt_rootVec i 1 hα]
  simp [CharTwo.neg_eq]

section Adj


variable (F : Type) [Field F] [CharP F 2]

@[expose] def ιF : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F

@[expose] def adjRep : Representation F (adjointGroup .E8 (ZMod 2)) (AdjMod F) :=
  (Units.coeHom (Module.End F (AdjMod F))).comp
    ((baseChangeGL (τ := .E8) (ιF F)).comp (adjointGroup .E8 (ZMod 2)).subtype)

variable {F}

theorem adjRep_apply (g : adjointGroup .E8 (ZMod 2)) :
    adjRep F g = ((baseChangeGL (τ := .E8) (ιF F) (g : ModGL .E8 (ZMod 2)) : ModGL .E8 F) :
      Module.End F (AdjMod F)) := rfl

@[expose] def e8Datum : CurtisDatum (adjointGroup .E8 (ZMod 2)) (coxeterSystem .E8) 2 :=
  chevDatum .E8 (ZMod 2) 2 exists_weyl_neg_E8

theorem adjRep_xC (i : Fin Tag.E8.rank) (c : ZMod 2) :
    adjRep F (xC .E8 (ZMod 2) i c) = xOp .E8 F i (ιF F c) := by
  rw [adjRep_apply]
  show ((baseChangeGL (τ := .E8) (ιF F) (xUnit .E8 (ZMod 2) i c) : ModGL .E8 F) :
    Module.End F (AdjMod F)) = _
  rw [baseChangeGL_xUnit]
  rfl

theorem adjRep_yC (i : Fin Tag.E8.rank) (c : ZMod 2) :
    adjRep F (yC .E8 (ZMod 2) i c) = yOp .E8 F i (ιF F c) := by
  rw [adjRep_apply]
  show ((baseChangeGL (τ := .E8) (ιF F) (yUnit .E8 (ZMod 2) i c) : ModGL .E8 F) :
    Module.End F (AdjMod F)) = _
  rw [baseChangeGL_yUnit]
  rfl

theorem baseChangeGL_weylElt_one'' {R S : Type} [Field R] [Field S] (f : R →+* S)
    (i : Fin Tag.E8.rank) : baseChangeGL (τ := .E8) f (weylElt .E8 R i 1) = weylElt .E8 S i 1 := by
  rw [weylElt_eq_xUnit_mul, weylElt_eq_xUnit_mul, map_mul, map_mul, baseChangeGL_xUnit,
    baseChangeGL_yUnit]
  simp

theorem adjRep_nC (i : Fin Tag.E8.rank) :
    adjRep F (nC .E8 (ZMod 2) i) = (weylElt .E8 F i 1 : Module.End F (AdjMod F)) := by
  rw [adjRep_apply]
  show ((baseChangeGL (τ := .E8) (ιF F) (weylElt .E8 (ZMod 2) i 1) : ModGL .E8 F) :
    Module.End F (AdjMod F)) = _
  rw [baseChangeGL_weylElt_one'']

theorem adjRep_fixU {v : AdjMod F} (hv : v ∈ e8Datum.fixU (adjRep F)) :
    ∃ c : F, v = c • rootVec .E8 F e8Theta := by
  refine ⟨_, eq_smul_rootVec_theta_of_fixed v fun i => ?_⟩
  have h := hv (xC .E8 (ZMod 2) i 1)
    (e8Datum.X_le i (xC_mem_X (hw := exists_weyl_neg_E8) i 1))
  rw [adjRep_xC, map_one] at h
  rw [Dop_apply, h, sub_self]

section Span

open scoped Classical in
abbrev spanθ (F : Type) [Field F] [CharP F 2] : Submodule F (AdjMod F) :=
  orbitSpan (adjRep F) (rootVec .E8 F e8Theta)

theorem span_reflect (i : Fin Tag.E8.rank) {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α)
    (h : rootVec .E8 F α ∈ spanθ F) : rootVec .E8 F (reflect .E8 i α) ∈ spanθ F := by
  have := orbitSpan_stable (adjRep F) (rootVec .E8 F e8Theta) (nC .E8 (ZMod 2) i) h
  rwa [adjRep_nC, weylElt_one_rootVec i hα] at this

theorem span_foldr (l : List (Fin Tag.E8.rank)) {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α)
    (h : rootVec .E8 F α ∈ spanθ F) :
    IsRoot .E8 (l.foldr (reflect .E8) α) ∧
      rootVec .E8 F (l.foldr (reflect .E8) α) ∈ spanθ F := by
  induction l with
  | nil => exact ⟨hα, h⟩
  | cons i l ih =>
    rw [List.foldr_cons]
    exact ⟨.reflect i ih.1, span_reflect i ih.1 ih.2⟩

theorem span_all_roots {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) :
    rootVec .E8 F α ∈ spanθ F := by
  induction hα with
  | basis j =>
    have := span_foldr (thetaWords.getD j []) isRoot_theta (mem_orbitSpan_self (adjRep F) _)
    rw [foldr_thetaWords] at this
    exact this.2
  | reflect i hv ih => exact span_reflect i hv ih

theorem span_hVec (i : Fin Tag.E8.rank) : hVec .E8 F i ∈ spanθ F := by
  have h1 := orbitSpan_stable (adjRep F) (rootVec .E8 F e8Theta) (yC .E8 (ZMod 2) i 1)
    (span_all_roots (isRoot_single .E8 i))
  rw [adjRep_yC, map_one, yOp_rootVec_single_eq] at h1
  have h2 := span_all_roots (F := F) (isRoot_single .E8 i)
  have h3 := span_all_roots (F := F) (isRoot_neg_single .E8 i)
  have := sub_mem (sub_mem h1 h2) h3
  simpa [add_assoc] using this

theorem orbitSpan_adj : spanθ F = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  refine adj_induction (P := fun v => v ∈ spanθ F) (zero_mem _) (fun _ _ => add_mem)
    (fun c _ h => Submodule.smul_mem _ c h) span_hVec (fun α => ?_) v
  by_cases hα : IsRoot .E8 α
  · exact span_all_roots hα
  · rw [rootVec_eq_zero hα]; exact zero_mem _

end Span

instance : Nontrivial (AdjMod F) := ⟨⟨0, hVec .E8 F n8, fun h => by
  have := congrArg (fun v : AdjMod F => v (Sum.inl n8)) h
  simp [hVec] at this⟩⟩

theorem isSimpleRep_adj : IsSimpleRep (adjRep F) :=
  e8Datum.isSimpleRep_of_fixU (p := 2) (adjRep F) (y := rootVec .E8 F e8Theta)
    (fun _ hx => adjRep_fixU hx) orbitSpan_adj

theorem rootVec_theta_ne_zero : rootVec .E8 F e8Theta ≠ 0 := by
  rw [rootVec_eq_single isRoot_theta]
  intro h
  have := congrArg (fun v : AdjMod F => v (Sum.inr ⟨e8Theta, isRoot_theta⟩)) h
  rw [Finsupp.single_eq_same, Finsupp.zero_apply] at this
  exact one_ne_zero this

theorem rootVec_theta_mem_fixU : rootVec .E8 F e8Theta ∈ e8Datum.fixU (adjRep F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).1
    (e8Datum.fixU_ne_bot (p := 2) (adjRep F))
  obtain ⟨c, rfl⟩ := adjRep_fixU hx
  have hc : c ≠ 0 := fun h => hx0 (by rw [h, zero_smul])
  have := Submodule.smul_mem _ c⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

theorem torus_eq_one {h : adjointGroup .E8 (ZMod 2)} (hh : h ∈ e8Datum.H) : h = 1 := by
  have h1 : ((h : ModGL .E8 (ZMod 2))) ^ (Nat.card (ZMod 2) - 1) = 1 :=
    pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
  rw [Nat.card_zmod] at h1
  exact Subtype.ext (by simpa using h1)

theorem heckeT_adj (i : Fin Tag.E8.rank) (v : AdjMod F) :
    e8Datum.heckeT (adjRep F) i v =
      (weylElt .E8 F i 1 : Module.End F (AdjMod F)) v +
        xOp .E8 F i 1 ((weylElt .E8 F i 1 : Module.End F (AdjMod F)) v) := by
  unfold e8Datum
  rw [heckeT_chevDatum]
  have hU : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
  rw [hU, Finset.sum_pair (by decide)]
  simp only [map_mul, Module.End.mul_apply, adjRep_xC, adjRep_nC, map_zero, map_one, xOp_zero,
    Module.End.one_apply]

theorem rootVec_add_self (v : AdjMod F) : v + v = 0 := by
  rw [← two_smul F v, CharTwo.two_eq_zero, zero_smul]

theorem theta_ne_single (i : Fin Tag.E8.rank) : e8Theta ≠ Pi.single i 1 := by
  revert i; decide +kernel

theorem theta_ne_neg_single (i : Fin Tag.E8.rank) : e8Theta ≠ -Pi.single i 1 := by
  revert i; decide +kernel

theorem theta_sub_ne_single : e8Theta - Pi.single n8 1 ≠ Pi.single n8 1 := by decide +kernel

theorem theta_sub_ne_neg_single : e8Theta - Pi.single n8 1 ≠ -Pi.single n8 1 := by decide +kernel

theorem theta_sub_add : e8Theta - Pi.single n8 1 + Pi.single n8 1 = e8Theta := sub_add_cancel _ _

theorem heckeT_adj_theta_of_ne {i : Fin Tag.E8.rank} (hi : i ≠ n8) :
    e8Datum.heckeT (adjRep F) i (rootVec .E8 F e8Theta) = 0 := by
  rw [heckeT_adj, weylElt_one_rootVec i isRoot_theta, reflect_theta_of_ne i hi,
    xOp_one_rootVec_of_ne i isRoot_theta (theta_ne_single i) (theta_ne_neg_single i),
    rootVec_eq_zero (not_isRoot_theta_add i), add_zero]
  exact rootVec_add_self _

theorem heckeT_adj_theta_n8 :
    e8Datum.heckeT (adjRep F) n8 (rootVec .E8 F e8Theta) = rootVec .E8 F e8Theta := by
  rw [heckeT_adj, weylElt_one_rootVec n8 isRoot_theta, reflect_theta_seven,
    xOp_one_rootVec_of_ne n8 isRoot_theta_sub theta_sub_ne_single theta_sub_ne_neg_single,
    theta_sub_add, ← add_assoc, rootVec_add_self, zero_add]

theorem adj_isChevType (χ : adjointGroup .E8 (ZMod 2) → F)
    (hχ : ∀ h ∈ e8Datum.H, χ h = 1) :
    IsChevType .E8 (ZMod 2) 2 exists_weyl_neg_E8 (adjRep F) (rootVec .E8 F e8Theta)
      χ (Finset.univ.erase n8) := by
  refine ⟨rootVec_theta_mem_fixU, rootVec_theta_ne_zero, fun h hh => ?_, fun i => ?_⟩
  · rw [hχ h hh, one_smul, torus_eq_one hh, map_one, Module.End.one_apply]
  · have hχ' : ∀ t : (ZMod 2)ˣ, χ (dC .E8 (ZMod 2) i t) = 1 := fun t => hχ _ (dC_mem_H i t)
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, hχ', implies_true, true_and]
    by_cases hi : i = n8
    · subst hi
      simp only [ne_eq, not_true_eq_false, false_iff]
      change ¬ e8Datum.heckeT (adjRep F) n8 _ = 0
      rw [heckeT_adj_theta_n8]
      exact rootVec_theta_ne_zero
    · simp only [ne_eq, hi, not_false_eq_true, true_iff]
      exact heckeT_adj_theta_of_ne hi

theorem finrank_adjMod : Module.finrank F (AdjMod F) = 248 := by
  rw [Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card, Nat.card_sum, Nat.card_fin,
    Nat.card_eq_fintype_card (α := {v : Fin Tag.E8.rank → ℤ // IsRoot .E8 v}), card_isRoot]
  rfl

end Adj

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc
