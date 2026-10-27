module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Frame
public import CFSG.RankThree.Classical2.SLnRootPermutingFixedGroups

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiFin

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K] [Finite K] {w : WeylGroup τ} (D : LangLevi τ K w)

@[expose] def Cl (M : IntermediateField K D.L) : Subgroup (ModGL τ D.L) :=
  Subgroup.closure {u | ∃ (i : Fin τ.rank) (c : ↥M),
    u = xUnit τ D.L i (M.val c) ∨ u = yUnit τ D.L i (M.val c)}

theorem Cl_mono {M M' : IntermediateField K D.L} (h : M ≤ M') : Cl D M ≤ Cl D M' := by
  refine Subgroup.closure_mono ?_
  rintro u ⟨i, c, hu⟩
  exact ⟨i, ⟨c.1, h c.2⟩, hu⟩

theorem algebraic : Algebra.IsIntegral K D.L :=
  (IsAlgClosure.isAlgebraic (R := K) (K := D.L)).isIntegral

theorem exists_Cl {g : ModGL τ D.L} (hg : g ∈ adjointGroup τ D.L) :
    ∃ M : IntermediateField K D.L, FiniteDimensional K M ∧ g ∈ Cl D M := by
  haveI := algebraic D
  unfold adjointGroup at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, c, h | h⟩ := hx
    · have hx : x = xUnit τ D.L i c := Units.ext h
      subst hx
      refine ⟨IntermediateField.adjoin K {c}, ?_, Subgroup.subset_closure
        ⟨i, ⟨c, IntermediateField.subset_adjoin K {c} rfl⟩, Or.inl rfl⟩⟩
      exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
    · have hx : x = yUnit τ D.L i c := Units.ext h
      subst hx
      refine ⟨IntermediateField.adjoin K {c}, ?_, Subgroup.subset_closure
        ⟨i, ⟨c, IntermediateField.subset_adjoin K {c} rfl⟩, Or.inr rfl⟩⟩
      exact IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  | one => exact ⟨⊥, inferInstance, one_mem _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨M₁, h₁, hx⟩ := hx
    obtain ⟨M₂, h₂, hy⟩ := hy
    exact ⟨M₁ ⊔ M₂, IntermediateField.finiteDimensional_sup M₁ M₂,
      mul_mem (Cl_mono D le_sup_left hx) (Cl_mono D le_sup_right hy)⟩
  | inv x _ hx =>
    obtain ⟨M, h, hx⟩ := hx
    exact ⟨M, h, inv_mem hx⟩

theorem exists_finite_subfield (A B : SL(3, D.L)) {g : ModGL τ D.L} (hg : g ∈ adjointGroup τ D.L) :
    ∃ M : IntermediateField K D.L, FiniteDimensional K M ∧
      (∃ A₀ B₀ : SL(3, ↥M), Matrix.SpecialLinearGroup.map (M.val : ↥M →+* D.L) A₀ = A ∧
        Matrix.SpecialLinearGroup.map (M.val : ↥M →+* D.L) B₀ = B) ∧
      ∃ g₀ ∈ adjointGroup τ ↥M, baseChangeGL (M.val : ↥M →+* D.L) g₀ = g := by
  classical
  haveI := algebraic D
  obtain ⟨M₂, h₂, hg₂⟩ := exists_Cl D hg
  let S : Set D.L :=
    Set.range (fun p : Fin 3 × Fin 3 => (A : Matrix (Fin 3) (Fin 3) D.L) p.1 p.2) ∪
      Set.range (fun p : Fin 3 × Fin 3 => (B : Matrix (Fin 3) (Fin 3) D.L) p.1 p.2)
  haveI : Finite S := (Set.Finite.union (Set.finite_range _) (Set.finite_range _)).to_subtype
  have h₁ : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  set M : IntermediateField K D.L := IntermediateField.adjoin K S ⊔ M₂ with hM
  have hle1 : IntermediateField.adjoin K S ≤ M := le_sup_left
  have hle2 : M₂ ≤ M := le_sup_right
  have hS : ∀ x ∈ S, x ∈ M := fun x hx => hle1 (IntermediateField.subset_adjoin K S hx)
  have hinj : Function.Injective (M.val : ↥M →+* D.L) := M.val.injective
  obtain ⟨A₀, hA₀⟩ := CFSG.RankThree.Classical2.exists_map_eq_of_forall_mem_range hinj A
    fun i j => ⟨⟨_, hS _ (Or.inl ⟨(i, j), rfl⟩)⟩, rfl⟩
  obtain ⟨B₀, hB₀⟩ := CFSG.RankThree.Classical2.exists_map_eq_of_forall_mem_range hinj B
    fun i j => ⟨⟨_, hS _ (Or.inr ⟨(i, j), rfl⟩)⟩, rfl⟩
  have hmem : g ∈ (adjointGroup τ ↥M).map (baseChangeGL (M.val : ↥M →+* D.L)) := by
    rw [map_baseChangeGL_adjointGroup]
    exact Cl_mono D hle2 hg₂
  obtain ⟨g₀, hg₀, hg₀e⟩ := hmem
  exact ⟨M, IntermediateField.finiteDimensional_sup _ _, ⟨A₀, B₀, hA₀, hB₀⟩, g₀, hg₀, hg₀e⟩

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.QuasiFin
