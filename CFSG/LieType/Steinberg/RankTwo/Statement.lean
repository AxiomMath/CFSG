module

public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.RankTwo.Reparam

public section

namespace CFSG.LieType.Steinberg.RankTwo

open CFSG.LieType.Steinberg CFSG.LieType.Universal

universe u w

section Generic

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Φ : RootSystem ι} {k : Type*} [Field k]
  {K : Type*} [Group K]

theorem closure_range_eq_top_of_presentationB {x : (ι → ℤ) → k → K}
    (hx : PresentationB (Φ := Φ) x) (O : CommOrder Φ) :
    Subgroup.closure (⋃ γ ∈ Φ.roots, Set.range (x γ)) = ⊤ := by
  obtain ⟨C, -, hC⟩ := (hx O).1
  obtain ⟨h, hbij⟩ := (hx O).2 C hC
  set S := Subgroup.closure (⋃ γ ∈ Φ.roots, Set.range (x γ))
  have key : ∀ w : PresentedGroup (relA Φ k ∪ relB Φ k O C), PresentedGroup.toGroup h w ∈ S := by
    intro w
    have hw : w ∈ Subgroup.closure (Set.range PresentedGroup.of) := by
      rw [PresentedGroup.closure_range_of]
      exact Subgroup.mem_top w
    induction hw using Subgroup.closure_induction with
    | mem _ hg =>
      obtain ⟨g, rfl⟩ := hg
      rw [PresentedGroup.toGroup.of]
      exact Subgroup.subset_closure (Set.mem_biUnion g.1.2 ⟨g.2, rfl⟩)
    | one => rw [map_one]; exact S.one_mem
    | mul _ _ _ _ ha hb => rw [map_mul]; exact S.mul_mem ha hb
    | inv _ _ ha => rw [map_inv]; exact S.inv_mem ha
  exact eq_top_iff.2 fun g _ => by
    obtain ⟨w, rfl⟩ := hbij.2 g
    exact key w

variable (Φ) in
@[expose] def PresentationABC (X : (ι → ℤ) → Subgroup K) (x : (ι → ℤ) → k → K) : Prop :=
  Subgroup.closure (⋃ γ ∈ Φ.roots, (X γ : Set K)) = ⊤ ∧
    (∀ (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ), CommutatorFormula x O C →
      ∀ (H : Type w) [Group H] (y : (ι → ℤ) → k → H),
        (∀ γ ∈ Φ.roots, ∀ c d, y γ (c + d) = y γ c * y γ d) → CommutatorFormula y O C →
        ∃! φ : K →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (x γ c) = y γ c) ∧
    ∀ (η : (ι → ℤ) → kˣ) (O : CommOrder Φ) (C : (ι → ℤ) → (ι → ℤ) → ℕ × ℕ → ℤ),
      CommutatorFormula x O C →
      Subgroup.closure (⋃ γ ∈ Φ.roots, Set.range (reparam x η γ)) = ⊤ ∧
        CommutatorFormulaK (reparam x η) O (reparamConst (fun α β p => (C α β p : k)) η) ∧
        (∃ h : ∀ r ∈ relA Φ k ∪ relBk Φ k O (reparamConst (fun α β p => (C α β p : k)) η),
            FreeGroup.lift (chevEval (reparam x η)) r = 1,
          Function.Bijective (PresentedGroup.toGroup h)) ∧
        ∀ (H : Type w) [Group H] (y : (ι → ℤ) → k → H),
          (∀ γ ∈ Φ.roots, ∀ c d, y γ (c + d) = y γ c * y γ d) →
          CommutatorFormulaK y O (reparamConst (fun α β p => (C α β p : k)) η) →
          ∃! φ : K →* H, ∀ γ ∈ Φ.roots, ∀ c, φ (reparam x η γ c) = y γ c

theorem presentationABC_of {X : (ι → ℤ) → Subgroup K} {x : (ι → ℤ) → k → K}
    (hpar : IsParametrization (Φ := Φ) X x) (hO : Nonempty (CommOrder Φ))
    (hx : PresentationB (Φ := Φ) x) : PresentationABC.{w} Φ X x := by
  obtain ⟨O⟩ := hO
  have hgen := closure_range_eq_top_of_presentationB hx O
  have hX : (⋃ γ ∈ Φ.roots, (X γ : Set K)) = ⋃ γ ∈ Φ.roots, Set.range (x γ) :=
    Set.iUnion₂_congr fun γ hγ => Set.ext fun g => (hpar γ hγ).1 g
  refine ⟨hX ▸ hgen, fun O C hC H _ y hA hB =>
    existsUnique_hom_of_presentationB hx O hC ⟨hA, hB⟩, fun η O C hC =>
      ⟨?_, reparametrization_of_presentationB hx O hC η⟩⟩
  simp_rw [range_reparam]
  exact hgen

end Generic

@[expose] def RankTwoPresentation {K : Type u} [Group K] (D : UniversalRootDatum K) (k : Type)
    [Field k] (x : (Fin D.rank → ℤ) → k → K) : Prop :=
  ConclusionB D k x ∧
    PresentationABC.{w} (RootSystem.ofCartan D.isFiniteType D.divisible) D.rootGroup x

theorem rankTwoPresentation_of_conclusionB {K : Type u} [Group K] {D : UniversalRootDatum K}
    {k : Type} [Field k] {x : (Fin D.rank → ℤ) → k → K} (h : ConclusionB D k x) :
    RankTwoPresentation.{u, w} D k x :=
  ⟨h, presentationABC_of h.1 h.2.1 h.2.2.1⟩

theorem sl3_rankTwoPresentation
    (k : Type) [Field k] [Finite k] :
    RankTwoPresentation.{0, w} (SpecialLinear.rootDatum 2 k) k (SL.x 2 k) :=
  rankTwoPresentation_of_conclusionB (sl_conclusionB 2 k le_rfl)

theorem sp4_rankTwoPresentation
    (k : Type) [Field k] [Finite k] :
    RankTwoPresentation.{0, w} (Symplectic.rootDatum 2 k) k (Sp.x 2 k) :=
  rankTwoPresentation_of_conclusionB (sp_conclusionB 2 k le_rfl)

end CFSG.LieType.Steinberg.RankTwo
