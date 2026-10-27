module

public import CFSG.LieType.SpecialLinear.BinaryDescent.ImageAlgebra
public import CFSG.LieType.SpecialLinear.BinaryDescent.Basic

public section

namespace CFSG.LieType.SpecialLinear

open Matrix
open ExteriorModel

variable {n i j : ℕ} {F : Type*} [Field F] [CharP F 2]

theorem isIrreducibleAdd_of_addSubgroup_closure_eq_top {K I F : Type*} [Fintype I] [Field F]
    (T : K → Matrix I I F) (hT : AddSubgroup.closure (Set.range T) = ⊤) :
    @IsIrreducibleAdd K (I → F) _ (fun (g : K) (v : I → F) => T g *ᵥ v) := by
  classical
  intro W hW
  have hstable : ∀ M : Matrix I I F, M ∈ AddSubgroup.closure (Set.range T) →
      ∀ v ∈ W, M *ᵥ v ∈ W := by
    intro M hM
    induction hM using AddSubgroup.closure_induction with
    | mem M hM =>
        obtain ⟨g, rfl⟩ := hM
        intro v hv
        exact hW g hv
    | zero => intro v _; simp
    | add M N _ _ ihM ihN =>
        intro v hv; rw [add_mulVec]; exact W.add_mem (ihM v hv) (ihN v hv)
    | neg M _ ih =>
        intro v hv; rw [neg_mulVec]; exact W.neg_mem (ih v hv)
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    have hne : ∃ v ∈ W, v ≠ 0 := by
      by_contra h
      apply hbot
      rw [AddSubgroup.eq_bot_iff_forall]
      intro v hv
      by_contra hv0
      exact h ⟨v, hv, hv0⟩
    obtain ⟨v, hvW, hv0⟩ := hne
    have hne_coord : ∃ s : I, v s ≠ 0 := by
      by_contra h
      apply hv0
      funext s
      by_contra hs
      exact h ⟨s, hs⟩
    obtain ⟨s, hs⟩ := hne_coord
    have hscalar : ∀ (c : F) (x : I → F), x ∈ W → c • x ∈ W := by
      intro c x hx
      have hmat : c • (1 : Matrix I I F) ∈ AddSubgroup.closure (Set.range T) := by
        rw [hT]; trivial
      have h := hstable _ hmat x hx
      rwa [Matrix.smul_mulVec, Matrix.one_mulVec] at h
    have hsingle : ∀ t : I, Pi.single t (1 : F) ∈ W := by
      intro t
      have hmat : Matrix.single t s (1 : F) ∈ AddSubgroup.closure (Set.range T) := by
        rw [hT]; trivial
      have h1 := hstable _ hmat v hvW
      rw [Matrix.single_mulVec_eq] at h1
      have h2 := hscalar ((v s)⁻¹) _ h1
      have h3 : ((v s)⁻¹ : F) • ((1 * v s) • Pi.single t (1 : F)) =
          Pi.single t (1 : F) := by
        rw [one_mul, smul_smul, inv_mul_cancel₀ hs, one_smul]
      rwa [h3] at h2
    refine le_antisymm le_top ?_
    intro x _
    rw [pi_eq_sum_univ' x]
    exact W.sum_mem (fun t _ => hscalar (x t) _ (hsingle t))

theorem isIrreducibleAdd_extTwist [Fintype F] (hi : 1 ≤ i) (hin : i < n) :
    @IsIrreducibleAdd (Matrix.SpecialLinearGroup (Fin n) F)
      (Set.powersetCard (Fin n) i → F) _
      (fun (g : Matrix.SpecialLinearGroup (Fin n) F)
        (v : Set.powersetCard (Fin n) i → F) => extTwist n i j F g *ᵥ v) :=
  isIrreducibleAdd_of_addSubgroup_closure_eq_top (extTwist n i j F)
    (addSubgroup_closure_range_extTwist_eq_top hi hin)

end CFSG.LieType.SpecialLinear
