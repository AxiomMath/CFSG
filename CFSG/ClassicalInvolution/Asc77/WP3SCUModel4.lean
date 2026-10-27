module

public import CFSG.ClassicalInvolution.Asc77.WP3SCUM4L
public import CFSG.ClassicalInvolution.Asc77.WP3SCUBGL
public import CFSG.ClassicalInvolution.Balance.StrongPowDiagDefs

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Balance.StrongBalance CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBHigherLinearAction
open scoped MatrixGroups

section Defs

@[expose] def PairToral (t : StatedLieTag) (n p e : ℕ) (hp : p.Prime) {H : Type} [Group H]
    (ψ : (modelUniv t n p e hp).K →* H) (a v : H) : Prop :=
  ∀ F₀ : Subgroup H, F₀ ≤ Subgroup.closure ({a, v} ∪ (Subgroup.center H : Set H)) →
    ToralActionDiag 2 t n p e hp ψ F₀

@[expose] def RankFourFacts (t : StatedLieTag) (n p e : ℕ) [Fact p.Prime] : Prop :=
  n = 4 → BlockGeom4 (fundamentalSubgroups t (modelUniv t n p e Fact.out).D) ∧
    ∀ {H : Type} [Group H] (ψ : (modelUniv t n p e Fact.out).K →* H),
      ψ.ker ≤ Subgroup.center (modelUniv t n p e Fact.out).K →
      ∀ {R : Subgroup (modelUniv t n p e Fact.out).K},
        R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D →
        ∀ {v : H}, v ∈ Subgroup.normalizer (ψ.range : Set H) → v * v = 1 →
        (∀ r ∈ R, v * ψ r = ψ r * v) →
        (∃ R'' ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D,
          (∀ r ∈ R, ∀ s ∈ R'', r * s = s * r) ∧ ∀ s ∈ R'', v * ψ s = ψ s * v) ∨
        ∀ x ∈ R, (∀ r ∈ R, x * r = r * x) → PairToral t n p e Fact.out ψ (ψ x) v

end Defs

section PSL

variable {p e : ℕ} [Fact p.Prime]

theorem pairToral_psl_of_diag {H : Type} [Group H] (ψ : SL(4, GaloisField p e) →* H)
    {R : Subgroup SL(4, GaloisField p e)}
    (hR : R ∈ longRootSet (K := GaloisField p e) (show 2 ≤ 4 by norm_num))
    {x : SL(4, GaloisField p e)} (hxR : x ∈ R) (hxc : ∀ r ∈ R, x * r = r * x)
    {v : H} (Y₀ : GL (Fin 4) (GaloisField p e)) (hY2 : Y₀ * Y₀ = 1)
    (hYx : Matrix.SpecialLinearGroup.toGL x * Y₀ = Y₀ * Matrix.SpecialLinearGroup.toGL x)
    (hact : ∀ y : SL(4, GaloisField p e), v * ψ y * v⁻¹ = ψ (slConjugation 4 _ Y₀ y)) :
    PairToral .PSL 4 p e Fact.out ψ (ψ x) v := by
  intro F₀ hF₀
  have hx2 : x * x = 1 :=
    CFSG.ClassicalInvolution.ModelFacts.mul_self_eq_one_of_mem_center_longRootSet hR hxR hxc
  set X₀ : GL (Fin 4) (GaloisField p e) := Matrix.SpecialLinearGroup.toGL x with hX₀
  have hX2 : X₀ * X₀ = 1 := by rw [hX₀, ← map_mul, hx2, map_one]
  have hXY : Commute X₀ Y₀ := hYx
  have hcx : ∀ y : SL(4, GaloisField p e),
      ψ x * ψ y * (ψ x)⁻¹ = ψ (slConjugation 4 _ X₀ y) := by
    intro y
    have : slConjugation 4 (GaloisField p e) X₀ y = x * y * x⁻¹ := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [toGL_slConjugation]
      simp [hX₀]
    rw [this, map_mul, map_mul, map_inv]
  let P : Subgroup (GL (Fin 4) (GaloisField p e)) := Subgroup.closure ({X₀, Y₀} : Set _)
  have hP : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    refine ChainFrame.commutes_closure ?_
    intro a ha b hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hXY.eq
    · exact hXY.eq.symm
    · rfl
  have hXm : X₀ ∈ P := Subgroup.subset_closure (by simp)
  have hYm : Y₀ ∈ P := Subgroup.subset_closure (by simp)
  let Good : Subgroup H :=
    { carrier := {f | ∃ x ∈ P, x * x = 1 ∧ ∀ y : SL(4, GaloisField p e),
        f * ψ y * f⁻¹ = ψ (slConjugation 4 _ x y)}
      one_mem' := ⟨1, P.one_mem, by simp, fun y => by simp⟩
      mul_mem' := by
        rintro f₁ f₂ ⟨x₁, hx₁, hx₁2, h₁⟩ ⟨x₂, hx₂, hx₂2, h₂⟩
        refine ⟨x₁ * x₂, P.mul_mem hx₁ hx₂, ?_, fun y => ?_⟩
        · calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
            _ = x₁ * (x₁ * x₂) * x₂ := by rw [hP x₂ hx₂ x₁ hx₁]
            _ = (x₁ * x₁) * (x₂ * x₂) := by group
            _ = 1 := by rw [hx₁2, hx₂2, one_mul]
        · calc f₁ * f₂ * ψ y * (f₁ * f₂)⁻¹ = f₁ * (f₂ * ψ y * f₂⁻¹) * f₁⁻¹ := by group
            _ = ψ (slConjugation 4 _ (x₁ * x₂) y) := by
                rw [h₂, h₁, map_mul, MulAut.mul_apply]
      inv_mem' := by
        rintro f ⟨x, hx, hx2, h⟩
        refine ⟨x⁻¹, P.inv_mem hx, ?_, fun y => ?_⟩
        · calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
            _ = 1 := by rw [hx2]; group
        · have h1 := h (slConjugation 4 _ x⁻¹ y)
          have e1 : slConjugation 4 (GaloisField p e) x (slConjugation 4 _ x⁻¹ y) = y := by
            rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
          rw [e1] at h1
          calc f⁻¹ * ψ y * f⁻¹⁻¹ = f⁻¹ * (f * ψ (slConjugation 4 _ x⁻¹ y) * f⁻¹) * f⁻¹⁻¹ := by
                rw [← h1]
            _ = ψ (slConjugation 4 _ x⁻¹ y) := by group }
  have hgood : F₀ ≤ Good := by
    refine hF₀.trans ((Subgroup.closure_le Good).mpr ?_)
    intro f hf
    rcases hf with hf | hf
    · rcases hf with rfl | rfl
      · exact ⟨X₀, hXm, hX2, fun y => hcx y⟩
      · exact ⟨Y₀, hYm, hY2, fun y => hact y⟩
    · have hcc := Subgroup.mem_center_iff.mp hf
      refine ⟨1, P.one_mem, by simp, fun y => ?_⟩
      rw [map_one, MulAut.one_apply]
      calc f * ψ y * f⁻¹ = (ψ y * f) * f⁻¹ := by rw [← hcc (ψ y)]
        _ = ψ y := by group
  unfold ToralActionDiag
  refine ⟨fun _ => ⟨MulEquiv.refl _, P, hP, fun f hf => ?_⟩, (fun h => by cases h),
    (fun h => by cases h), (fun h => by cases h), (fun h => by cases h), (fun h => by cases h),
    (fun h => absurd rfl h)⟩
  obtain ⟨x', hx', hx'2, hx'a⟩ := hgood hf
  exact ⟨x', hx', by rw [pow_two]; exact hx'2, hx'a⟩

theorem rankFourFacts_psl (n : ℕ) (hp2 : p ≠ 2) (h5 : 5 ≤ p ^ e) : RankFourFacts .PSL n p e := by
  intro hn
  subst hn
  have he : e ≠ 0 := by
    rintro rfl
    simp at h5
  have hcard : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [hcard]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h5' : 5 ≤ Nat.card (GaloisField p e) := by rw [hcard]; exact h5
  have hcl : CFSG.ClassicalInvolution.RouteD.Gaps.LinearAutClassification (GaloisField p e)
      (3 + 1) :=
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification hp2 h5 (by norm_num)
  have heq : fundamentalSubgroups .PSL (modelUniv .PSL 4 p e Fact.out).D =
      longRootSet (K := GaloisField p e) (show 2 ≤ 4 by norm_num) :=
    Set.Subset.antisymm
      (CFSG.ClassicalInvolution.RouteD.fundamentalSubgroups_psl_subset (m := 3) (by norm_num))
      (CFSG.ClassicalInvolution.RouteD.longRootSet_subset_fundamentalSubgroups_psl (m := 3)
        (by norm_num))
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact blockGeom4_longRootSet hodd h5'
  · intro H _ ψ hker R hR v hv hv2 hvR
    have hRl : R ∈ longRootSet (K := GaloisField p e) (show 2 ≤ 3 + 1 by norm_num) :=
      (Set.ext_iff.mp heq R).mp hR
    rcases psl4_dichotomy hodd h5' hcl ψ hker hRl hv hv2 hvR with ⟨R'', hR''l, hc, hv''⟩ |
        ⟨Y₀, hY2, hYR, hact⟩
    · exact Or.inl ⟨R'', (Set.ext_iff.mp heq R'').mpr hR''l, hc, hv''⟩
    · exact Or.inr fun x hxR hxc =>
        pairToral_psl_of_diag ψ hRl hxR hxc Y₀ hY2 (hYR x hxR) hact

end PSL

end CFSG.ClassicalInvolution.Asc77
