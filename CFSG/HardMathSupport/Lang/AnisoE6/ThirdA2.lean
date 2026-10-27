module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.RankThree.E6.RootLatticeTools

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open scoped Matrix

@[expose] def uWord : List (Fin Tag.E6.rank) :=
  [e6Index 4, e6Index 3, e6Index 2, e6Index 1, e6Index 3, e6Index 4, e6Index 0, e6Index 2,
    e6Index 3]

@[expose] def ωFold : List (Fin TwistTag.E6.foldedTag.rank) :=
  [⟨2, by decide⟩, ⟨1, by decide⟩, ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩,
    ⟨3, by decide⟩, ⟨2, by decide⟩, ⟨1, by decide⟩]

@[expose] def ωWord : List (Fin Tag.E6.rank) :=
  (ωFold.map TwistTag.E6.orbitWord).flatten

theorem ωWord_eq : ωWord =
    [e6Index 3, e6Index 2, e6Index 4, e6Index 1, e6Index 3, e6Index 2, e6Index 4, e6Index 0,
      e6Index 5, e6Index 1, e6Index 3, e6Index 2, e6Index 4] := by
  decide +kernel

@[expose] def wWord : List (Fin Tag.E6.rank) := ωWord ++ uWord


variable (τ : Tag) (K : Type) [Field K]

@[expose] def nElt (ω : List (Fin τ.rank)) : ModGL τ K :=
  (ω.map fun i => weylElt τ K i 1).prod

variable {K}

section Combinatorics

@[expose] def beta1 : Fin Tag.E6.rank → ℤ := Pi.single (e6Index 1) 1

@[expose] def beta2 : Fin Tag.E6.rank → ℤ := fun i => (![1, 1, 2, 3, 2, 1] : Fin 6 → ℤ) ⟨i.1, i.2⟩

theorem wWord_smul_e0 :
    (coxeterSystem Tag.E6).wordProd wWord • (Pi.single (e6Index 0) 1 : Fin Tag.E6.rank → ℤ) =
      beta1 := by
  simp only [wWord, ωWord_eq, uWord, CoxeterSystem.wordProd, List.map, List.prod_cons,
    List.prod_nil, List.cons_append, List.nil_append, mul_smul, one_smul, simple_smul, beta1]
  decide +kernel

theorem wWord_smul_e2 :
    (coxeterSystem Tag.E6).wordProd wWord • (Pi.single (e6Index 2) 1 : Fin Tag.E6.rank → ℤ) =
      beta2 := by
  simp only [wWord, ωWord_eq, uWord, CoxeterSystem.wordProd, List.map, List.prod_cons,
    List.prod_nil, List.cons_append, List.nil_append, mul_smul, one_smul, simple_smul, beta2]
  decide +kernel

theorem isRoot_beta1 : IsRoot Tag.E6 beta1 := isRoot_single _ _

theorem isRoot_beta2 : IsRoot Tag.E6 beta2 := by
  rw [← wWord_smul_e2]
  exact IsRoot.smul (isRoot_single _ _) _

theorem rootForm_beta_single (i : Fin Tag.E6.rank)
    (hi : i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5) :
    beta1 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0 ∧
      beta2 ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0 := by
  rcases hi with rfl | rfl | rfl | rfl <;> constructor <;> decide +kernel

end Combinatorics

section Commute


variable (K)

theorem commute_pinnedX_E6 {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β) (h0 : α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ β) = 0) (c d : K) :
    Commute (pinnedX Tag.E6 K α c) (pinnedX Tag.E6 K β d) :=
  commute_pinnedX_of_rootForm_eq_zero (t := TwistTag.E6) K hα hβ h0 c d

theorem commute_pinnedX_signs {α β : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hβ : IsRoot Tag.E6 β)
    (h0 : α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ β) = 0) (c d : K) :
    Commute (pinnedX Tag.E6 K α c) (pinnedX Tag.E6 K β d) ∧
    Commute (pinnedX Tag.E6 K (-α) c) (pinnedX Tag.E6 K β d) ∧
    Commute (pinnedX Tag.E6 K α c) (pinnedX Tag.E6 K (-β) d) ∧
    Commute (pinnedX Tag.E6 K (-α) c) (pinnedX Tag.E6 K (-β) d) := by
  have hαn : IsRoot Tag.E6 (-α) := CFSG.LieType.Chevalley.IsRoot.neg hα
  have hβn : IsRoot Tag.E6 (-β) := CFSG.LieType.Chevalley.IsRoot.neg hβ
  refine ⟨commute_pinnedX_E6 K hα hβ h0 c d, commute_pinnedX_E6 K hαn hβ ?_ c d,
    commute_pinnedX_E6 K hα hβn ?_ c d, commute_pinnedX_E6 K hαn hβn ?_ c d⟩
  · rw [neg_dotProduct, h0, neg_zero]
  · rw [Matrix.mulVec_neg, dotProduct_neg, h0, neg_zero]
  · rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, h0, neg_neg]

theorem commute_xy_of_orth {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (i : Fin Tag.E6.rank)
    (h0 : α ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0)
    (c d : K) :
    Commute (pinnedX Tag.E6 K α c) (xUnit Tag.E6 K i d) ∧
    Commute (pinnedX Tag.E6 K (-α) c) (xUnit Tag.E6 K i d) ∧
    Commute (pinnedX Tag.E6 K α c) (yUnit Tag.E6 K i d) ∧
    Commute (pinnedX Tag.E6 K (-α) c) (yUnit Tag.E6 K i d) := by
  obtain ⟨h1, h2, h3, h4⟩ := commute_pinnedX_signs K hα (isRoot_single Tag.E6 i) h0 c d
  rw [pinnedX_single] at h1 h2
  rw [pinnedX_neg_single] at h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem commute_conj_gen (j : Fin Tag.E6.rank) (hj : j = e6Index 0 ∨ j = e6Index 2)
    (i : Fin Tag.E6.rank) (hi : i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5)
    (c d : K) :
    Commute (nElt Tag.E6 K wWord * xUnit Tag.E6 K j c * (nElt Tag.E6 K wWord)⁻¹) (xUnit Tag.E6 K i d) ∧
    Commute (nElt Tag.E6 K wWord * xUnit Tag.E6 K j c * (nElt Tag.E6 K wWord)⁻¹) (yUnit Tag.E6 K i d) ∧
    Commute (nElt Tag.E6 K wWord * yUnit Tag.E6 K j c * (nElt Tag.E6 K wWord)⁻¹) (xUnit Tag.E6 K i d) ∧
    Commute (nElt Tag.E6 K wWord * yUnit Tag.E6 K j c * (nElt Tag.E6 K wWord)⁻¹) (yUnit Tag.E6 K i d) := by
  obtain ⟨hb1, hb2⟩ := rootForm_beta_single i hi
  obtain ⟨ε, -, hx⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K wWord (isRoot_single Tag.E6 j)
  obtain ⟨ε', -, hy⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K wWord (isRoot_neg_single Tag.E6 j)
  have ex : nElt Tag.E6 K wWord * xUnit Tag.E6 K j c * (nElt Tag.E6 K wWord)⁻¹ =
      pinnedX Tag.E6 K ((coxeterSystem Tag.E6).wordProd wWord • Pi.single j 1) (ε * c) := by
    rw [← pinnedX_single]
    exact hx c
  have ey : nElt Tag.E6 K wWord * yUnit Tag.E6 K j c * (nElt Tag.E6 K wWord)⁻¹ =
      pinnedX Tag.E6 K (-((coxeterSystem Tag.E6).wordProd wWord • Pi.single j 1)) (ε' * c) := by
    rw [← pinnedX_neg_single, ← smul_neg]
    exact hy c
  rcases hj with rfl | rfl
  · rw [wWord_smul_e0] at ex ey
    obtain ⟨a1, a2, a3, a4⟩ := commute_xy_of_orth K isRoot_beta1 i hb1 (ε * c) d
    obtain ⟨b1, b2, b3, b4⟩ := commute_xy_of_orth K isRoot_beta1 i hb1 (ε' * c) d
    rw [ex, ey]
    exact ⟨a1, a3, b2, b4⟩
  · rw [wWord_smul_e2] at ex ey
    obtain ⟨a1, a2, a3, a4⟩ := commute_xy_of_orth K isRoot_beta2 i hb2 (ε * c) d
    obtain ⟨b1, b2, b3, b4⟩ := commute_xy_of_orth K isRoot_beta2 i hb2 (ε' * c) d
    rw [ex, ey]
    exact ⟨a1, a3, b2, b4⟩

theorem commute_conj_support13 {b : ModGL Tag.E6 K}
    (hb : b ∈ subsystemGroup Tag.E6 K support13)
    (i : Fin Tag.E6.rank) (hi : i = e6Index 0 ∨ i = e6Index 2 ∨ i = e6Index 4 ∨ i = e6Index 5)
    (d : K) :
    Commute (nElt Tag.E6 K wWord * b * (nElt Tag.E6 K wWord)⁻¹) (xUnit Tag.E6 K i d) ∧
    Commute (nElt Tag.E6 K wWord * b * (nElt Tag.E6 K wWord)⁻¹) (yUnit Tag.E6 K i d) := by
  induction hb using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hy
    · have hj' : j = e6Index 0 ∨ j = e6Index 2 := hj
      obtain ⟨a1, a2, -, -⟩ := commute_conj_gen K j hj' i hi c d
      exact ⟨a1, a2⟩
    · have hj' : j = e6Index 0 ∨ j = e6Index 2 := hj
      obtain ⟨-, -, a3, a4⟩ := commute_conj_gen K j hj' i hi c d
      exact ⟨a3, a4⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have e : nElt Tag.E6 K wWord * (x * y) * (nElt Tag.E6 K wWord)⁻¹ =
        (nElt Tag.E6 K wWord * x * (nElt Tag.E6 K wWord)⁻¹) * (nElt Tag.E6 K wWord * y * (nElt Tag.E6 K wWord)⁻¹) := by group
    rw [e]
    exact ⟨hx.1.mul_left hy.1, hx.2.mul_left hy.2⟩
  | inv x _ hx =>
    have e : nElt Tag.E6 K wWord * x⁻¹ * (nElt Tag.E6 K wWord)⁻¹ = (nElt Tag.E6 K wWord * x * (nElt Tag.E6 K wWord)⁻¹)⁻¹ := by
      group
    rw [e]
    exact ⟨hx.1.inv_left, hx.2.inv_left⟩

end Commute

end CFSG.HardMathSupport.Lang.AnisoE6
