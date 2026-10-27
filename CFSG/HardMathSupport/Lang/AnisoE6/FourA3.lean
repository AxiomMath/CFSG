module

public import CFSG.HardMathSupport.Lang.AnisoE6.ThirdA2
public import CFSG.Adapters.ProjectiveSpecialLinear

public noncomputable section

namespace CFSG.HardMathSupport.Lang.AnisoE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
open scoped Matrix

set_option linter.unusedSectionVars false

@[expose] def wWord4 : List (Fin Tag.E6.rank) :=
  [e6Index 4, e6Index 3, e6Index 2, e6Index 1, e6Index 3, e6Index 4, e6Index 5, e6Index 0,
    e6Index 2, e6Index 3, e6Index 4, e6Index 1]

@[expose] def gammaVec : Fin Tag.E6.rank → ℤ :=
  fun i => (![1, 1, 2, 2, 2, 1] : Fin 6 → ℤ) ⟨i.1, i.2⟩

section Combinatorics4


theorem wWord4_smul_e0 :
    (coxeterSystem Tag.E6).wordProd wWord4 • (Pi.single (e6Index 0) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (e6Index 1) 1 := by
  simp only [wWord4, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil, mul_smul,
    one_smul, simple_smul]
  decide +kernel

theorem wWord4_smul_e2 :
    (coxeterSystem Tag.E6).wordProd wWord4 • (Pi.single (e6Index 2) 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single (e6Index 3) 1 := by
  simp only [wWord4, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil, mul_smul,
    one_smul, simple_smul]
  decide +kernel

theorem wWord4_smul_e3 :
    (coxeterSystem Tag.E6).wordProd wWord4 • (Pi.single (e6Index 3) 1 : Fin Tag.E6.rank → ℤ) =
      gammaVec := by
  simp only [wWord4, CoxeterSystem.wordProd, List.map, List.prod_cons, List.prod_nil, mul_smul,
    one_smul, simple_smul, gammaVec]
  decide +kernel

theorem isRoot_gammaVec : IsRoot Tag.E6 gammaVec := by
  rw [← wWord4_smul_e3]
  exact IsRoot.smul (isRoot_single _ _) _

theorem rootForm_gamma_single (i : Fin Tag.E6.rank) (hi : i = e6Index 0 ∨ i = e6Index 5) :
    (Pi.single (e6Index 1) 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0 ∧
    (Pi.single (e6Index 3) 1 : Fin Tag.E6.rank → ℤ) ⬝ᵥ
        (Tag.E6.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0 ∧
    gammaVec ⬝ᵥ (Tag.E6.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) = 0 := by
  rcases hi with rfl | rfl <;> refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end Combinatorics4

section Commute4


variable (K : Type) [Field K]

theorem commute_conj_gen4 (j : Fin Tag.E6.rank)
    (hj : j = e6Index 0 ∨ j = e6Index 2 ∨ j = e6Index 3)
    (i : Fin Tag.E6.rank) (hi : i = e6Index 0 ∨ i = e6Index 5) (c d : K) :
    Commute (nElt Tag.E6 K wWord4 * xUnit Tag.E6 K j c * (nElt Tag.E6 K wWord4)⁻¹)
      (xUnit Tag.E6 K i d) ∧
    Commute (nElt Tag.E6 K wWord4 * xUnit Tag.E6 K j c * (nElt Tag.E6 K wWord4)⁻¹)
      (yUnit Tag.E6 K i d) ∧
    Commute (nElt Tag.E6 K wWord4 * yUnit Tag.E6 K j c * (nElt Tag.E6 K wWord4)⁻¹)
      (xUnit Tag.E6 K i d) ∧
    Commute (nElt Tag.E6 K wWord4 * yUnit Tag.E6 K j c * (nElt Tag.E6 K wWord4)⁻¹)
      (yUnit Tag.E6 K i d) := by
  obtain ⟨h1, h3, hg⟩ := rootForm_gamma_single i hi
  obtain ⟨ε, -, hx⟩ := exists_prod_weylElt_mul_pinnedX_mul_inv K wWord4 (isRoot_single Tag.E6 j)
  obtain ⟨ε', -, hy⟩ :=
    exists_prod_weylElt_mul_pinnedX_mul_inv K wWord4 (isRoot_neg_single Tag.E6 j)
  have ex : nElt Tag.E6 K wWord4 * xUnit Tag.E6 K j c * (nElt Tag.E6 K wWord4)⁻¹ =
      pinnedX Tag.E6 K ((coxeterSystem Tag.E6).wordProd wWord4 • Pi.single j 1) (ε * c) := by
    rw [← pinnedX_single]
    exact hx c
  have ey : nElt Tag.E6 K wWord4 * yUnit Tag.E6 K j c * (nElt Tag.E6 K wWord4)⁻¹ =
      pinnedX Tag.E6 K (-((coxeterSystem Tag.E6).wordProd wWord4 • Pi.single j 1)) (ε' * c) := by
    rw [← pinnedX_neg_single, ← smul_neg]
    exact hy c
  rcases hj with rfl | rfl | rfl
  · rw [wWord4_smul_e0] at ex ey
    obtain ⟨a1, a2, a3, a4⟩ := commute_xy_of_orth K (isRoot_single Tag.E6 _) i h1 (ε * c) d
    obtain ⟨b1, b2, b3, b4⟩ := commute_xy_of_orth K (isRoot_single Tag.E6 _) i h1 (ε' * c) d
    rw [ex, ey]
    exact ⟨a1, a3, b2, b4⟩
  · rw [wWord4_smul_e2] at ex ey
    obtain ⟨a1, a2, a3, a4⟩ := commute_xy_of_orth K (isRoot_single Tag.E6 _) i h3 (ε * c) d
    obtain ⟨b1, b2, b3, b4⟩ := commute_xy_of_orth K (isRoot_single Tag.E6 _) i h3 (ε' * c) d
    rw [ex, ey]
    exact ⟨a1, a3, b2, b4⟩
  · rw [wWord4_smul_e3] at ex ey
    obtain ⟨a1, a2, a3, a4⟩ := commute_xy_of_orth K isRoot_gammaVec i hg (ε * c) d
    obtain ⟨b1, b2, b3, b4⟩ := commute_xy_of_orth K isRoot_gammaVec i hg (ε' * c) d
    rw [ex, ey]
    exact ⟨a1, a3, b2, b4⟩

theorem commute_conj_support134 {b : ModGL Tag.E6 K}
    (hb : b ∈ subsystemGroup Tag.E6 K support134)
    (i : Fin Tag.E6.rank) (hi : i = e6Index 0 ∨ i = e6Index 5) (d : K) :
    Commute (nElt Tag.E6 K wWord4 * b * (nElt Tag.E6 K wWord4)⁻¹) (xUnit Tag.E6 K i d) ∧
    Commute (nElt Tag.E6 K wWord4 * b * (nElt Tag.E6 K wWord4)⁻¹) (yUnit Tag.E6 K i d) := by
  induction hb using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨j, hj, c, rfl | rfl⟩ := hy
    · have hj' : j = e6Index 0 ∨ j = e6Index 2 ∨ j = e6Index 3 := hj
      obtain ⟨a1, a2, -, -⟩ := commute_conj_gen4 K j hj' i hi c d
      exact ⟨a1, a2⟩
    · have hj' : j = e6Index 0 ∨ j = e6Index 2 ∨ j = e6Index 3 := hj
      obtain ⟨-, -, a3, a4⟩ := commute_conj_gen4 K j hj' i hi c d
      exact ⟨a3, a4⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have e : nElt Tag.E6 K wWord4 * (x * y) * (nElt Tag.E6 K wWord4)⁻¹ =
        (nElt Tag.E6 K wWord4 * x * (nElt Tag.E6 K wWord4)⁻¹) *
          (nElt Tag.E6 K wWord4 * y * (nElt Tag.E6 K wWord4)⁻¹) := by group
    rw [e]
    exact ⟨hx.1.mul_left hy.1, hx.2.mul_left hy.2⟩
  | inv x _ hx =>
    have e : nElt Tag.E6 K wWord4 * x⁻¹ * (nElt Tag.E6 K wWord4)⁻¹ =
        (nElt Tag.E6 K wWord4 * x * (nElt Tag.E6 K wWord4)⁻¹)⁻¹ := by group
    rw [e]
    exact ⟨hx.1.inv_left, hx.2.inv_left⟩

end Commute4

end CFSG.HardMathSupport.Lang.AnisoE6
