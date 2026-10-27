module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families
public import CFSG.LieType.Chevalley.OrthogonalFixedOrbitMaps
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LocalAnalysis.ComponentInitial


theorem rootSL2_mem_closedIdentityComponent_of_commute {tau : Tag} {Ω : Type}
    [Field Ω] [IsAlgClosed Ω] {γ : Fin tau.rank → ℤ}
    (hγ : IsRoot tau γ) {Hh : Set (ModGL tau Ω)}
    (hcomm : ∀ h ∈ Hh, ∀ A, h * rootSL2 tau Ω γ A = rootSL2 tau Ω γ A * h) (A : SL2 Ω) :
    rootSL2 tau Ω γ A ∈ closedIdentityComponent (adjointGroup tau Ω ⊓
      Subgroup.centralizer Hh) := by
  have hZ : ∀ X, rootSL2 tau Ω γ X ∈
      adjointGroup tau Ω ⊓ Subgroup.centralizer Hh := fun X =>
    Subgroup.mem_inf.2 ⟨rootSL2_mem_adjointGroup _ _,
      Subgroup.mem_centralizer_iff.2 fun h hh => hcomm h hh X⟩
  have hU : ∀ t, rootSL2 tau Ω γ (uSL t) ∈ closedIdentityComponent (adjointGroup tau Ω ⊓
      Subgroup.centralizer Hh) := by
    have hcurve : IsPolynomialCurve fun t : Ω => rootSL2 tau Ω γ (uSL t) := by
      have h : (fun t : Ω => rootSL2 tau Ω γ (uSL t)) = fun t =>
          pinnedX tau Ω γ ((Polynomial.C (((pinnedData tau γ).2.2 : ℤ) : Ω) *
            Polynomial.X).eval t) := by
        funext t
        simp only [rootSL2_uSL_eq, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
          zsmul_eq_mul]
      rw [h]
      exact isPolynomialCurve_pinnedX _ _
    intro t
    refine mem_closedIdentityComponent_of_isPolynomialCurve hcurve (fun t => hZ _) (t₀ := 0) ?_ t
    rw [show (uSL (0 : Ω) : SL2 Ω) = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [uSL],
      map_one]
  have hV : ∀ t, rootSL2 tau Ω γ (vSL t) ∈ closedIdentityComponent (adjointGroup tau Ω ⊓
      Subgroup.centralizer Hh) := by
    obtain ⟨ε, -, hε⟩ := exists_rootSL2_vSL_eq (K := Ω) hγ
    have hcurve : IsPolynomialCurve fun t : Ω => rootSL2 tau Ω γ (vSL t) := by
      have h : (fun t : Ω => rootSL2 tau Ω γ (vSL t)) = fun t =>
          pinnedX tau Ω (-γ) ((Polynomial.C ε * Polynomial.X).eval t) := by
        funext t
        simp only [hε, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      rw [h]
      exact isPolynomialCurve_pinnedX _ _
    intro t
    refine mem_closedIdentityComponent_of_isPolynomialCurve hcurve (fun t => hZ _) (t₀ := 0) ?_ t
    rw [show (vSL (0 : Ω) : SL2 Ω) = 1 by ext i j; fin_cases i <;> fin_cases j <;> simp [vSL],
      map_one]
  have hA : A ∈ Subgroup.closure (Set.range (sl2Upper Ω) ∪ Set.range (sl2Lower Ω)) := by
    rw [sl2_closure_upper_lower]
    exact Subgroup.mem_top A
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hU c
    · exact hV c
  | one => rw [map_one]; exact Subgroup.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx


end CFSG.LieType.AlgebraicGroups
