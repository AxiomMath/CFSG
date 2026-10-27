module

public import CFSG.RankThree.PartOne.S11c.G2Torus
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcRDDefs
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcToralityFive
public import CFSG.HardMathSupport.Timmesfeld.RootAut.Linear

public section

namespace CFSG.HardMathSupport.Dickson.Sec6

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Solomon.UniquenessMaximal CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.RootAut
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple CFSG.RankThree.PartOne
  CFSG.RankThree.Chevalley

namespace Up34Exc

section Linear

variable {τ : Tag}

theorem iform_eq_sum_single (β v : Fin τ.rank → ℤ) :
    iform β v = ∑ j, v j * iform β (Pi.single j 1) := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem corootPair_sum {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (v : Fin τ.rank → ℤ) :
    corootPair γ v = ∑ j, v j * corootPair γ (Pi.single j 1) := by
  have hpos := iform_self_pos_of_isRoot hγ
  refine mul_right_cancel₀ hpos.ne' ?_
  rw [corootPair_mul hγ, Finset.sum_mul]
  simp_rw [mul_assoc, corootPair_mul hγ]
  rw [iform_eq_sum_single γ v, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

end Linear

section Z0

set_option linter.unusedSectionVars false

variable {τ : Tag} {K : Type} [Field K]

@[expose] noncomputable def z0 (τ : Tag) {K : Type} [Field K] (γ₁ γ₂ : Fin τ.rank → ℤ)
    (ω : Kˣ) : ModGL τ K :=
  rootDiagUnit τ (fun j => ω ^ a2Exp τ γ₁ γ₂ j)

theorem z0_eq_rootSL2 {γ₁ γ₂ : Fin τ.rank → ℤ} (hP : IsA2Pair τ γ₁ γ₂) (ω : Kˣ) :
    z0 τ γ₁ γ₂ ω = rootSL2 τ K γ₁ (HSL ω) * rootSL2 τ K γ₂ (HSL (ω ^ 2)) := by
  rw [rootSL2_HSL_eq_rootDiagUnit hP.1 (fun i => cop τ γ₁ (Pi.single i 1))
      (fun δ _ => corootPair_sum hP.1 δ) ω,
    rootSL2_HSL_eq_rootDiagUnit hP.2.1 (fun i => cop τ γ₂ (Pi.single i 1))
      (fun δ _ => corootPair_sum hP.2.1 δ) (ω ^ 2), ← rootDiagUnit_mul, z0]
  congr 1
  funext j
  simp only [a2Exp, Pi.mul_apply]
  rw [← zpow_natCast, ← zpow_mul, ← zpow_add]
  congr 1

theorem z0_mem_rootSpan {γ₁ γ₂ : Fin τ.rank → ℤ} (hP : IsA2Pair τ γ₁ γ₂)
    {S : Set (Fin τ.rank → ℤ)} (h1 : γ₁ ∈ S) (h2 : γ₂ ∈ S) (hn1 : -γ₁ ∈ S) (hn2 : -γ₂ ∈ S)
    (ω : Kˣ) : z0 τ γ₁ γ₂ ω ∈ rootSpan τ K S := by
  have hrange : ∀ {γ : Fin τ.rank → ℤ}, IsRoot τ γ → γ ∈ S → -γ ∈ S → ∀ A : SL2 K,
      rootSL2 τ K γ A ∈ rootSpan τ K S := by
    intro γ hγ hγS hnγS A
    have : rootSL2 τ K γ A ∈ (rootSL2 τ K γ).range := ⟨A, rfl⟩
    rw [range_rootSL2_of_isRoot hγ] at this
    exact (sup_le (rootSubgroup_le_rootSpan hγS) (rootSubgroup_le_rootSpan hnγS)) this
  rw [z0_eq_rootSL2 hP]
  exact mul_mem (hrange hP.1 h1 hn1 _) (hrange hP.2.1 h2 hn2 _)

end Z0

end Up34Exc

end CFSG.HardMathSupport.Dickson.Sec6
