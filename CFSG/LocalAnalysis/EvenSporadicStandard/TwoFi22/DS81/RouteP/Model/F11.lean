module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Cocode
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.F11

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem E0_le_B0 :
    E0 ≤ B0 := by
  intro g hg
  have h0 : g • x0 = x0 := by simpa [planePt_zero] using E0_smul_planePt hg 0
  have h1 : g • x1 = x1 := by simpa [planePt_one] using E0_smul_planePt hg 1
  refine Subgroup.mem_inf.2 ⟨mem_L0_iff.2 ⟨?_, h1⟩, E0_le_Zq hg⟩
  rw [Zp_eq_stabilizer]
  exact MulAction.mem_stabilizer_iff.2 h0

@[expose] noncomputable def t0 :
    Q3 :=
  (((e0.symm (cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1))) : ↥E0q) : ↥Zq) : Q3)

theorem t0_mem_E0 :
    t0 ∈ E0 :=
  (e0.symm (cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1)))).2

theorem tauM24_zero_ne_one : tauM24 0 ≠ tauM24 1 := by
  rw [tauM24_zero, tauM24_one]
  decide

theorem t0_ne_one :
    t0 ≠ 1 := by
  intro h
  have h1 : e0.symm (cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1))) = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have h2 : cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1)) = 1 := by
    have := congrArg e0 h1
    rwa [MulEquiv.apply_symm_apply, MulEquiv.map_one] at this
  exact kappa_pairVec_ne_one tauM24_zero_ne_one h2

theorem eq_of_mem_E0_of_commute_B0
    {y : Q3} (hy : y ∈ E0) (hc : ∀ b ∈ B0, b * y = y * b) : y = 1 ∨ y = t0 := by
  let x : ↥E0q := ⟨⟨y, E0_le_Zq hy⟩, hy⟩
  have hx : ∀ b ∈ cocodeExtension_Zq.Bduad (tauM24 0) (tauM24 1),
      b * (x : ↥Zq) = (x : ↥Zq) * b := by
    intro b hb
    exact Subtype.ext (hc b ((mem_B0_iff_mem_Bduad b).2 hb))
  rcases CocodeExtension.eq_of_mem_centralizer_Bduad cocodeExtension_Zq
    tauM24_zero_ne_one hx with h | h
  · left
    have hx1 : x = 1 := e0.injective (by rw [h, map_one])
    exact congrArg (fun z : ↥E0q => ((z : ↥Zq) : Q3)) hx1
  · right
    have hx1 : x = e0.symm (cocodeCoords.κ (pairVec (tauM24 0) (tauM24 1))) := by
      rw [← h, MulEquiv.symm_apply_apply]
    exact congrArg (fun z : ↥E0q => ((z : ↥Zq) : Q3)) hx1

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
