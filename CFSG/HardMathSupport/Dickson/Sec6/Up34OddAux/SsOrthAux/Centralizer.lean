module

public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsOrthAux.Blocks
public import CFSG.HardMathSupport.Dickson.Sec6.Up34OddAux.SsOrthAux.Comp

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.SsOrth

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
open CFSG.ComponentClassification.CatLeafProof (OddLieCentralQuotient
  oddLieCentralQuotient_of_mulEquiv)

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V} {ℓ f : ℕ}

theorem normal_supportedBlock_subgroupOf (h : K[X]) :
    ((supportedBlock Q x h).subgroupOf (isometryCentralizer Q x)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (supportedBlock_le_isometryCentralizer h)]
  intro f g hf hg
  have hgc : g ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := (Subgroup.mem_inf.mp hg).2
  refine mem_supportedBlock.mpr ⟨mul_mem (mul_mem hg
    (supportedBlock_le_isometryCentralizer h hf)) (inv_mem hg), fun r hr => ?_⟩
  have hr' : g⁻¹ r ∈ othersSpace x.toLinearMap h := mem_othersSpace_of_apply (inv_mem hgc) hr
  show g (f (g⁻¹ r)) = r
  rw [(mem_supportedBlock.mp hf).2 _ hr']
  exact g.apply_symm_apply r

theorem oddLie_isometryCentralizer (hx : OddOrderIsometry Q p x) (hp2 : Odd p) (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) {L : Subgroup (V ≃ₗ[K] V)}
    (hLM : L ≤ isometryCentralizer Q x)
    (hL : CFSG.IsComponent (L.subgroupOf (isometryCentralizer Q x))) :
    OddLieCentralQuotient ℓ ↥L := by
  classical
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨r, hr⟩ := exists_le_of_isComponent_of_normal_iSup
    (fun r : ↥Rep => supportedBlock Q x r) (fun r => supportedBlock_le_isometryCentralizer _)
    (fun r => normal_supportedBlock_subgroupOf _) (hx.blocks_iSup_eq hRep) hLM hL
  have hBM : supportedBlock Q x r ≤ isometryCentralizer Q x :=
    supportedBlock_le_isometryCentralizer _
  have hLcM : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q x) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLM).2 hL
  have hLcB : CFSG.IsComponent (L.subgroupOf (supportedBlock Q x r)) :=
    (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hr).1
      (hLcM.of_le_of_le hr hBM)
  exact oddLieCentralQuotient_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hr).symm
    (oddLie_supportedBlock hx hp2 hℓ hℓ2 hf hK (hRep.1 r.2) hLcB)

end CFSG.HardMathSupport.Dickson.Sec6.SsOrth
