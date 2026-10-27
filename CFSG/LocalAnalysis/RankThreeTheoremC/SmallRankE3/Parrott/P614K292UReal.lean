module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeQuasisimpleSL
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.LThreeEpsLift

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292U

open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut)
open CFSG.ShultStronglyClosedTI.UnitaryAutomorphism
  (unitary_three_full_semilinear_automorphism_realization)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott (eq_of_inv_mul_mem_center)

variable {p f : ℕ} {K : Type} [Field K]

theorem exists_semilinear (hK : PiField false p f K) (h2 : 2 < p ^ f)
    (α : MulAut ↥(slPi false 3 (p ^ f) K)) :
    ∃ A ∈ glPi false 3 (p ^ f) K, ∃ σ : K ≃+* K, ∀ s : ↥(slPi false 3 (p ^ f) K),
      ((α s : ↥(slPi false 3 (p ^ f) K)) : GL (Fin 3) K) =
        A * glAut σ (s : GL (Fin 3) K) * A⁻¹ := by
  have h := hK.unitary
  let α' : MulAut ↥(unitarySU p f K 3) := α
  have hZ : (unitaryScalars h 3).map (α' : ↥(unitarySU p f K 3) →* ↥(unitarySU p f K 3)) =
      unitaryScalars h 3 := by
    rw [← center_unitarySU_three (h := h) h2]
    exact Subgroup.map_center_eq α'
  obtain ⟨σ, A, hA, hβ⟩ := unitary_three_full_semilinear_automorphism_realization h h2
    (QuotientGroup.congr (unitaryScalars h 3) (unitaryScalars h 3) α' hZ)
  refine ⟨A, (mem_glPi_false h).2 hA, σ, fun s => ?_⟩
  haveI : Group.IsPerfect ↥(unitarySU p f K 3) :=
    (Item462AltProof.KSLThree.isQuasisimple_slPi hK h2).1
  let φ : MulAut ↥(unitarySU p f K 3) := suConj h ⟨A, hA⟩ * suField h σ
  have hφ : ∀ g : ↥(unitarySU p f K 3), ((φ g : ↥(unitarySU p f K 3)) : GL (Fin 3) K) =
      A * glAut σ (g : GL (Fin 3) K) * A⁻¹ := fun g => rfl
  have key : ∀ g : ↥(unitarySU p f K 3),
      ((φ : ↥(unitarySU p f K 3) →* ↥(unitarySU p f K 3)) g)⁻¹ *
        (α' : ↥(unitarySU p f K 3) →* ↥(unitarySU p f K 3)) g ∈
          Subgroup.center ↥(unitarySU p f K 3) := by
    intro g
    obtain ⟨hg, hαg⟩ := hβ g
    have e : φ g = ⟨_, hg⟩ := Subtype.ext (hφ g)
    have h1 : ((⟨_, hg⟩ : ↥(unitarySU p f K 3)) : unitaryPSU h 3) =
        ((α' g : ↥(unitarySU p f K 3)) : unitaryPSU h 3) := hαg.symm
    rw [center_unitarySU_three (h := h) h2]
    change (φ g)⁻¹ * α' g ∈ unitaryScalars h 3
    rw [e]
    exact QuotientGroup.eq.1 h1
  exact (congrArg Subtype.val (eq_of_inv_mul_mem_center
    (α' : ↥(unitarySU p f K 3) →* ↥(unitarySU p f K 3))
    (φ : ↥(unitarySU p f K 3) →* ↥(unitarySU p f K 3)) key s)).trans (hφ s)

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614.P614K292U
