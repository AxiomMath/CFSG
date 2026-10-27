module

public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRankCover
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
import CFSG.RankThree.PartTwo.Census.Carrier.SpinDBridge
import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank

open Matrix CFSG.Assembly.RankThreeEven CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4

private def permLs₁ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![0, 0, 0, 0, 1, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1]) (by decide +kernel)

private def permLs₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![0, 0, 0, 0, 0, 0, 0, 1;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       1, 0, 0, 0, 0, 0, 0, 0]) (by decide +kernel)

private def permRs₂ : GL (Fin 4 ⊕ Fin 4) (ZMod 2) :=
  unitOfSq (matPlus
    !![0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 0, 0, 0, 0, 1, 0;
       0, 0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0]) (by decide +kernel)

private def plusConj : Fin 4 → GL (Fin 4 ⊕ Fin 4) (ZMod 2) := ![permLs₁, 1, permLs₂, permRs₂]

private theorem plusConj_conj (i : Fin 4) : plusConj i * pRs₁ * (plusConj i)⁻¹ = plusA i := by
  revert i
  decide +kernel

private theorem isometry_plusConj (i : Fin 4) (v : Fin 4 ⊕ Fin 4 → ZMod 2) :
    plusQuadForm 4 ((plusConj i : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)) *ᵥ v) =
      plusQuadForm 4 v := by
  revert i v
  decide +kernel

private theorem projF2_plusA_mem (i : Fin 4) :
    projF2 (plusA i) ∈ projOmegaPlus 4 (GaloisField 2 1) := by
  have hc : toF2 (plusConj i) ∈ orthogonalPlus 4 (GaloisField 2 1) :=
    toF2_mem_orthogonalPlus (isometry_plusConj i)
  have h₁ : toF2 pX₁₂ ∈ orthogonalPlus 4 (GaloisField 2 1) :=
    toF2_mem_orthogonalPlus fun v => (isometry_pX v).1
  have h₂ : toF2 pX₂₀ ∈ orthogonalPlus 4 (GaloisField 2 1) :=
    toF2_mem_orthogonalPlus fun v => (isometry_pX v).2
  rw [← plusConj_conj i, ← plus_involution.1, conjugate_commutatorElement]
  refine projF2_commutatorElement_mem ?_ ?_
  · rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem hc h₁) (inv_mem hc)
  · rw [map_mul, map_mul, map_inv]
    exact mul_mem (mul_mem hc h₂) (inv_mem hc)

private theorem centralCoverFour_projOmegaPlus_two :
    CentralCoverFour (projOmegaPlus 4 (GaloisField 2 1)) := by
  obtain ⟨h3, h1, -, hZA, hZZ, hZA'⟩ := plus_relations
  refine centralCoverFour_of_inverters
    (fun i => ⟨projF2 (plusZ i), projF2_plusZ_mem i⟩)
    (fun i => ⟨projF2 (plusA i), projF2_plusA_mem i⟩) ?_ ?_ ?_ ?_
  · intro i j
    by_cases hij : i = j
    · subst hij
      exact Commute.refl _
    · refine Subtype.ext ?_
      change projF2 (plusZ i) * projF2 (plusZ j) = projF2 (plusZ j) * projF2 (plusZ i)
      rw [← map_mul, ← map_mul, hZZ i j hij]
  · intro i
    refine orderOf_eq_prime ?_ ?_
    · refine Subtype.ext ?_
      change projF2 (plusZ i) ^ 3 = 1
      rw [← map_pow, h3 i, map_one]
    · intro h
      have hz : plusZ i ∈ Subgroup.center (GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :=
        ker_projF2_le (MonoidHom.mem_ker.2 (congrArg Subtype.val h))
      exact h1 i (Subgroup.mem_center_iff.1 hz (plusA i)).symm
  · intro i
    have hsq : plusA i * plusZ i * (plusA i)⁻¹ = plusZ i * plusZ i := by
      have hc := hZA' i
      rw [commutatorElement_def] at hc
      exact mul_inv_eq_iff_eq_mul.1 hc
    have hinv : plusA i * plusZ i * (plusA i)⁻¹ = (plusZ i)⁻¹ :=
      hsq.trans (eq_inv_of_mul_eq_one_left ((pow_three' _).symm.trans (h3 i)))
    refine Subtype.ext ?_
    change projF2 (plusA i) * projF2 (plusZ i) * (projF2 (plusA i))⁻¹ = (projF2 (plusZ i))⁻¹
    simpa only [map_mul, map_inv] using congrArg projF2 hinv
  · intro i j hij
    have hfix : plusA i * plusZ j * (plusA i)⁻¹ = plusZ j :=
      mul_inv_eq_iff_eq_mul.2 (hZA i j hij).symm
    refine Subtype.ext ?_
    change projF2 (plusA i) * projF2 (plusZ j) * (projF2 (plusA i))⁻¹ = projF2 (plusZ j)
    simpa only [map_mul, map_inv] using congrArg projF2 hfix

theorem centralCoverFour_D4Two (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.D 4 q).Valid)
    (hp : q.p = 2) (he : q.exponent = 1) :
    CentralCoverFour (TauCeti.ValidLieTypeIndex.Group ⟨.D 4 q, hv⟩) := by
  obtain ⟨e⟩ := CFSG.RankThree.PartTwo.Census.bridgeOmega8PlusTwo q hv hp he
  exact CentralCoverFour.of_mulEquiv e.symm centralCoverFour_projOmegaPlus_two

end CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank
