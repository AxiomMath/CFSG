module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE6F4Frame
public import CFSG.LieType.Chevalley.E6SignedGraphRankOneGroups

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof

open CFSG CFSG.LieType CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.Timmesfeld CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Chevalley.E6SignedGraph
open CFSG.ClassicalInvolution.WeakCT (blk hom_ext_sl2 blk_zero_tv01 blk_zero_tv10 blk_one_tv01
  blk_one_tv10 range_le_of_tv)
open scoped MatrixGroups Matrix

@[expose] def e6C4Word :
    WeylGroup TwistTag.E6.tag :=
  (coxeterSystem TwistTag.E6.tag).wordProd [⟨1, by decide⟩, ⟨3, by decide⟩]

theorem e6C4Word_mem :
    e6C4Word ∈ relWeylTwist TwistTag.E6 := by
  have h3 : TwistTag.E6.orbitWord ⟨3, by decide⟩ = [⟨1, by decide⟩] := by decide
  have h2 : TwistTag.E6.orbitWord ⟨2, by decide⟩ = [⟨3, by decide⟩] := by decide
  have e : e6C4Word = TwistTag.E6.orbitReflection ⟨3, by decide⟩ *
      TwistTag.E6.orbitReflection ⟨2, by decide⟩ := by
    rw [TwistTag.orbitReflection, TwistTag.orbitReflection, h3, h2,
      ← CoxeterSystem.wordProd_append]
    rfl
  rw [e]
  exact mul_mem (TwistTag.E6.orbitReflection_mem _) (TwistTag.E6.orbitReflection_mem _)

theorem e6C4Word_smul :
    e6C4Word • (Pi.single ⟨2, by decide⟩ 1 : E6Vec) = simpleRoot 0 ∧
      e6C4Word • (Pi.single ⟨4, by decide⟩ 1 : E6Vec) = rho (simpleRoot 0) := by
  rw [e6C4Word, wordProd_smul, wordProd_smul]
  decide +kernel

theorem orbitImage_e6C4Word :
    orbitImage e6C4Word ⟨1, by decide⟩ = simpleOrbit 0 := by
  rw [orbitImage_pair (by decide) e6C4Word,
    show TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ by decide,
    show TwistTag.E6.perm ⟨2, by decide⟩ = ⟨4, by decide⟩ by decide, e6C4Word_smul.1,
    e6C4Word_smul.2, simpleOrbit, diagramOrbit_eq]

theorem orbitSign_e6C4Word
    (K : Type) [Field K] : orbitSign K e6C4Word ⟨1, by decide⟩ = -1 := by
  rw [orbitSign, show TwistTag.E6.orbitMin ⟨1, by decide⟩ = ⟨2, by decide⟩ by decide,
    e6C4Word_smul.1, show (simpleRoot 0) ⟨1, by decide⟩ = 1 by decide, zpow_one]

theorem canonicalRep_e6C4Word
    (K : Type) [Field K] :
    canonicalRep (coxeterSystem TwistTag.E6.tag) K e6C4Word =
      weylElt TwistTag.E6.tag K ⟨1, by decide⟩ 1 * weylElt TwistTag.E6.tag K ⟨3, by decide⟩ 1 := by
  rw [e6C4Word, canonicalRep_wordProd (isReduced_of_reducedCheck (by decide +kernel))]
  simp

section Family

variable (K : Type) [Field K]

@[expose] def e6C4Rho :
    Fin 4 → SL(2, K) →* ModGL TwistTag.E6.tag K :=
  ![orbitSL2 K e6C4Word ⟨1, by decide⟩, orbitSL2 K 1 ⟨0, by decide⟩, orbitSL2 K 1 ⟨1, by decide⟩,
    orbitSL2 K 1 ⟨2, by decide⟩]

theorem e6C4Rho_eq_e6F4Rho :
    e6C4Rho K 1 = e6F4Rho K 3 ∧ e6C4Rho K 2 = e6F4Rho K 2 ∧ e6C4Rho K 3 = e6F4Rho K 1 := by
  have hs : ∀ a : Fin TwistTag.E6.foldedTag.rank, TwistTag.E6.orbitMin a ≠ ⟨1, by decide⟩ →
      orbitSign K 1 a = 1 := fun a ha => by
    rw [orbitSign, one_smul, Pi.single_eq_of_ne (Ne.symm ha), zpow_zero]
  refine ⟨MonoidHom.ext fun M => ?_, MonoidHom.ext fun M => ?_, MonoidHom.ext fun M => ?_⟩
  · obtain ⟨-, h⟩ := orbitSL2_pair (K := K) (w := 1) (a := ⟨0, by decide⟩) (j := ⟨5, by decide⟩)
      (by decide) (by decide)
    change orbitSL2 K 1 ⟨0, by decide⟩ M = _
    rw [h M, canonicalRep_one, hs _ (by decide), diagConj_one, one_mul, inv_one, mul_one]
    rfl
  · obtain ⟨-, h⟩ := orbitSL2_pair (K := K) (w := 1) (a := ⟨1, by decide⟩) (j := ⟨4, by decide⟩)
      (by decide) (by decide)
    change orbitSL2 K 1 ⟨1, by decide⟩ M = _
    rw [h M, canonicalRep_one, hs _ (by decide), diagConj_one, one_mul, inv_one, mul_one]
    rfl
  · change orbitSL2 K 1 ⟨2, by decide⟩ M = _
    rw [orbitSL2_single (by decide) M, canonicalRep_one, one_mul, inv_one, mul_one]
    rfl

theorem e6C4Rho_zero_apply
    (M : SL(2, K)) :
    e6C4Rho K 0 M = canonicalRep (coxeterSystem TwistTag.E6.tag) K e6C4Word *
      (simpleRootSL2 TwistTag.E6.tag K ⟨2, by decide⟩ M *
        simpleRootSL2 TwistTag.E6.tag K ⟨4, by decide⟩ (diagConj K (-1) M)) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) K e6C4Word)⁻¹ := by
  obtain ⟨-, h⟩ := orbitSL2_pair (K := K) (w := e6C4Word) (a := ⟨1, by decide⟩)
    (j := ⟨4, by decide⟩) (by decide) (by decide)
  change orbitSL2 K e6C4Word ⟨1, by decide⟩ M = _
  rw [h M, orbitSign_e6C4Word]
  rfl

end Family

end CFSG.ComponentClassification.CatLeafProof
