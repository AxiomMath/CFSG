module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OFiveTwFaceD4
public import CFSG.LieType.Chevalley.E6SignedGraphRankOneGroups
public import CFSG.LieType.Chevalley.E6SignedGraphRoots
public import CFSG.LieType.Chevalley.FoldedRootOrbits
public import CFSG.LieType.Chevalley.E6FieldGraphFieldPointwiseCentralizer
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
public import CFSG.LieType.SeitzGeneration.ExcHigh.TwE6TwoAssembly
public import CFSG.LieType.SeitzGeneration.ExcHigh.Product

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.LieType.SeitzGeneration.ExcWideThree
open CFSG.LieType.Chevalley.E6GraphHighestRoot CFSG.LieType.Chevalley.E6SignedGraph

local notation "Γ₂" F => ModGL TwistTag.E6.tag F

@[expose] def d4Beta : Fin TwistTag.E6.tag.rank → ℤ := ![1, 1, 2, 2, 1, 1]

@[expose] def d4BetaRho : Fin TwistTag.E6.tag.rank → ℤ := ![1, 1, 1, 2, 2, 1]

theorem isRoot_d4Beta : IsRoot TwistTag.E6.tag d4Beta := by
  rw [CFSG.LieType.Chevalley.E6SignedGraph.isRoot_iff_cert]
  decide

theorem isRoot_d4BetaRho : IsRoot TwistTag.E6.tag d4BetaRho := by
  rw [CFSG.LieType.Chevalley.E6SignedGraph.isRoot_iff_cert]
  decide

theorem d4Beta_ne_d4BetaRho : d4Beta ≠ d4BetaRho := by decide

theorem diagramOrbit_d4Beta :
    TwistTag.E6.diagramOrbit d4Beta = ({d4Beta, d4BetaRho} : Finset _) := by decide

private theorem height_d4Beta : height d4Beta = 8 := by decide

private theorem height_d4BetaRho : height d4BetaRho = 8 := by decide

theorem height_of_mem_d4Beta_pair
    {v : Fin TwistTag.E6.tag.rank → ℤ}
    (hv : v ∈ ({d4Beta, d4BetaRho} : Finset (Fin TwistTag.E6.tag.rank → ℤ))) :
    height v = 8 := by
  rcases Finset.mem_insert.1 hv with h | h
  · rw [h]; exact height_d4Beta
  · rw [Finset.mem_singleton.1 h]; exact height_d4BetaRho

theorem rootChar_d4TorusParam_eq_one_of_coord_eq {F : Type} [Field F] (ω : Fˣ)
    {v : Fin TwistTag.E6.tag.rank → ℤ} (hv : v 0 = v 5) :
    rootChar (d4TorusParam ω) v = 1 := by
  have hmul : ∀ (a b : Fin TwistTag.E6.tag.rank → Fˣ)
      (u : Fin TwistTag.E6.tag.rank → ℤ),
      rootChar (a * b) u = rootChar a u * rootChar b u := by
    intro a b u
    rw [rootChar, rootChar, rootChar, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by rw [Pi.mul_apply, mul_zpow]
  rw [d4TorusParam, hmul, CFSG.LieType.Chevalley.RootTorus.rootChar_mulSingle,
    CFSG.LieType.Chevalley.RootTorus.rootChar_mulSingle, hv, ← mul_zpow, mul_inv_cancel,
    one_zpow]

theorem coe_orbitX_of_card_two {F : Type} [Field F] {σ : F →+* F}
    {a : Fin TwistTag.E6.foldedTag.rank} (hcard : (TwistTag.E6.orbit a).card = 2)
    (c : orbitField TwistTag.E6 F σ a) :
    (orbitX TwistTag.E6 F σ a c : ModGL TwistTag.E6.tag F) =
      xUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
        xUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (σ (c : F)) := by
  rw [coe_orbitX, hcard]
  norm_num [List.range_succ]

theorem coe_orbitY_of_card_two {F : Type} [Field F] {σ : F →+* F}
    {a : Fin TwistTag.E6.foldedTag.rank} (hcard : (TwistTag.E6.orbit a).card = 2)
    (c : orbitField TwistTag.E6 F σ a) :
    (orbitY TwistTag.E6 F σ a c : ModGL TwistTag.E6.tag F) =
      yUnit TwistTag.E6.tag F (TwistTag.E6.orbitMin a) (c : F) *
        yUnit TwistTag.E6.tag F (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) (σ (c : F)) := by
  rw [coe_orbitY, hcard]
  norm_num [List.range_succ]

theorem conj_canonicalRep_xUnit_eq_of_two_eq_zero {F : Type} [Field F]
    (h2 : (2 : F) = 0) {w : WeylGroup TwistTag.E6.tag} (k : Fin TwistTag.E6.tag.rank) (c : F) :
    canonicalRep (coxeterSystem TwistTag.E6.tag) F w * xUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹ =
      pinnedX TwistTag.E6.tag F (w • Pi.single k 1) c := by
  obtain ⟨ε, hε, h⟩ := canonicalRep_conj_xUnit (K := F) w k
  rw [h, CFSG.LieType.Chevalley.eq_one_of_mul_self_eq_one_of_two_eq_zero h2 hε, one_mul]

theorem pinnedX_d4Beta_mem_parabolicRadical {F : Type} [Field F] (t : F) :
    pinnedX TwistTag.E6.tag F d4Beta t ∈
      parabolicRadical TwistTag.E6.tag F (TwistTag.E6.orbitUnion twE6MaxD4) := by
  refine pinnedX_mem_rootSpan (S := parabolicRadicalRoots TwistTag.E6.tag
    (TwistTag.E6.orbitUnion twE6MaxD4)) ?_ t
  rw [mem_parabolicRadicalRoots_iff]
  refine ⟨isRoot_d4Beta, by decide, ⟨0, ?_, by decide⟩⟩
  rw [orbitUnion_twE6MaxD4]
  decide

theorem pinnedX_d4BetaRho_mem_parabolicRadical {F : Type} [Field F] (t : F) :
    pinnedX TwistTag.E6.tag F d4BetaRho t ∈
      parabolicRadical TwistTag.E6.tag F (TwistTag.E6.orbitUnion twE6MaxD4) := by
  refine pinnedX_mem_rootSpan (S := parabolicRadicalRoots TwistTag.E6.tag
    (TwistTag.E6.orbitUnion twE6MaxD4)) ?_ t
  rw [mem_parabolicRadicalRoots_iff]
  refine ⟨isRoot_d4BetaRho, by decide, ⟨0, ?_, by decide⟩⟩
  rw [orbitUnion_twE6MaxD4]
  decide

private theorem d4Witness_conjD_canonicalRep_xUnit {F : Type} [Field F] {ω : Fˣ}
    {w : WeylGroup TwistTag.E6.tag} {k : Fin TwistTag.E6.tag.rank} (c : F) :
    d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w * xUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * (d4Witness ω)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        xUnit TwistTag.E6.tag F k
          ((rootChar (d4TorusParam ω) (w • Pi.single k 1) : F) * c) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹ := by
  obtain ⟨ε, -, h⟩ := canonicalRep_conj_xUnit (K := F) w k
  rw [h]
  change rootDiagUnit TwistTag.E6.tag (d4TorusParam ω) *
      pinnedX TwistTag.E6.tag F (w • Pi.single k 1) (ε * c) *
      (rootDiagUnit TwistTag.E6.tag (d4TorusParam ω))⁻¹ =
    canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
      xUnit TwistTag.E6.tag F k
        ((rootChar (d4TorusParam ω) (w • Pi.single k 1) : F) * c) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹
  rw [rootDiagUnit_conj_pinnedX (d4TorusParam ω)
    (IsRoot.smul (isRoot_single TwistTag.E6.tag k) w) (ε * c), h]
  congr 1
  ring

private theorem d4Witness_conjD_canonicalRep_yUnit {F : Type} [Field F] {ω : Fˣ}
    {w : WeylGroup TwistTag.E6.tag} {k : Fin TwistTag.E6.tag.rank} (c : F) :
    d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w * yUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * (d4Witness ω)⁻¹ =
      canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        yUnit TwistTag.E6.tag F k
          ((rootChar (d4TorusParam ω) (w • -(Pi.single k 1)) : F) * c) *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹ := by
  obtain ⟨ε, -, h⟩ := canonicalRep_conj_yUnit (K := F) w k
  rw [h]
  change rootDiagUnit TwistTag.E6.tag (d4TorusParam ω) *
      pinnedX TwistTag.E6.tag F (w • -Pi.single k 1) (ε * c) *
      (rootDiagUnit TwistTag.E6.tag (d4TorusParam ω))⁻¹ =
    canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
      yUnit TwistTag.E6.tag F k
        ((rootChar (d4TorusParam ω) (w • -Pi.single k 1) : F) * c) *
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹
  rw [rootDiagUnit_conj_pinnedX (d4TorusParam ω)
    (IsRoot.smul (isRoot_neg_single TwistTag.E6.tag k) w) (ε * c), h]
  congr 1
  ring

theorem d4Witness_commute_conj_xUnit {F : Type} [Field F] {ω : Fˣ}
    {w : WeylGroup TwistTag.E6.tag} {k : Fin TwistTag.E6.tag.rank}
    (hχ : rootChar (d4TorusParam ω) (w • Pi.single k 1) = 1) (c : F) :
    d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w * xUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w * xUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * d4Witness ω := by
  have h := d4Witness_conjD_canonicalRep_xUnit (ω := ω) (w := w) (k := k) c
  rw [hχ, Units.val_one, one_mul] at h
  calc d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        xUnit TwistTag.E6.tag F k c * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) =
      (d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        xUnit TwistTag.E6.tag F k c * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) *
        (d4Witness ω)⁻¹) * d4Witness ω := by group
    _ = (canonicalRep (coxeterSystem TwistTag.E6.tag) F w * xUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * d4Witness ω := by rw [h]

theorem d4Witness_commute_conj_yUnit {F : Type} [Field F] {ω : Fˣ}
    {w : WeylGroup TwistTag.E6.tag} {k : Fin TwistTag.E6.tag.rank}
    (hχ : rootChar (d4TorusParam ω) (w • -(Pi.single k 1)) = 1) (c : F) :
    d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w * yUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) =
      (canonicalRep (coxeterSystem TwistTag.E6.tag) F w * yUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * d4Witness ω := by
  have h := d4Witness_conjD_canonicalRep_yUnit (ω := ω) (w := w) (k := k) c
  rw [hχ, Units.val_one, one_mul] at h
  calc d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        yUnit TwistTag.E6.tag F k c * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) =
      (d4Witness ω * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w *
        yUnit TwistTag.E6.tag F k c * (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) *
        (d4Witness ω)⁻¹) * d4Witness ω := by group
    _ = (canonicalRep (coxeterSystem TwistTag.E6.tag) F w * yUnit TwistTag.E6.tag F k c *
        (canonicalRep (coxeterSystem TwistTag.E6.tag) F w)⁻¹) * d4Witness ω := by rw [h]

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
