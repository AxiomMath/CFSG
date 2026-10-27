module

public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.OutRank
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LieType.Steinberg.TwistedD4.Defs
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link

open CFSG.LieType.Chevalley.RootOps CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.TwistedD4
  CFSG.LieType.SeitzGeneration.ExcOuterLeOne



@[expose] noncomputable def pcoord (R : Type) [CommRing R] (v : RootModule Tag.D4 R) (p : ℕ) : R :=
  posCoord Tag.D4 R p v

@[expose] def applyEnt {R : Type} [CommRing R] (L : List Entry) (w : ℕ → R) (p : ℕ) : R :=
  (L.map fun e => if e.2.1 = p then (e.2.2 : R) * w e.1 else 0).sum

theorem posCoord_entry {R : Type} [CommRing R] (c q p : ℕ) (hq : q < dim Tag.D4) (z : R)
    (v : RootModule Tag.D4 R) :
    posCoord Tag.D4 R p ((z • (posCoord Tag.D4 R c).smulRight (posVec Tag.D4 R q)) v) =
      if p = q then z * posCoord Tag.D4 R c v else 0 := by
  simp only [LinearMap.smul_apply, LinearMap.smulRight_apply, map_smul, posCoord_posVec hq,
    smul_eq_mul]
  split_ifs <;> simp [mul_comm]

theorem pcoord_entriesOp {R : Type} [CommRing R] (L : List Entry)
    (hL : ValidEntries Tag.D4 L) (v : RootModule Tag.D4 R) (p : ℕ) :
    pcoord R (entriesOp Tag.D4 R L v) p = applyEnt L (fun q => pcoord R v q) p := by
  induction L with
  | nil => simp [pcoord, applyEnt, entriesOp_nil]
  | cons e L ih =>
    have he : e.2.1 < dim Tag.D4 := (hL e (by simp)).2
    have hL' : ValidEntries Tag.D4 L := fun x hx => hL x (by simp [hx])
    have ih' := ih hL'
    simp only [pcoord, applyEnt] at ih' ⊢
    rw [entriesOp_cons, LinearMap.add_apply, map_add, posCoord_entry _ _ _ he, ih',
      List.map_cons, List.sum_cons]
    congr 1
    by_cases h : p = e.2.1
    · subst h
      simp
    · rw [if_neg h, if_neg (fun h' => h h'.symm)]

theorem endHom_xPar_pos {K : Type} [Field K] (i : Fin Tag.D4.rank) (c : K) :
    endHom K (xPar (rootOperatorFamily Tag.D4) (Pi.single i 1) c) =
      1 + c • entriesOp Tag.D4 K (entries Tag.D4 i 1) +
        c ^ 2 • entriesOp Tag.D4 K (entries Tag.D4 i 2) := by
  have hb : entryDegreeBound Tag.D4 = 2 := by simp [entryDegreeBound]
  have e : endHom K (xPar (rootOperatorFamily Tag.D4) (Pi.single i 1) c) = xOp Tag.D4 K i c := by
    rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.D4).elt_simple]
  rw [e, xOp_eq_sum_xCoeff_entryDegreeBound, hb]
  have h1 := RootOps.dataChecks_D4.simple K i 1 le_rfl (by norm_num)
  have h2 := RootOps.dataChecks_D4.simple K i 2 (by norm_num) (by norm_num)
  simp [Finset.sum_range_succ, xCoeff_zero, ← h1, ← h2, add_assoc]

theorem endHom_xPar_neg {K : Type} [Field K] (i : Fin Tag.D4.rank) (c : K) :
    endHom K (xPar (rootOperatorFamily Tag.D4) (-Pi.single i 1) c) =
      1 + c • entriesOp Tag.D4 K (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image (i : ℕ) i) 1) +
        c ^ 2 • entriesOp Tag.D4 K (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image (i : ℕ) i)
            2) := by
  have hb : entryDegreeBound Tag.D4 = 2 := by simp [entryDegreeBound]
  have e : endHom K (xPar (rootOperatorFamily Tag.D4) (-Pi.single i 1) c) = yOp Tag.D4 K i c := by
    rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily Tag.D4).elt_neg_simple]
  rw [e, yOp_eq_sum_yCoeff_entryDegreeBound, hb]
  have h1 := RootOps.dataChecks_D4.negSimple K i 1 le_rfl (by norm_num)
  have h2 := RootOps.dataChecks_D4.negSimple K i 2 (by norm_num) (by norm_num)
  simp [Finset.sum_range_succ, yCoeff_zero, ← h1, ← h2, add_assoc]

theorem pcoord_endHom_pos {K : Type} [Field K] (i : Fin Tag.D4.rank) (c : K)
    (v : RootModule Tag.D4 K) (p : ℕ)
    (hv1 : ValidEntries Tag.D4 (entries Tag.D4 i 1))
    (hv2 : ValidEntries Tag.D4 (entries Tag.D4 i 2)) :
    pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4) (Pi.single i 1) c) v) p =
      pcoord K v p + c * applyEnt (entries Tag.D4 i 1) (fun q => pcoord K v q) p +
        c ^ 2 * applyEnt (entries Tag.D4 i 2) (fun q => pcoord K v q) p := by
  rw [endHom_xPar_pos]
  simp only [pcoord, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, map_add,
    map_smul, smul_eq_mul]
  have h1 := pcoord_entriesOp (entries Tag.D4 i 1) hv1 v p
  have h2 := pcoord_entriesOp (entries Tag.D4 i 2) hv2 v p
  simp only [pcoord] at h1 h2
  rw [h1, h2]

theorem pcoord_endHom_neg {K : Type} [Field K] (i : Fin Tag.D4.rank) (c : K)
    (v : RootModule Tag.D4 K) (p : ℕ)
    (hv1 : ValidEntries Tag.D4 (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image (i : ℕ) i) 1))
    (hv2 : ValidEntries Tag.D4 (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image (i : ℕ) i) 2)) :
    pcoord K (endHom K (xPar (rootOperatorFamily Tag.D4) (-Pi.single i 1) c) v) p =
      pcoord K v p + c * applyEnt (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image (i : ℕ) i) 1)
        (fun q => pcoord K v q) p +
        c ^ 2 * applyEnt (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image (i : ℕ) i) 2)
          (fun q => pcoord K v q) p := by
  rw [endHom_xPar_neg]
  simp only [pcoord, LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, map_add,
    map_smul, smul_eq_mul]
  have h1 := pcoord_entriesOp (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image (i : ℕ) i) 1)
      hv1 v p
  have h2 := pcoord_entriesOp (entries Tag.D4 ((Tag.rootCertificate Tag.D4).image (i : ℕ) i) 2)
      hv2 v p
  simp only [pcoord] at h1 h2
  rw [h1, h2]


end CFSG.LieType.SeitzGeneration.ExcWideThree.D4TwF2Link

end
