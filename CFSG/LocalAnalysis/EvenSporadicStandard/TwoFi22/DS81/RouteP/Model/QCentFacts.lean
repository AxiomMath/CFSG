module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.QCentCount
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.TPair
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.S1
public import Certificates.Certificate450290
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.PlaneAction
import all CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
open CFSG.Quasithin (pairVec)
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

theorem tauM24_two : tauM24 2 = 5 := by decide

theorem t13_eq_epsElt :
    t13 = epsElt ⟨8, by norm_num⟩ := by
  have hne : tauM24 0 ≠ tauM24 2 := tauM24.injective.ne (by decide)
  have h1 : cocodeCoords.κ (pairVec (tauM24 0) (tauM24 2)) = toW 11 (actM cocodeMCols 256) := by
    rw [kappa11_pairVec_mask _ _ hne, tauM24_zero, tauM24_two]
    exact congrArg (toW 11) (by decide +kernel)
  have h2 : e0.symm (cocodeCoords.κ (pairVec (tauM24 0) (tauM24 2))) = epsQ 256 := by
    rw [h1, ← e0_epsQ, MulEquiv.symm_apply_apply]
  have h3 : t13 = epsMask 256 := by
    change (((e0.symm (cocodeCoords.κ (pairVec (tauM24 0) (tauM24 2))) : ↥E0q) : ↥Zq) : Q3) = _
    rw [h2]
    rfl
  rw [h3, show (256 : ℕ) = 2 ^ 8 by norm_num]
  exact epsMask_two_pow (j := 8) (by norm_num)

theorem rep_t13 :
    Rep 920808 objTabs[epsReg qcentEps]! t13 := by
  rw [t13_eq_epsElt]
  exact rep_epsElt ⟨8, by norm_num⟩

structure QCentParts (tau t13 : Table) (G0 : CFSG.Perm.Native.Tree) (G : Array Table)
    (T : CFSG.Perm.Native.Tree) : Prop where
  c0 : ((Finset.range G0.pts.size).filter fun k =>
    (ap t13 (ap G0.pts k) == ap G0.pts k) = true).card = 3511
  c1 : ((Finset.range G0.pts.size).filter fun k =>
    (ap t13 (ap tau (ap G0.pts k)) == ap tau (ap G0.pts k)) = true).card = 695
  gsize : G.size = 14
  tsize : T.pts.size = 693
  tree : CFSG.Perm.Native.treeOK degree qcentRoot T G (Array.range 14) = true
  notMem : memTree T 99705 = false
  cover : ∀ k < G0.pts.size, memTree G0 (ap tau (ap G0.pts k)) = true →
    ap t13 (ap tau (ap G0.pts k)) = ap tau (ap G0.pts k) →
    ap tau (ap G0.pts k) = 99705 ∨ memTree T (ap tau (ap G0.pts k)) = true

theorem QCentParts.of_qcentCheck {tau t13 : Table} {G0 : CFSG.Perm.Native.Tree} {G : Array Table}
    {T : CFSG.Perm.Native.Tree} (h : qcentCheck tau t13 G0 G T = true) :
    QCentParts tau t13 G0 G T := by
  unfold qcentCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨?_, ?_, h2, h3, h4, h5, ?_⟩
  · have := qcentCount_eq (fun k => ap t13 (ap G0.pts k) == ap G0.pts k) G0.pts.size 0
    omega
  · have := qcentCount_eq (fun k => ap t13 (ap tau (ap G0.pts k)) == ap tau (ap G0.pts k))
      G0.pts.size 0
    omega
  · intro k hk hm ht
    have h := allIn_zero_iff.1 h6 k hk
    simp only [hm, ht, Bool.and_self, beq_self_eq_true, Bool.not_true, Bool.false_or,
      Bool.or_eq_true, beq_iff_eq] at h
    exact h

theorem qcentOK_eq_true : qcentOK () = true :=
  Certificates.certificate450290

abbrev qcentTree : CFSG.Perm.Native.Tree :=
  CFSG.Perm.Native.treeBFS degree qcentRoot (qcentGens objTabs) (Array.range planeGenCount)

theorem qcentParts :
    QCentParts objTabs[tauReg]! objTabs[epsReg qcentEps]! gTrees[1]! (qcentGens objTabs)
      qcentTree := by
  have h := qcentOK_eq_true
  unfold qcentOK qcentOKAt at h
  unfold gTrees
  exact QCentParts.of_qcentCheck h

theorem ncard_fixed_gamma :
    {y : Ω | Δ.Adj x0 y ∧ t13 • y = y}.ncard = 3511 := by
  have hT : CFSG.Perm.TreeFacts 920808 gTrees[1]! zpLetters genQ geomReps[1]! := treeFacts 1
  have hset : {y : Ω | Δ.Adj x0 y ∧ t13 • y = y} =
      {y : Fin 920808 | (∃ k < gTrees[1]!.pts.size, ap gTrees[1]!.pts k = y.val) ∧
        (fun p => ap objTabs[epsReg qcentEps]! p == p) y.val = true} := by
    ext y
    simp only [Set.mem_setOf_eq, beq_iff_eq]
    rw [Δ_adj_x0_iff, mem_orbit_x1_iff]
    refine and_congr Iff.rfl ?_
    rw [← smul_val_of_rep rep_t13 y]
    exact Fin.ext_iff
  exact (congrArg Set.ncard hset).trans
    ((ncard_filter_tree hT (fun p => ap objTabs[epsReg qcentEps]! p == p)).trans qcentParts.c0)

theorem ncard_fixed_gamma_tau :
    {y : Ω | Δ.Adj x0 y ∧ t13 • (tauElt • y) = tauElt • y}.ncard = 695 := by
  have hT : CFSG.Perm.TreeFacts 920808 gTrees[1]! zpLetters genQ geomReps[1]! := treeFacts 1
  have hset : {y : Ω | Δ.Adj x0 y ∧ t13 • (tauElt • y) = tauElt • y} =
      {y : Fin 920808 | (∃ k < gTrees[1]!.pts.size, ap gTrees[1]!.pts k = y.val) ∧
        (fun p => ap objTabs[epsReg qcentEps]! (ap objTabs[tauReg]! p) ==
          ap objTabs[tauReg]! p) y.val = true} := by
    ext y
    simp only [Set.mem_setOf_eq, beq_iff_eq]
    rw [Δ_adj_x0_iff, mem_orbit_x1_iff]
    refine and_congr Iff.rfl ?_
    rw [← smul_val_of_rep rep_tauElt y, ← smul_val_of_rep rep_t13 (tauElt • y)]
    exact Fin.ext_iff
  exact (congrArg Set.ncard hset).trans
    ((ncard_filter_tree hT (fun p => ap objTabs[epsReg qcentEps]! (ap objTabs[tauReg]! p) ==
      ap objTabs[tauReg]! p)).trans qcentParts.c1)

@[expose] noncomputable def qcentW : Subgroup Q3 :=
  CFSG.Perm.lettersGroup (Array.range planeGenCount) planeGen

@[expose] def qcentRootPt : Ω := ⟨qcentRoot, by decide⟩

theorem qcentW_le_Q0 :
    qcentW ≤ Q0 := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨l, hl, rfl⟩
  exact planeGen_mem_Q0 (Array.mem_range.1 hl)

theorem qcentTreeFacts :
    CFSG.Perm.TreeFacts 920808 qcentTree (Array.range planeGenCount) planeGen qcentRoot := by
  refine CFSG.Perm.treeOK_facts (n := 920808) (fun l hl => ?_) qcentParts.tree
  have hl' : l < planeGenCount := Array.mem_range.1 hl
  have e : (qcentGens objTabs)[l]! =
      planeGenTabAt objTabs (planeDWords ()) (planeUWord ()) (planeVWord ()) l := by
    unfold qcentGens
    exact getElem!_map_range _ hl'
  rw [e]
  exact rep_planeGen l

theorem card_orbit_qcentW :
    Nat.card (MulAction.orbit qcentW qcentRootPt) = 693 := by
  have h := qcentTreeFacts.card_orbit
  rw [qcentParts.tsize] at h
  exact h

theorem notMem_orbit_qcentW :
    x2 ∉ MulAction.orbit qcentW qcentRootPt := by
  intro h
  obtain ⟨k, hk, hkx⟩ := (qcentTreeFacts.mem_orbit_iff x2).1 h
  have hm : memTree qcentTree 99705 = true :=
    memTree_of_exists qcentTreeFacts.pos_pts ⟨k, hk, by rw [hkx]; rfl⟩
  rw [qcentParts.notMem] at hm
  exact Bool.false_ne_true hm

theorem eq_x2_or_mem_orbit_qcentW
    {a : Ω}
    (h0 : Δ.Adj x0 a) (h1 : Δ.Adj x1 a) (ha : t13 • a = a) :
    a = x2 ∨ a ∈ MulAction.orbit qcentW qcentRootPt := by
  have hT : CFSG.Perm.TreeFacts 920808 gTrees[1]! zpLetters genQ geomReps[1]! := treeFacts 1
  have hτ : tauElt⁻¹ • x1 = x0 := inv_smul_eq_iff.2 tauElt_smul_x0.symm
  have hc : Δ.Adj x0 (tauElt⁻¹ • a) := by
    have h := (Δ_adj_smul tauElt⁻¹ x1 a).2 h1
    rwa [hτ] at h
  obtain ⟨k, hk, hkc⟩ := (mem_orbit_x1_iff _).1 (Δ_adj_x0_iff.1 hc)
  have hval : ap objTabs[tauReg]! (ap gTrees[1]!.pts k) = a.val := by
    rw [hkc, ← smul_val_of_rep rep_tauElt, smul_inv_smul]
  have hmem : memTree gTrees[1]! a.val = true :=
    memTree_of_exists hT.pos_pts ((mem_orbit_x1_iff a).1 (Δ_adj_x0_iff.1 h0))
  have hfix : ap objTabs[epsReg qcentEps]! a.val = a.val := by
    rw [← smul_val_of_rep rep_t13 a, ha]
  have hcov := qcentParts.cover k hk (by rw [hval]; exact hmem) (by rw [hval]; exact hfix)
  rw [hval] at hcov
  rcases hcov with h | h
  · exact Or.inl (Fin.ext h)
  · obtain ⟨j, hj, hja⟩ := memTree_spec h
    exact Or.inr ((qcentTreeFacts.mem_orbit_iff a).2 ⟨j, hj, hja⟩)

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model
