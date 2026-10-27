module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerDec
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6ThreeLayerStep

public noncomputable section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

open Matrix CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Seitz
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped MatrixGroups

set_option linter.unusedSectionVars false

section Gen

variable
  {K : Type} [Field K]

theorem conj_e6LineElt_ne_one {ω : Kˣ} (h1 : ω ≠ 1) :
    (MulAut.conj (e6LineElt ω) : MulAut (adjointGroup Tag.E6 K)) ≠ 1 := by
  intro h
  have hαr : IsRoot Tag.E6 (Pi.single e6KacNode 1 : Fin Tag.E6.rank → ℤ) :=
    isRoot_single Tag.E6 e6KacNode
  have e := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) =>
    ((φ ⟨pinnedX Tag.E6 K (Pi.single e6KacNode 1) 1, pinnedX_mem_adjointGroup _ 1⟩ :
      adjointGroup Tag.E6 K) : ModGL Tag.E6 K)) h
  simp only [MulAut.one_apply] at e
  have e2 : rootDiagUnit Tag.E6 (e6LineChar ω) * pinnedX Tag.E6 K (Pi.single e6KacNode 1) 1 *
      (rootDiagUnit Tag.E6 (e6LineChar ω))⁻¹ = pinnedX Tag.E6 K (Pi.single e6KacNode 1) 1 := e
  rw [rootDiagUnit_conj_pinnedX _ hαr, rootChar_e6LineChar, Pi.single_eq_same, zpow_one] at e2
  have e3 := pinnedX_injective Tag.E6 K _ e2
  apply h1
  apply Units.ext
  simpa using e3

theorem conj_e6LineElt_apply_of_mem {ω : Kˣ} (h3 : ω ^ 3 = 1) (h1 : ω ≠ 1) (i : Fin 3)
    {x : adjointGroup Tag.E6 K} (hx : (x : ModGL Tag.E6 K) ∈ e6LineFactor K i) :
    (MulAut.conj (e6LineElt ω) : MulAut (adjointGroup Tag.E6 K)) x = x := by
  have hS : ((e6LineRoots i : Finset (Fin Tag.E6.rank → ℤ)) : Set (Fin Tag.E6.rank → ℤ)) ⊆
      rootCharKernel (e6LineChar ω) := fun α hα => by
    rw [e6Line_kernel h3 h1]
    exact Set.mem_iUnion.2 ⟨i, hα⟩
  have hmem : (x : ModGL Tag.E6 K) ∈ Subgroup.centralizer {rootDiagUnit Tag.E6 (e6LineChar ω)} :=
    rootSpan_le_centralizer (e6LineChar ω) hS hx
  exact Subtype.ext (conj_eq_iff_mem_centralizer.2 hmem)

theorem e6LineFactor_le_seitzHyperGamma [Finite K] (hchar : ringChar K ≠ 3)
    (h3 : 3 ∣ Nat.card K - 1) (h4 : Nat.card K ≠ 4) {ω : Kˣ} (hw3 : ω ^ 3 = 1) (hw1 : ω ≠ 1)
    {E : Subgroup (MulAut (adjointGroup Tag.E6 K))} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 3) (hEd : E ≤ e6Inndiag K)
    (hsig : MulAut.conj (e6LineElt ω) ∈ E) (i : Fin 3) :
    (e6LineFactor K i).subgroupOf (adjointGroup Tag.E6 K) ≤ seitzHyperGamma 3 E := by
  have hK4 : 4 ≤ Nat.card K := (four_lt_card_of_three_dvd h3 h4).le
  obtain ⟨ρ, hinj, hrange, hd⟩ := exists_lineFrames K
  have hρC : ∀ i s, ρ i s ∈ adjointGroup Tag.E6 K := fun i s => by
    have hx : ρ i s ∈ e6LineFactor K i := (hrange i) ▸ ⟨s, rfl⟩
    exact (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α : e6LineFactor K i ≤ _) hx
  have key := layerStep_of_three_copies h3 h4 hE (by rw [hcard]; norm_num)
    (ρ := fun i => (ρ i).codRestrict (adjointGroup Tag.E6 K) (hρC i))
    (fun i x y hxy => hinj i (congrArg Subtype.val hxy))
    (fun i j hij s t => Subtype.ext (e6LineFactor_commute hij
      ((hrange i) ▸ ⟨s, rfl⟩) ((hrange j) ▸ ⟨t, rfl⟩)))
    hsig (conj_e6LineElt_ne_one hw1)
    (fun i s => conj_e6LineElt_apply_of_mem hw3 hw1 i ((hrange i) ▸ ⟨s, rfl⟩))
    (fun ε hε => exists_hdec hw3 hw1 hK4 hE hEd hsig hρC hrange hd hε) i
  rw [range_codRestrict_eq, hrange] at key
  exact key

theorem e6ThreeLayerGen_holds : E6ThreeLayerGen :=
  fun K _ _ hc h3 h4 ω hw3 hw1 E hE hcard hEd hsig i =>
    e6LineFactor_le_seitzHyperGamma hc h3 h4 hw3 hw1 hE hcard hEd hsig i

end Gen

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

end
