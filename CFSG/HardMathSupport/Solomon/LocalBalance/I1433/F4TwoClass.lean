module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.TwCompSUF4

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne.KE
open scoped MatrixGroups Matrix

set_option maxRecDepth 100000
set_option linter.unusedSectionVars false

theorem f4_count6 : ∀ c ∈ f4Conn,
    kacCount Tag.F4 ![2, 3, 4, 2] (c.map (idxNode (r := Tag.F4.rank))).toFinset = 6 →
      c = [0, 1] ∨ c = [1, 2] ∨ c = [3, 4] := by
  decide +kernel


theorem exists_a2frame_of_class {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ}
    (S : LangSetup Tag.F4 L p₀) (hp : p.Prime) (hpL : (p : L) ≠ 0)
    {a : Fin Tag.F4.rank → Lˣ} (hTp : rootDiagUnit Tag.F4 a ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (h6 : (componentRoots (rootCharHom a) i).ncard = 6) :
    ∃ (ψ : SL(3, L) →* ModGL Tag.F4 L) (σ : Fin 3 → Fin 3 → Fin Tag.F4.rank → ℤ) (κ : ℤ),
      IsA2Frame ψ σ ∧ (κ = 1 ∨ κ = 2) ∧
        (∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * κ) ∧
        componentRoots (rootCharHom a) i = frameRoots σ := by
  classical
  obtain ⟨v, μ, hμ, hall⟩ := S.exists_kacT_of_prime hp hpL facts_F4 hTp
  obtain ⟨x, hx, hi⟩ := hall i
  obtain ⟨c, hc, hcomp⟩ := kacF4.exists_comp_eq_of_check f4_tree f4_adj (adm := fun _ => true)
    f4_check rfl hx
  set C : Finset (Option (Fin Tag.F4.rank)) := (c.map (idxNode (r := Tag.F4.rank))).toFinset
    with hCdef
  have hCset : kacF4.comp p μ x = (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hcomp]
    ext y
    simp only [Set.mem_ofPred_eq, hCdef, List.coe_toFinset, List.mem_map]
    constructor
    · intro hy
      exact ⟨nodeIdx y, hy, idxNode_nodeIdx y⟩
    · rintro ⟨w, hw, rfl⟩
      rw [nodeIdx_idxNode (f4_lt c hc w hw)]
      exact hw
  have hCp : ∃ y, y ∉ C := by
    obtain ⟨y, hy⟩ := exists_not_mem_comp kacF4 hp.pos μ x
    exact ⟨y, fun h => hy (by rw [hCset]; exact h)⟩
  have hi' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' kacF4.rootsOf (C : Set (Option (Fin Tag.F4.rank))) := by
    rw [hi, hCset]
  have hncard : (componentRoots (rootCharHom a) i).ncard =
      kacCount Tag.F4 kacF4.θ (c.map (idxNode (r := Tag.F4.rank))).toFinset := by
    rw [hi', ncard_image_smul, ncard_rootsOf kacF4 facts_F4 hCp]
  rw [hncard] at h6
  rcases f4_count6 c hc h6 with rfl | rfl | rfl
  ·
    have hC : C = {none, some 0} := by rw [hCdef]; decide
    have hroots := f4_rootsOf_eq (C := C) hCp (σ := f4Sigma01)
      (by rw [hC]; exact f4_long01_roots) (fun a b hab => by
        rw [hC]
        exact ⟨(f4_long01_isRoot a b hab).1, (f4_long01_isRoot a b hab).2.1⟩)
    refine ⟨_, fun a b => v • f4Sigma01 a b, 2, f4_long01_frame.transport v, Or.inr rfl,
      fun a b hab => ?_, ?_⟩
    · rw [iform_smul]
      exact (f4_long01_isRoot a b hab).2.2
    · rw [hi', hroots, IsSLFrame.frameRoots_smul]
  ·
    have hC : C = {some 0, some 1} := by rw [hCdef]; decide
    have hroots := f4_rootsOf_eq (C := C) hCp
      (σ := fun a b => CFSG.RankThree.E6.chainRoot f4chainLong a b)
      (by rw [hC]; exact f4_long12_roots) (fun a b hab => by
        rw [hC]
        exact ⟨(f4_long12_isRoot a b hab).1, (f4_long12_isRoot a b hab).2.1⟩)
    refine ⟨_, fun a b => v • CFSG.RankThree.E6.chainRoot f4chainLong a b, 2,
      f4Long_frame.transport v, Or.inr rfl, fun a b hab => ?_, ?_⟩
    · rw [iform_smul]
      exact (f4_long12_isRoot a b hab).2.2
    · rw [hi', hroots, IsSLFrame.frameRoots_smul]
  ·
    have hC : C = {some 2, some 3} := by rw [hCdef]; decide
    have hroots := f4_rootsOf_eq (C := C) hCp (σ := f4ShortSigma)
      (by rw [hC]; exact f4_short_roots) (fun a b hab => by
        rw [hC]
        exact ⟨(f4_short_isRoot a b hab).1, (f4_short_isRoot a b hab).2.1⟩)
    refine ⟨_, fun a b => v • f4ShortSigma a b, 1, f4Short_frame.transport v, Or.inl rfl,
      fun a b hab => ?_, ?_⟩
    · rw [iform_smul]
      exact (f4_short_isRoot a b hab).2.2
    · rw [hi', hroots, IsSLFrame.frameRoots_smul]

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
