module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs123
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnOrthMark
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactD
import CFSG.Blueprint.SourceClassicalTransportOrthogonal
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I167

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA

theorem i167COrth_catalogIs_plus {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .POmegaPlus n 2 f) : catalogIs S (isOmPA n (2 ^ f)) := by
  obtain ⟨q, hv, hqp, hqf, ⟨e⟩⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact.exists_D_of_statedClassicalModel_POmegaPlus h
  refine ⟨TauCeti.CFSGIndex.lie ⟨.D n q, hv⟩,
    Or.inl (show n = n ∧ q.card = 2 ^ f from ⟨rfl, ?_⟩), ⟨e⟩⟩
  rw [TauCeti.PrimePower.card_def, hqp, hqf]

private theorem i167COrth_catalogIs_minus_aux1 {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus n 2 f) : catalogIs S (isOmMA n (2 ^ f)) := by
  obtain ⟨hadm, K, hfield, hfinite, hK, b, c, hirr, ⟨θ⟩⟩ := h
  let _ := hfield
  let _ := hfinite
  obtain ⟨hp, hf, hn⟩ := hadm
  let q : TauCeti.PrimePower := ⟨2, f, hp, by omega⟩
  have hv : (TauCeti.LieTypeIndex.twistedD n q).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    exact ⟨hn, not_false⟩
  obtain ⟨b₀, c₀, hirr₀, ⟨eT⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      n q hv
  obtain ⟨φ⟩ := CFSG.ClassicalModels.nonempty_ringEquiv_validIndex_fixedField
    ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩ K (by
      simp [TauCeti.ValidLieTypeIndex.fieldOrder, q, hK])
  have _ : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField
      ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  obtain ⟨e2⟩ := CFSG.Blueprint.EvenSource.nonempty_statedOmegaMinus_equiv (n := n) (by omega)
    (CFSG.ClassicalInvolution.Upgrade.irreducible_map φ hirr) hirr₀
  let e1 := CFSG.Adapters.RankTwoModelTransports.statedProjCongr
    (CFSG.Adapters.RankTwoModelTransports.glCongr φ)
    (CFSG.ClassicalInvolution.Upgrade.map_statedOmega φ
      (CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp (n := n) (b := b) (c := c) φ rfl
        rfl))
    (CFSG.Adapters.RankTwoModelTransports.glCongr_statedScalars φ)
  exact ⟨TauCeti.CFSGIndex.lie ⟨TauCeti.LieTypeIndex.twistedD n q, hv⟩,
    Or.inl (show n = n ∧ q.card = 2 ^ f from ⟨rfl, by rw [TauCeti.PrimePower.card_def]⟩),
    ⟨((θ.trans e1).trans e2).trans eT.symm⟩⟩

theorem i167COrth_catalogIs_minus {S : Type} [Group S] {n f : ℕ}
    (h : StatedClassicalModel S .POmegaMinus n 2 f) : catalogIs S (isOmMA n (2 ^ f)) := by
  exact i167COrth_catalogIs_minus_aux1 h

theorem i167COrth_admissible_plus {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel G .POmegaPlus n 2 f) : 1 ≤ f ∧ 4 ≤ n := by
  obtain ⟨⟨-, hf, hn⟩, -⟩ := h
  exact ⟨hf, hn⟩

theorem i167COrth_admissible_minus {G : Type} [Group G] {n f : ℕ}
    (h : StatedClassicalModel G .POmegaMinus n 2 f) : 1 ≤ f ∧ 4 ≤ n := by
  obtain ⟨⟨-, hf, hn⟩, -⟩ := h
  exact ⟨hf, hn⟩

theorem i167COrth_catalog_of_innDiag {S : Type} [Group S] [Finite S] {labK : GLALabel} {α : MulAut S}
    (hZ : Subgroup.center S = ⊥) (hFam : Y10GField.FamOrth labK) (hInn : Y10GField.InnDiagKind S labK α) :
    4 ≤ labK.rank ∧ 1 ≤ (canonLabel labK).n ∧
      (catalogIs S (isOmPA labK.rank (2 ^ (canonLabel labK).n)) ∨
        catalogIs S (isOmMA labK.rank (2 ^ (canonLabel labK).n))) := by
  obtain ⟨hmod | hmod, -⟩ := Y10GInnOrthMark.innDiagKind_orth_data hZ hFam hInn
  · obtain ⟨hf, hn⟩ := i167COrth_admissible_plus hmod
    exact ⟨hn, hf, Or.inl (i167COrth_catalogIs_plus hmod)⟩
  · obtain ⟨hf, hn⟩ := i167COrth_admissible_minus hmod
    exact ⟨hn, hf, Or.inr (i167COrth_catalogIs_minus hmod)⟩

end CFSG.LocalAnalysis.GLTheoremA.I167

end
