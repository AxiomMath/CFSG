module

public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Config
public import CFSG.LocalAnalysis.ComponentClassification.CatFC.KGHS3Lift
public import CFSG.Open.StatedDefs
public import CFSG.Certificates.CosetTableShort
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.ComponentClassification.CatFC.KGHS3

open Subgroup CFSG.Open

theorem hsType_range_of_injective {Y G : Type} [Group Y] [Group G] (f : Y →* G)
    (hf : Function.Injective f) (hY : HSType Y) : HSType ↥f.range := by
  have hker : f.ker ≤ center Y := by
    intro x hx
    have : x = 1 := hf (by simpa using hx)
    rw [this]; exact one_mem _
  obtain ⟨hq, ⟨e⟩⟩ := quasisimple_range_of_ker_le_center hY.1 f hker
  exact ⟨hq, by obtain ⟨g⟩ := hY.2; exact ⟨e.trans g⟩⟩

theorem hsType_map_of_injective {M G : Type} [Group M] [Group G] (f : M →* G)
    (hf : Function.Injective f) (Y : Subgroup M) (hY : HSType ↥Y) : HSType ↥(Y.map f) := by
  have h := hsType_range_of_injective (f.comp Y.subtype) (hf.comp Y.subtype_injective) hY
  have hrange : (f.comp Y.subtype).range = Y.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange] at h
  exact h

theorem exists_hsType_of_quotient {M : Type} [Group M] (C : Subgroup M) [C.Normal]
    (hC : C ≤ center M) {S : Type} [Group S] (e : S ≃* M ⧸ C) (K : Subgroup S)
    (hK : HSType ↥K) : ∃ Y : Subgroup M, HSType ↥Y := by
  have hK' : HSType ↥(K.map e.toMonoidHom) :=
    hsType_map_of_injective e.toMonoidHom e.injective K hK
  obtain ⟨Y, hYq, ⟨f⟩⟩ := exists_quasisimple_lift C hC (K.map e.toMonoidHom) hK'.1
  exact ⟨Y, hYq, by obtain ⟨g⟩ := hK'.2; exact ⟨f.trans g⟩⟩

theorem exists_hsType_of_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    (H : Subgroup (GL ι F)) {S : Type} [Group S] (e : S ≃* StatedProj H) (K : Subgroup S)
    (hK : HSType ↥K) : ∃ Y : Subgroup (GL ι F), Y ≤ H ∧ HSType ↥Y := by
  have hC : (StatedScalars ι F).subgroupOf H ≤ center ↥H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have hx' : (x : GL ι F) ∈ StatedScalars ι F := hx
    have hz : (x : GL ι F) ∈ Subgroup.center (GL ι F) := by
      rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]; exact hx'
    exact Subgroup.mem_center_iff.mp hz g
  obtain ⟨Yh, hYh⟩ := exists_hsType_of_quotient ((StatedScalars ι F).subgroupOf H) hC e K hK
  exact ⟨Yh.map H.subtype, by
    rintro _ ⟨y, _, rfl⟩; exact y.2, hsType_map_of_injective H.subtype H.subtype_injective Yh hYh⟩

end CFSG.ComponentClassification.CatFC.KGHS3
