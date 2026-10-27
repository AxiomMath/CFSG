module

public import CFSG.Open.LocalVocabulary
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

theorem pCoreOf_le_pCoreOf_of_le_normalizer (p : ℕ) {X H : Subgroup G} (hXH : X ≤ H)
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) :
    CFSG.Open.pCoreOf p X ≤ CFSG.Open.pCoreOf p H := by
  have hNX : CFSG.Open.pCoreOf p X ≤ X := Subgroup.map_subtype_le _
  have hNH : CFSG.Open.pCoreOf p X ≤ H := hNX.trans hXH
  have hNp : IsPGroup p (CFSG.Open.pCoreOf p X) :=
    (CFSG.pCore_isPGroup (p := p) (G := ↥X)).map X.subtype
  have hHN : H ≤ Subgroup.normalizer (CFSG.Open.pCoreOf p X : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map ((MulAut.conj h).toMonoidHom) ((CFSG.pCore p ↥X).map X.subtype) =
      (CFSG.pCore p ↥X).map X.subtype
    let α : MulAut ↥X := X.normalizerMonoidHom ⟨h, hHX hh⟩
    have hcomp : X.subtype.comp α.toMonoidHom = (MulAut.conj h).toMonoidHom.comp X.subtype := by
      ext y
      simp [α, Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    rw [Subgroup.map_map, ← hcomp, ← Subgroup.map_map]
    rw [(Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (CFSG.pCore p ↥X).Characteristic)) α]
  have hNnorm : ((CFSG.Open.pCoreOf p X).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).mpr hHN
  have hNp' : IsPGroup p ↥((CFSG.Open.pCoreOf p X).subgroupOf H) :=
    hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hcore : (CFSG.Open.pCoreOf p X).subgroupOf H ≤ CFSG.pCore p ↥H := by
    rw [CFSG.pCore_eq_iSup]
    exact le_iSup_of_le ((CFSG.Open.pCoreOf p X).subgroupOf H)
      (le_iSup_of_le hNnorm (le_iSup_of_le hNp' le_rfl))
  rw [← Subgroup.map_subgroupOf_eq_of_le hNH]
  exact Subgroup.map_mono hcore

end CFSG.GroupTheory
