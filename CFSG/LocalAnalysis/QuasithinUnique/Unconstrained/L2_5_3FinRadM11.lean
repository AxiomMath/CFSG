module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadList
public import CFSG.Sporadic.Schreier.M11
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadList
public meta import CFSG.Sporadic.Schreier.M11
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadM11Inputs
public import Certificates.Certificate4054
public import Certificates.Certificate2191
public import Certificates.Certificate2192
public import Certificates.Certificate3120
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public meta import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadical
public meta import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_3FinRadical
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public meta import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public meta import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public meta import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public meta import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.LocalAnalysis.SectionRank.TitsCover
public meta import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3ComponentsAmbient
public meta import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.Quasithin.Background.A3Structure39Aut
public meta import CFSG.Quasithin.Background.A3Structure39Aut
public import CFSG.Sporadic.J4.Simple
public meta import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public meta import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M12
public meta import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Mathieu.M24
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public meta import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
public meta import Certificates.Certificate43

public section

namespace CFSG.QuasithinUnique.Fin253

open CFSG.Sporadic.Schreier CFSG.Blueprint

abbrev M11G : Type := ↥NativeSporadic.M11

@[expose] def m11Model : ListModel M11G (Equiv.Perm (Fin 11)) where
  enc := fun x => (x : Equiv.Perm (Fin 11))
  inj := Subtype.val_injective
  mul := m11mul
  one := 1
  inv := m11inv
  enc_mul := fun x y => (tab_eq _).symm
  enc_one := rfl
  enc_inv := fun x => (tab_eq _).symm
  elems := m11Elements
  mem_elems := fun y => by
    rw [mem_m11Elements]
    exact ⟨fun h => ⟨⟨y, h⟩, rfl⟩, fun ⟨x, hx⟩ => hx ▸ x.2⟩

theorem m11_hcenter_raw : CenterOK m11mul 1 m11Elements :=
  Certificates.certificate4054.1

theorem m11_hodd_raw :
    OddOK m11mul 1 495 m11Elements m11Invs m11Ord4 :=
  Certificates.certificate4054.2.1

theorem m11_hquat_raw : QuatAll m11mul 1 m11Elements m11Invs :=
  Certificates.certificate4054.2.2.1

theorem m11_hcore_raw :
    CoreAll m11mul 1 m11inv m11Elements m11Invs :=
  Certificates.certificate4054.2.2.2

theorem m11_hcenter : CenterOK m11Model.mul m11Model.one m11Model.elems := by
  simp only [m11Model]
  exact m11_hcenter_raw

theorem m11_hodd :
    OddOK m11Model.mul m11Model.one 495 m11Model.elems m11Invs m11Ord4 := by
  simp only [m11Model]
  exact m11_hodd_raw

theorem m11_hquat : QuatAll m11Model.mul m11Model.one m11Model.elems m11Invs := by
  simp only [m11Model]
  exact m11_hquat_raw

theorem m11_hcore :
    CoreAll m11Model.mul m11Model.one m11Model.inv m11Model.elems m11Invs := by
  simp only [m11Model]
  exact m11_hcore_raw

theorem radData_of_equiv_m11 {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11) : RadData Y := by
  have hS : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M11) :=
    (CFSG.Sporadic.Mathieu.fam_m11_simplicity).2.2
  have hcard : Nat.card Y = 16 * 495 := by
    rw [Nat.card_congr e.toEquiv]
    exact m11_card
  refine radData_of_listModel_equiv m11Model e e.isSimpleGroup (m := 495)
    (by decide) (by norm_num) hcard m11Invs m11Ord4 ?_ ?_ m11_hcenter m11_hodd m11_hquat m11_hcore
  · intro t
    simp only [m11Model, m11Invs, List.mem_filter, decide_eq_true_eq]
  · intro u
    simp only [m11Model, m11Ord4, List.mem_filter, decide_eq_true_eq]

end CFSG.QuasithinUnique.Fin253
