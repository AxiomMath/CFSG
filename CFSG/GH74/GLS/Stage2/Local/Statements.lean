module

public import CFSG.GH74.GLS.Stage2.Local.Closed
public import CFSG.GH74.GLS.Stage2.Local.Ctx0
public import CFSG.GH74.GLS.Stage2.Local.Prop22
public import CFSG.GH74.GLS.Stage2.Local.Prop22x
public import CFSG.GH74.GLS.Stage2.Local.Lemma23d
public import CFSG.GH74.GLS.Stage2.Local.Lemma23eRes

public section

namespace CFSG.GH74.GLS.Stage2.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12

theorem stage2_local (bg : Stage2Bg) {G : Type} [Group G] [Finite G] {z : G} {k : Kind}
    {S : Subgroup G} (h : Stage2Ctx G z k S) : Stage2Local G z k S where
  data := h.data
  prop21g := bg.ivk_3_1f G z k S h
  prop21h := bg.ivk_3_3 G z k S h
  prop22a := h.prop22a
  prop22x := h.prop22x
  lemma23 := ⟨h.lemma23_abc.1, h.lemma23_abc.2.1, h.lemma23_abc.2.2,
    lemma23_d (bg.ivk_3_3 G z k S h), h.lemma23e⟩
  lemma26 := bg.lemma26 G z k S h
  prop27 := bg.prop27 G z k S h.toCtx0
  lemma29 := bg.lemma29 G z k S h
  lemma31 := fun H J R hH hhyp => bg.lemma31 G z k S h H J R hH hhyp
  prop32 := bg.ivk_8_5 G z k S h
  prop34 := bg.prop34 G z k S h
  lemma35 := fun H J R hC hH hhyp => bg.lemma35 G z k S h H J R hC hH hhyp

end CFSG.GH74.GLS.Stage2.Local
