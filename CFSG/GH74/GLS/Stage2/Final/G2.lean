module

public import CFSG.GH74.GLS.Stage2.Final.Sporadic
public import CFSG.GH74.GLS.Stage2.Final.Basic
public import CFSG.GH74.GLS.Stage1.Main.Basic
public import CFSG.GH74.GLS.Stage1.Main.Assembly
public import CFSG.GH74.GLS.Stage1.Thm6.Prod.Resid
public import CFSG.GH74.GLS.Stage12.Branches
public import CFSG.GH74.GLS.Stage2.Final.Named

public section

namespace CFSG.GH74.GLS.Stage2.Final

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage1.Main

theorem isTwoCentralG2Type_of_stage1Out (hmain : Stage2Main) {G : Type} [Group G] [Finite G] {z : G}
    {S : Subgroup G} (hStd : Std G) (h : Stage1Out G z S Kind.g2) :
    ∃ (Gs : Type) (_ : Group Gs), IsTwoCentralG2Type G Gs := by
  have hctx := h.ctxStd hStd
  have hout := hmain G z Kind.g2 S hctx
  have hO : pPrimeCore 2 ↥(Cen z) = ⊥ := hout.oddCore (fun ε h' => by cases h')
  obtain ⟨p, f, hp, hp2, ⟨Gs, iGs, fGs, hL, S', hS'⟩, hone, hsl⟩ : G2Term G z S := by
    cases h with
    | g2 _ t => exact t
  have hSsyl : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ := sylow_top_of_central hctx.central hctx.sylow
  obtain ⟨P, hP⟩ := sylow_of_sylowTop hSsyl
  obtain ⟨e⟩ := hS'
  have hC : HasSL2ProductOfIndexTwoCh6 (oPrimeResidual 2 ↥(Cen z)) (p ^ f) := by
    let eqv := toBarEquiv z hO
    have h1 := hasSL2ProductOfIndexTwoCh6_map eqv.symm hsl
    have h2 : (oPrimeResidual 2 (CentralizerBar z)).map eqv.symm.toMonoidHom =
        oPrimeResidual 2 ↥(Cen z) :=
      CFSG.GH74.GLS.Stage1.Thm6.Prod.map_oPrimeResidual eqv.symm.toMonoidHom eqv.symm.surjective
        Nat.prime_two
    rwa [h2] at h1
  refine ⟨Gs, iGs, Or.inr ⟨p, f, hp, hp2, hL⟩, ⟨P, S', ?_⟩, z, hctx.central, hone, hO,
    Or.inr ⟨p, f, hp, hp2, hL, hC⟩⟩
  exact ⟨(MulEquiv.subgroupCongr hP).trans e⟩

theorem s_stage4_G2_Std_of_stage1 (h1 : Stage1OutThree) (hmain : Stage2Main) : S_stage4_G2_Std := by
  intro G _ _ hStd h3 hT
  obtain ⟨z, S, -, -, hout⟩ := h1 G hStd.toStd0 h3 hT
  exact isTwoCentralG2Type_of_stage1Out hmain hStd hout

end CFSG.GH74.GLS.Stage2.Final
