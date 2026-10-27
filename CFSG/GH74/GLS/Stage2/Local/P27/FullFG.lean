module

public import CFSG.GH74.GLS.Stage2.Local.P27.FullG

public section

namespace CFSG.GH74.GLS.Stage2.Local.P27

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12
  CFSG.GH74.GLS.Stage2.Local

variable {G : Type} [Group G] [Finite G]

theorem fullF_of_T1 {z x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hx2 : orderOf x = 2)
    (hZ : Subgroup.center (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = ⊥)
    (hOut : OutAbel (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))) (hT1 : FullFT1 z x T) : FullF z x T := by
  obtain ⟨T₁, h1, h2, h3, h4, h5, h6⟩ := hT1
  have hE := S45.fullE_of_T1 hT hx2 hZ ⟨T₁, h1, h2, h3, h6⟩
  exact ⟨fullF_res hT hOut hE.1, T₁, h1, h2, h3, h4, h5, h6⟩

theorem fullG_of_T1 {z x : G} {T : Subgroup G}
    (hT : IsSylowOf 2 T (centralizer ({x} : Set G))) (hx2 : orderOf x = 2)
    (hZ : Subgroup.center (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = ⊥)
    (hOut : OutAbel (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))) (hT1 : FullFT1 z x T)
    (hD₂ : IsDihedral ↥(T ⊓ Jx x)) : FullG x := by
  have hF := fullF_of_T1 hT hx2 hZ hOut hT1
  obtain ⟨T₁, h1, h2, h3, h4, -, h6⟩ := hT1
  exact fullG_of_data hT hx2 hF.res ⟨T₁, h1, h2, h3, h4, h6⟩ hD₂

theorem fullF_of_datum {z x t' : G} {T D₁ D₂ U : Subgroup G} {q n : ℕ} (hcfg : Cfg z x T q)
    (hsyl : Syl z x T D₁ D₂ U n t') (hex : Extra z x T D₁ D₂ U t')
    (hZ : Subgroup.center (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = ⊥)
    (hOut : OutAbel (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))) : FullF z x T :=
  fullF_of_T1 hcfg.T_syl hcfg.x_nc.1 hZ hOut (fullFT1_of_extra hsyl hex)

theorem fullG_of_datum {z x t' : G} {T D₁ D₂ U : Subgroup G} {q n : ℕ} (hcfg : Cfg z x T q)
    (hsyl : Syl z x T D₁ D₂ U n t') (hex : Extra z x T D₁ D₂ U t')
    (hZ : Subgroup.center (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x)) = ⊥)
    (hOut : OutAbel (↥(Jx x) ⧸ pPrimeCore 2 ↥(Jx x))) : FullG x :=
  fullG_of_T1 hcfg.T_syl hcfg.x_nc.1 hZ hOut (fullFT1_of_extra hsyl hex)
    (hex.T_inf_J ▸ ⟨2 ^ n, hsyl.D₂_dih.2⟩)

end CFSG.GH74.GLS.Stage2.Local.P27
