module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67LyGenTransfer
public import CFSG.Sporadic.Ly.GenSpecBase

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.LyGen

open Subgroup Equiv Equiv.Perm CFSG.Sporadic.Recognition.LyonsSims

theorem sup_eq_top_of_ly
    {Y : Type} [Group Y] (eT : Y ≃* CFSG.Blueprint.NativeSporadic.Ly) {t : Y}
    {ρ : ↥(centralizer ({t} : Set Y)) →* Perm (Fin 11)} (D : LyData Y t ρ)
    {x₁ : ↥(centralizer ({t} : Set Y))} (hx3 : x₁ ^ 3 = 1) (hxρ : ρ x₁ = x1p) :
    centralizer ({t} : Set Y) ⊔ centralizer ({(x₁ : Y)} : Set Y) = ⊤ := by
  obtain ⟨u, hu21, hau, hgen⟩ := CFSG.Sporadic.Ly.exists_gen_pair
  have e1 : Y ≃* CFSG.Sporadic.Ly.J := eT.trans CFSG.Sporadic.Ly.lyEquivJ
  have h1 := @sup_eq_top_of_gen_pair Y CFSG.Sporadic.Ly.J _ _ e1 CFSG.Sporadic.Ly.a u
    CFSG.Sporadic.Ly.orderOf_a hu21 hau hgen
  exact h1 D hx3 hxρ

end CFSG.GH74.GLS.Stage2.Bender.Thm1.LyGen
