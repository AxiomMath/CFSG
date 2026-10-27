module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Setup
public import CFSG.LocalAnalysis.EvenBN.GMSK.LayerRankOne
public import CFSG.LocalAnalysis.SteinbergBVSp6DirectSimpleLayer

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

variable {B : Type} [Group B] [Finite B] {e t : B} {J₀ E₂ : Subgroup B} [(zpowers e).Normal]

abbrev Rq (e : B) [(zpowers e).Normal] : Subgroup (B ⧸ zpowers e) :=
  CFSG.pPrimeCore 2 (B ⧸ zpowers e)

abbrev Xq (e : B) [(zpowers e).Normal] : Type := (B ⧸ zpowers e) ⧸ Rq e

abbrev θq (e : B) [(zpowers e).Normal] : (B ⧸ zpowers e) →* Xq e := QuotientGroup.mk' (Rq e)

abbrev π₁q (e : B) [(zpowers e).Normal] : B →* (B ⧸ zpowers e) := QuotientGroup.mk' (zpowers e)

noncomputable abbrev π₂q (e : B) [(zpowers e).Normal] : B →* Xq e := (θq e).comp (π₁q e)

structure LayerOut (e t : B) (J₀ : Subgroup B) [(zpowers e).Normal] : Prop where
  injOn_J : Set.InjOn (θq e) (J₀.map (π₁q e))
  injOn_two : ∀ P : Subgroup (B ⧸ zpowers e), IsPGroup 2 P → Set.InjOn (θq e) P
  R_abelian : IsMulCommutative (Rq e)
  kGroup : CFSG.SectionRank.IsKGroupCat (Xq e)
  oddCore : CFSG.pPrimeCore 2 (Xq e) = ⊥
  inf_eq : zpowers (θq e (π₁q e t)) ⊓ (J₀.map (π₁q e)).map (θq e) = ⊥
  sup_eq : zpowers (θq e (π₁q e t)) ⊔ (J₀.map (π₁q e)).map (θq e) =
    centralizer ({θq e (π₁q e t)} : Set (Xq e))
  sylow : ∀ S : Sylow 2 (Xq e), θq e (π₁q e t) ∈ S → ∃ s ∈ S, s * θq e (π₁q e t) ≠ θq e (π₁q e t) * s
  standard : CFSG.IsStandardSubgroup ((J₀.map (π₁q e)).map (θq e))
  conclusion : SteinbergBV.OneOrTwoLayerConclusion ((J₀.map (π₁q e)).map (θq e)) (θq e (π₁q e t))
  center_Q : (center (normalClosure ((J₀.map (π₁q e) : Subgroup (B ⧸ zpowers e)) :
      Set (B ⧸ zpowers e)))).map
      (normalClosure ((J₀.map (π₁q e) : Subgroup (B ⧸ zpowers e)) : Set (B ⧸ zpowers e))).subtype =
    normalClosure ((J₀.map (π₁q e) : Subgroup (B ⧸ zpowers e)) : Set (B ⧸ zpowers e)) ⊓ Rq e
  centralizer_Q : centralizer (normalClosure ((J₀.map (π₁q e) : Subgroup (B ⧸ zpowers e)) :
      Set (B ⧸ zpowers e)) : Set (B ⧸ zpowers e)) = Rq e
  map_Q : (normalClosure ((J₀.map (π₁q e) : Subgroup (B ⧸ zpowers e)) :
      Set (B ⧸ zpowers e))).map (θq e) =
    normalClosure (((J₀.map (π₁q e)).map (θq e) : Subgroup (Xq e)) : Set (Xq e))
  odd_Q_inf_R : Odd (Nat.card (normalClosure ((J₀.map (π₁q e) : Subgroup (B ⧸ zpowers e)) :
      Set (B ⧸ zpowers e)) ⊓ Rq e : Subgroup (B ⧸ zpowers e)))

theorem GomiU42Setup.layerOut (h : GomiU42Setup B e t J₀ E₂) : LayerOut e t J₀ := by
  have hL := CFSG.LocalAnalysis.SteinbergBV.direct_simple_involution_centralizer_layer_of
    CFSG.LocalAnalysis.EvenBN.GMSK.nonnormalInvolutionComponentLayerStmt
    (B ⧸ zpowers e) h.isKGroupCat_F (J₀.map (QuotientGroup.mk' (zpowers e)))
    h.isSimpleGroup_Jb h.nonabelian_Jb h.exists_four_group (QuotientGroup.mk' (zpowers e) t)
    h.orderOf_mk_t (by rw [h.centralizer_bar_eq]; exact le_sup_right) h.inf_bar_eq_bot
    h.centralizer_bar_eq.symm h.sylow_not_central
  dsimp only at hL
  obtain ⟨⟨hRab, hinv, hRC⟩, ⟨hinjJ, hinjC, hinjP⟩, ⟨hK, hKP, hO⟩, ⟨hJc, hJi, hJs⟩, hsyl,
    ⟨hstd, hidx, hconj, hnn⟩, hlayer, ⟨hcent, hJR⟩, ⟨hQn, hQp, hQmap, hQcomap, hQcc, hQcent, he⟩,
    ⟨hodd, hinvQ⟩, hpc, hfit⟩ := hL
  exact ⟨hinjJ, hinjP, hRab, hK, hO, hJi, hJs, hsyl, hstd, hlayer, hQcc, hQcent, hQmap, hodd⟩

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
