module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCF23SocHS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixCore
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsPFBase

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.QuasithinUnique.Id2519.HSAut (outerC)

theorem false_of_hs_fixed
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (e : S ≃* NativeSporadic.Carrier .HS)
    {σ : MulAut S} {P : Subgroup S} (h : CatLeaf.ProperFixedComponent σ P)
    (htype : IsL34Type (P ⧸ Open.fusionZStar P)) : False := by
  let θ : S ≃* hsP := (e : S ≃* NativeSporadic.HS).trans hsPermEquiv
  have hσσ : σ * σ = 1 := MulEquiv.ext fun y => h.1 y
  have hσ2 : MulAut.congr θ σ * MulAut.congr θ σ = 1 := by rw [← map_mul, hσσ, map_one]
  have hσ1 : MulAut.congr θ σ ≠ 1 := fun h1 =>
    h.ne_one ((MulAut.congr θ).injective (by rw [h1, map_one]))
  obtain ⟨r, hr, g, -, x, -, -, hfix⟩ := QuasithinUnique.Id2519.SporHS.fix_data _ hσ2 hσ1
  let Ψ : fixedSubgroup σ ≃*
      ↥(hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850)))) :=
    (Sporadic.HeldB.fixedSubgroupCongr θ σ).trans (QuasithinUnique.Id2519.SporHS.fixEquiv hfix)
  obtain ⟨-, -, -, hrows, -, -, -, hodd⟩ := hs_involution_centralizers
  obtain ⟨hrR, hr2, -, -, hrcard, -⟩ := hrows r hr
  have hd : 20160 ∣ r.centOrder := by
    rw [← hrcard, ← Nat.card_congr Ψ.toEquiv]
    exact (L34PF.dvd_card_of_isL34Type htype).trans (Subgroup.card_dvd_of_le h.2.1)
  rcases QuasithinUnique.Id2519.SporHS.hsRows_cases hr with h1 | ⟨-, -, h1, -⟩ | ⟨hrep, -⟩ | h1
  · rw [h1] at hd
    exact absurd hd (by decide)
  · rw [h1] at hd
    exact absurd hd (by decide)
  swap
  · rw [h1] at hd
    exact absurd hd (by decide)
  have hO : hsP ⊓ centralizer ({tp 3850 r.rep} : Set (Equiv.Perm (Fin 3850))) = outerC := by
    rw [hrep]
    rfl
  have hodd' : pPrimeCore 2 ↥outerC = ⊥ := by
    rw [HeldFix.pPrimeCore_two_eq_oddCore, ← hO]
    exact hodd _ hrR hr2
  let Ψ' : fixedSubgroup σ ≃* ↥outerC := Ψ.trans (MulEquiv.subgroupCongr hO)
  set L := P.subgroupOf (fixedSubgroup σ) with hLdef
  have hL' : IsPComponent 2 (L.map Ψ'.toMonoidHom) :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 Ψ' h.2.2.1
  have hB := HeldFix.isComponent_of_isPComponent hodd' hL'
  have : IsSimpleGroup ↥(commutator ↥outerC) := QuasithinUnique.Id2519.HSAut.commutator_simple'
  have hBle := QuasithinUnique.Id2519.le_commutator_of_isQuasisimple hB.1
  have htop := QuasithinUnique.Id2519.isComponent_eq_top_of_isSimpleGroup
    (CFSG.LocalCores.component_overgroup hB hBle)
  have hBeq : L.map Ψ'.toMonoidHom = commutator ↥outerC :=
    le_antisymm hBle (Subgroup.subgroupOf_eq_top.mp htop)
  let eX : ↥P ≃* ↥(commutator ↥outerC) :=
    (subgroupOfEquivOfLe h.2.1).symm.trans
      ((L.equivMapOfInjective Ψ'.toMonoidHom Ψ'.injective).trans (MulEquiv.subgroupCongr hBeq))
  have : IsSimpleGroup P := eX.isSimpleGroup
  have hZ := L34PF.fusionZStar_eq_bot_of_simple
    (L34PF.nonabelian_of_simple_of_four_dvd
      ((show 4 ∣ 20160 by norm_num).trans (L34PF.dvd_card_of_isL34Type htype)))
    ((show 2 ∣ 20160 by norm_num).trans (L34PF.dvd_card_of_isL34Type htype))
  apply GSThmB.Soc.not_statedClassicalModel_commutator_outerC
  refine CatLeaf.statedClassicalModel_of_lieModel_psl
    (LieType.CurtisTits.lieModel_of_mulEquiv ?_ htype)
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans eX

end CFSG.ComponentClassification.GrSLit.L34Sec5S
