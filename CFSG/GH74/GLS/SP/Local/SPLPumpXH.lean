module

public import CFSG.GH74.GLS.SP.Local.SPLPumpXG
public import CFSG.GH74.GLS.SP.Local.SPLPumpXB

public section

namespace CFSG.GH74.GLS.SP.Local

open Subgroup CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem splPumpX_of_shapes
    (hG : Generic.GenericKnownFacts) (hF : E2.E2ComponentFacts)
    (hUI : StableUniqueInvolution) (hAlt : StableDoubleCoverAlt) (hL34 : StableL34Cover)
    (hOUI : OtherUniqueInvolution) (hDiag : DiagonalImpossible) : SPLPumpX := by
  intro G _ _ hKP q z t I F₀ S
  obtain ⟨T₁, hX⟩ := S.xctx
  have hs : orderOf (⟨z, S.z_mem_Y⟩ : ↥(centralizer ({t} : Set G))) = 2 :=
    orderOf_mk_centralizer S.z_mem_Y S.z_ord
  have hΛC := le_centralizer_mk (isPCompIn_two_iff.mp S.I_comp).1 S.z_mem_Y
  have hΛ := isTwoComponent_centralizer_mk S.I_comp S.z_mem_Y
  obtain ⟨-, -, L, hL, hcases, -, -, -⟩ := pumpupY_structure hs hΛC hΛ
  have hcomp : ∀ K : Subgroup (barQ ↥(centralizer ({t} : Set G))), IsComponent K → K ≤ barT t I :=
    hX.component_le hG hF hUI hAlt hL34 hOUI hDiag S.comp hL hcases
  refine sSup_le fun K hK => ?_
  have hKc : IsComponent ((K.subgroupOf (centralizer ({t} : Set G))).map
      (barMk ↥(centralizer ({t} : Set G)))) :=
    isComponent_map_barMk (isPCompIn_two_iff.mp hK).2
  have hle := hcomp _ hKc
  intro k hk
  have hkY : k ∈ centralizer ({t} : Set G) := hK.1 hk
  obtain ⟨i, hi, hik⟩ := hle ⟨⟨k, hkY⟩, hk, rfl⟩
  have hker : (⟨k, hkY⟩ : ↥(centralizer ({t} : Set G))) * i⁻¹ ∈
      pPrimeCore 2 ↥(centralizer ({t} : Set G)) := by
    rw [← QuotientGroup.eq_one_iff]
    show barMk ↥(centralizer ({t} : Set G)) ((⟨k, hkY⟩ : ↥(centralizer ({t} : Set G))) * i⁻¹) = 1
    rw [map_mul, map_inv, hik, mul_inv_cancel]
  have hk' : k = (((⟨k, hkY⟩ : ↥(centralizer ({t} : Set G))) * i⁻¹ : ↥(centralizer ({t} : Set G))) : G) *
      (i : G) := by simp
  rw [hk']
  exact mul_mem_sup ⟨_, hker, rfl⟩ hi

end CFSG.GH74.GLS.SP.Local
