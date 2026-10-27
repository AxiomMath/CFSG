module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscEnd
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc


section Data

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_orderFour_of_mem_USet (hΩ : HypOmegaGen Ω) {U : Subgroup G} (hU : U ∈ USet Ω) :
    ∃ x ∈ U, orderOf x = 4 := by
  obtain ⟨R, -, J, -, -, -, hcyc, -, h4⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hU
  exact exists_orderOf_eq_four_of_isPGroup_of_isCyclic (Sec6Gen.isPGroup_of_mem_USet hΩ hU) hcyc h4

theorem exists_dataR (hΩ : HypOmegaGen Ω) {K K' : Subgroup G} {z : G} (hK : K ∈ Ω)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K)
    (hperp : KPerp Ω K ≠ twinSet Ω K) :
    ∃ (u : G) (J : Subgroup G) (t : G) (W : Subgroup G), Data Ω K K' z u J t W ∧ u ∈ W ∧
      TwinThmEW.PrintedWT Ω K W := by
  obtain ⟨J, hJ, -⟩ := A7Q.Gen.exists_mem_omegaOfSet_twinSet hΩ hK hz hperp
  obtain ⟨t, ht⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ.1
  obtain ⟨S, R, R', T, hRsyl, hR'syl, hTsyl, hRS, hR'S, hTS, hRR', hRT, hR'T⟩ :=
    A7Q.Gen.exists_twinSylow hΩ hK hz hK' hne hJ
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨η, hη, hηinv⟩ := Sec6Gen.exists_invariant_mem_etaSet hΩ S
  have hWmem : (⨆ U ∈ η, U : Subgroup G) ∈ WSet Ω := ⟨η, ⟨S, hη, hηinv⟩, rfl⟩
  have hWS : (⨆ U ∈ η, U : Subgroup G) ≤ (S : Subgroup G) := iSup₂_le fun U hU => (hη.1 hU).2
  have hzW := Hat2A7S.exists_mem_eta_of_sylow hΩ hη hK hz hRsyl hRS
  have htW := Hat2A7S.exists_mem_eta_of_sylow hΩ hη hJ.1 ht hTsyl hTS
  have hWn : ∀ s ∈ (S : Subgroup G), conjSub s (⨆ U ∈ η, U : Subgroup G) = ⨆ U ∈ η, U :=
    fun s hs => T7A.conjSub_eta_eq hηinv hs
  set W : Subgroup G := ⨆ U ∈ η, U with hWdef
  have hKW : K ⊓ W ∈ USet Ω := TwinThmEW.inf_W_mem_USet' hΩ hWmem hWS hK
    (mem_RSet_of_isSylow2In hK hRsyl) hRsyl.1 hRS
  have hK'W : K' ⊓ W ∈ USet Ω := TwinThmEW.inf_W_mem_USet' hΩ hWmem hWS hK'Ω
    (mem_RSet_of_isSylow2In hK'Ω hR'syl) hR'syl.1 hR'S
  obtain ⟨u₁, hu₁, hu₁4⟩ := exists_orderFour_of_mem_USet hΩ hKW
  obtain ⟨u₂, hu₂, hu₂4⟩ := exists_orderFour_of_mem_USet hΩ hK'W
  have hu₁K : u₁ ∈ K := hu₁.1
  have hu₂K' : u₂ ∈ K' := hu₂.1
  have hsq₁ : u₁ * u₁ = z := T7A.sq_eq_of_orderOf_four hz hu₁K hu₁4
  have hsq₂ : u₂ * u₂ = z := T7A.sq_eq_of_orderOf_four hzK' hu₂K' hu₂4
  have hc : u₁ * u₂ = u₂ * u₁ := wSet_comm hΩ hWmem u₁ hu₁.2 u₂ hu₂.2
  have hu₁K' : u₁ ∉ K' := fun h => hne (eq_of_mem_inf_of_four_dvd hΩ hK hK'Ω hu₁K h
    (by rw [hu₁4])).symm
  have hu₂K : u₂ ∉ K := fun h => hne (eq_of_mem_inf_of_four_dvd hΩ hK hK'Ω h hu₂K'
    (by rw [hu₂4])).symm
  have hu2 : (u₁ * u₂) * (u₁ * u₂) = 1 := by
    calc (u₁ * u₂) * (u₁ * u₂) = u₁ * (u₂ * u₁) * u₂ := by group
      _ = u₁ * (u₁ * u₂) * u₂ := by rw [← hc]
      _ = (u₁ * u₁) * (u₂ * u₂) := by group
      _ = 1 := by rw [hsq₁, hsq₂, hz.sq]
  have hu1 : u₁ * u₂ ≠ 1 := by
    intro h
    apply hu₁K'
    have : u₁ = u₂⁻¹ := by rw [eq_inv_iff_mul_eq_one]; exact h
    rw [this]
    exact K'.inv_mem hu₂K'
  have huz : u₁ * u₂ ≠ z := by
    intro h
    apply hu₁K'
    have : u₁ = z * u₂⁻¹ := by rw [← h]; group
    rw [this]
    exact K'.mul_mem hzK'.mem (K'.inv_mem hu₂K')
  have huW : u₁ * u₂ ∈ W := W.mul_mem hu₁.2 hu₂.2
  have hfr : TwinFrameData Ω K K' z (u₁ * u₂) J t :=
    { mem := hK
      hz := hz
      hK' := hK'
      hne := hne
      hu := Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₁K) (Subgroup.mem_sup_right hu₂K')
      hu2 := hu2
      hu1 := hu1
      huz := huz
      hJ := hJ
      ht := ht
      htu := wSet_comm hΩ hWmem t htW (u₁ * u₂) huW }
  exact ⟨u₁ * u₂, J, t, W, ⟨hfr, hWmem, hzW, htW⟩, huW,
    ⟨S, R, hRsyl, hRS, hWmem, hWS, hWn, K', hK', hne, R', mem_RSet_of_isSylow2In hK'Ω hR'syl,
      hR'syl.1, hR'S⟩⟩

end Data

section Main

variable {r n : ℕ}

theorem twinCoreDiscPerpR_of_inputsR (I : TwinDiscInputsR r n) : TwinCoreDiscPerpR r n := by
  intro Y _ _ R S t h hdisc hperp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := CoreAssembly.mem_conjClass_self _
  have hz : IsUniqueInvolution (tightCore R) t := Q8Datum.isUniqueInvolution_core h.datum
  obtain ⟨K', hK', hne'⟩ := h.twin
  obtain ⟨u, J, t', W, d, huW, hP⟩ := exists_dataR h.hyp hK hz hK' hne' hperp
  exact false_of_settingR I h ⟨h.toStd, hdisc, d, huW⟩ hP

end Main

end CFSG.CGT.PushingUpLit.SolKNA.R4
