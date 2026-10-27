module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeafQuasi
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmallMain

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.Blueprint
  CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ClassicalInvolution.McLData CFSG.ClassicalInvolution.McLProof
open CFSG.CGT.PushingUpLit.SolKNA.R4 CFSG.CGT.PushingUpLit.SolKNA.R4.TwinSmall


theorem outTwoCyclic_mcl : Nobq.OutTwoCyclic NativeSporadic.McL :=
  Nobq.OutTwoCyclic.of_card_le_two CFSG.Sporadic.Schreier.McL_outer_card_le_two.1

theorem not_twinPair_mcl {F : Type} [Group F] (h : NativeSporadic.IsSporadic F .McL) :
    ¬ TwinPair F := by
  obtain ⟨e₀⟩ := h
  have e₁ : F ≃* NativeSporadic.McL := e₀
  have e : TLGrpEquiv F ↥P := e₁.trans mclEquivP
  have hP : Nat.card P = 898128000 := card_P
  have : Finite ↥P := inferInstance
  have hpa : orderOf (⟨pa, pa_mem⟩ : ↥P) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_pa
  have hS2 : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [card_S]; norm_num)
  have hmap : (Subgroup.centralizer ({(⟨pa, pa_mem⟩ : ↥P)} : Set ↥P)).map P.subtype = K := by
    rw [CFSG.Sporadic.Schreier.map_centralizer_subtype P ⟨pa, pa_mem⟩]
    exact centralizerIn_P hP
  have e₀' : TLGrpEquiv ↥(Subgroup.centralizer ({(⟨pa, pa_mem⟩ : ↥P)} : Set ↥P)) ↥K :=
    (Subgroup.equivMapOfInjective _ P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have hcov : ∀ z : ↥P, orderOf z = 2 → ∃ c : ↥P, c * ⟨pa, pa_mem⟩ * c⁻¹ = z := fun z hz => by
    obtain ⟨c, hc, hcz⟩ := cover_of_sylow P S hS2 (S_index_odd hP) pa cover_S (z : _) z.2
      (by rw [Subgroup.orderOf_coe]; exact hz)
    exact ⟨⟨c, hc⟩, Subtype.ext hcz.symm⟩
  exact not_twinPair_of_quasi (G := ↥P) e ⟨pa, pa_mem⟩ hpa e₀' K_quasisimple.1
    card_center_K hcov


theorem twinLeafR_mcl {r n : ℕ} (hr : 4 ≤ r) :
    TwinLeafR r n fun F _ => NativeSporadic.IsSporadic F .McL := by
  intro Y _ _ R S t hP _ hF
  haveI := hP.core.simple
  obtain ⟨e⟩ := hF
  have hcomm : SocleComm2 ↥(genFittingFStar Y) :=
    socleComm2_of_outTwoCyclic (Nobq.OutTwoCyclic.of_mulEquiv e outTwoCyclic_mcl)
  exact not_twinPair_mcl ⟨e⟩ (exists_twinPair_of_perp hr hP hcomm)

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
