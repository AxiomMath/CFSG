module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FSp4Kind
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87U42Idx
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell
public import CFSG.GH74.GLS.IVK.Proofs2.NoOuter
public import CFSG.GH74.GLS.IVK.Proofs2.TwoTori
public import CFSG.GH74.GLS.Stage2.Local.Prop27Cfg

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem outAbelian_of_FSp4 {Y : Type} [Group Y] (h : FSp4 Y) : OutAbelian Y := by
  obtain ⟨p, f, hp, hf, hp2, hlie⟩ := h
  obtain ⟨-, F, iF, fF, hcard, ⟨e⟩⟩ := CFSG.GH74.GLS.Stage2.Final.lieModel_psp_unpack hlie
  exact outAbelian_of_mulEquiv e.symm (outAbelian_psp4 (ringChar_ne_two_of_card_psp4 hp hp2 hcard))

@[expose] def PSp4Core : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], FSp4 Y → ∀ α : MulAut Y, α * α = 1 → α ≠ 1 →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ X : Subgroup Y, IsPGroup p ↥X → X ≠ ⊥ →
      Subgroup.closure ((fun x : Y => x * (α x)⁻¹) '' (X : Set Y)) = X →
      fixSub α ≤ normalizer (X : Set Y) → False

theorem cell87_FSp4 (hInv : InvSec) (hCore : PSp4Core) : Cell87 FSp4 := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hF
  classical
  exfalso
  by_cases hZ : center ↥(layer (Sec H₀ H₁)) = ⊥
  swap
  · exact not_kindFactorAll_of_FSp4 minIndexU42 hF k (layerBar_kindFactor hInv hctx hsig hyp hZ)
  have hd := CellData.of_ctx hctx hsig hyp
  have hzb2 := hd.z2
  set zb : Sec H₀ H₁ := zSec z H₀ hz H₁ with hzb
  set K : Subgroup (Sec H₀ H₁) := layer (Sec H₀ H₁) with hK
  have hKn : K.Normal := layer_normal
  have hq : IsQuasisimple ↥K := hd.quasi
  let eq0 : (↥K ⧸ center ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hFK' : FSp4 ↥K := FSp4.of_mulEquiv eq0 hF
  have hOut : OutAbelian ↥K := outAbelian_of_FSp4 hFK'
  have hXK : X ≤ K :=
    x_le_layer_of_comm hzb2 hsig.A hsig.op hd.gen fun x _ => comm_mem_sup_centralizer K hOut x zb
  let α : MulAut ↥K := layerAut zb
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun s => ?_
    show α (α s) = s
    exact layerAut_layerAut hzb2 s
  have hα1 : α ≠ 1 := by
    intro h1
    obtain ⟨k0, hk0, hne⟩ := hd.exists_not_commute
    apply hne
    have h3 : α ⟨k0, hk0⟩ = ⟨k0, hk0⟩ := by rw [h1]; rfl
    have h2' := congrArg Subtype.val h3
    have h2 : zb * k0 * zb⁻¹ = k0 := by
      rw [show ((α ⟨k0, hk0⟩ : ↥K) : Sec H₀ H₁) = zb * k0 * zb⁻¹ from coe_layerAut zb _] at h2'
      exact h2'
    calc zb * k0 = zb * k0 * zb⁻¹ * zb := by group
      _ = k0 * zb := by rw [h2]
  have hfixC : ∀ y ∈ fixSub α, (y : Sec H₀ H₁) ∈ centralizer ({zb} : Set (Sec H₀ H₁)) := by
    intro y hy
    have h1 : α y = y := hy
    have h2 := congrArg Subtype.val h1
    rw [show ((α y : ↥K) : Sec H₀ H₁) = zb * y * zb⁻¹ from coe_layerAut zb y] at h2
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (y : Sec H₀ H₁) * zb = (zb * y * zb⁻¹) * zb := by rw [h2]
      _ = zb * y := by group
  have : Fact p.Prime := ⟨hsig.A.prime⟩
  let XT : Subgroup ↥K := X.subgroupOf K
  have hXp : IsPGroup p ↥XT := hsig.A.pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hXK).symm
  have hXne : XT ≠ ⊥ := by
    intro h
    apply hsig.A.ne_bot
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hXK hx⟩ : ↥K) ∈ XT := hx
    rw [h] at h1
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp h1))
  have hN : fixSub α ≤ normalizer (XT : Set ↥K) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hyN : (y : Sec H₀ H₁) ∈ normalizer (X : Set (Sec H₀ H₁)) :=
      hsig.A.inv _ (Subgroup.mem_top _) (hfixC y hy)
    exact Subgroup.mem_normalizer_iff.mp hyN (x : Sec H₀ H₁)
  have hzN : zb ∈ normalizer (X : Set (Sec H₀ H₁)) := z_mem_normalizer_of_sig4A hsig.A
  have hcomm : Subgroup.closure ((fun x : ↥K => x * (α x)⁻¹) '' (XT : Set ↥K)) = XT := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      have hxA : (x : Sec H₀ H₁) ∈ X := hx
      have hαx : ((α x : ↥K) : Sec H₀ H₁) ∈ X := by
        rw [coe_layerAut]
        exact (Subgroup.mem_normalizer_iff.mp hzN _).mp hxA
      exact XT.mul_mem hx (XT.inv_mem hαx)
    · set T : Subgroup ↥K := Subgroup.closure ((fun x : ↥K => x * (α x)⁻¹) '' (XT : Set ↥K)) with hT
      have hX : X ≤ T.map K.subtype := by
        rw [← hsig.A.comm, Subgroup.commutator_le]
        intro x hx g hg
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        have hz2' : zb ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hzb2
        rcases Int.even_or_odd' n with ⟨m, rfl | rfl⟩
        · rw [zpow_mul, hz2', one_zpow, commutatorElement_one_right]
          exact Subgroup.one_mem _
        · rw [zpow_add_one, zpow_mul, hz2', one_zpow, one_mul]
          have hxT : (⟨x, hXK hx⟩ : ↥K) ∈ XT := hx
          refine ⟨(⟨x, hXK hx⟩ : ↥K) * (α ⟨x, hXK hx⟩)⁻¹,
            Subgroup.subset_closure ⟨⟨x, hXK hx⟩, hxT, rfl⟩, ?_⟩
          have hcoe : ((α ⟨x, hXK hx⟩ : ↥K) : Sec H₀ H₁) = zb * x * zb⁻¹ :=
            coe_layerAut zb ⟨x, hXK hx⟩
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype]
          rw [hcoe, commutatorElement_def, ← hzb]
          group
      intro y hy
      have hyX : (y : Sec H₀ H₁) ∈ X := hy
      obtain ⟨t, ht, hty⟩ := hX hyX
      have : t = y := Subtype.ext hty
      rw [← this]
      exact ht
  exact hCore ↥K hFK' α hα2 hα1 p hsig.A.odd XT hXp hXne hcomm hN

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
