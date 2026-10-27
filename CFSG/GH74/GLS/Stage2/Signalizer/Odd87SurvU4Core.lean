module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FU4ThreeData
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Out
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87SurvU4Comm

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.PerfectAutomorphisms (onCenterQuotient onCenterQuotient_apply_mk)
open scoped commutatorElement

@[expose] def U4SurvCore : Prop :=
  ∀ (p₀ f₀ : ℕ) (K : Type) [Field K] [Finite K] (h : UnitaryFieldData p₀ f₀ K),
    p₀.Prime → p₀ ≠ 2 → p₀ ^ f₀ % 8 ≠ 7 →
    ∀ α : MulAut (hypPSU h 2 0), α * α = 1 → SurvU4Orth h α →
      ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
        ∀ X : Subgroup (hypPSU h 2 0), IsPGroup p ↥X → X ≠ ⊥ →
          Subgroup.closure ((fun x => x * (α x)⁻¹) '' (X : Set (hypPSU h 2 0))) = X →
          fixSub α ≤ normalizer (X : Set (hypPSU h 2 0)) → False

theorem cell87Surv_FU4 (hCore : U4SurvCore) : Cell87Surv FU4 := by
  intro _ _ G _ _ z k S hctx H₀ H₁ _ hz p X hsig hyp hZ hF hnk
  classical
  exfalso
  have hd := CellData.of_ctx hctx hsig hyp
  have hzb2 := hd.z2
  set zb : Sec H₀ H₁ := zSec z H₀ hz H₁ with hzb
  set K : Subgroup (Sec H₀ H₁) := layer (Sec H₀ H₁) with hK
  have hKn : K.Normal := layer_normal
  let α : MulAut ↥K := layerAut zb
  have hα2 : α * α = 1 := by
    refine MulEquiv.ext fun s => ?_
    show α (α s) = s
    exact layerAut_layerAut hzb2 s
  have hαY2 : onCenterQuotient α * onCenterQuotient α = 1 := by
    refine MulEquiv.ext fun s => ?_
    obtain ⟨s₀, rfl⟩ := QuotientGroup.mk_surjective s
    show onCenterQuotient α (onCenterQuotient α (QuotientGroup.mk s₀)) = QuotientGroup.mk s₀
    have e1 := onCenterQuotient_apply_mk α s₀
    have e2 := onCenterQuotient_apply_mk α (α s₀)
    simp only [QuotientGroup.mk'_apply] at e1 e2
    rw [e1, e2]
    have : α (α s₀) = s₀ := congrArg (fun a : MulAut ↥K => a s₀) hα2
    rw [this]
  rcases genericKill_or_surv_of_FU4_data hF (onCenterQuotient α) hαY2 with
    hk | ⟨p₀, f₀, K₀, iK, fK, h, ⟨hp2, hq8, hcard⟩, e, α', hcomm, hS⟩
  · exact hnk hk
  · have : Fact p.Prime := ⟨hsig.A.prime⟩
    let eq0 : (↥K ⧸ center ↥K) ≃* ↥K :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let ε : ↥K ≃* hypPSU h 2 0 := eq0.symm.trans e
    have hmk : ∀ s : ↥K, eq0.symm s = QuotientGroup.mk s := fun s =>
      (MulEquiv.symm_apply_eq eq0).mpr rfl
    have hεcomm : ∀ s : ↥K, ε (α s) = α' (ε s) := by
      intro s
      show e (eq0.symm (α s)) = α' (e (eq0.symm s))
      rw [hmk, hmk, ← hcomm]
      exact congrArg e (onCenterQuotient_apply_mk α s).symm
    have hα'2 : α' * α' = 1 := by
      refine MulEquiv.ext fun s => ?_
      obtain ⟨s₀, rfl⟩ := ε.surjective s
      show α' (α' (ε s₀)) = ε s₀
      rw [← hεcomm, ← hεcomm]
      have : α (α s₀) = s₀ := congrArg (fun a : MulAut ↥K => a s₀) hα2
      rw [this]
    have hOut : U4Red.OutCommFour ↥K :=
      U4Red.outCommFour_of_mulEquiv ε.symm
        (fun a b => U4Red.commutator_pow_four_mem_hypPSU h hp2 a b)
    have hXK : X ≤ K :=
      x_le_layer_of_comm hzb2 hsig.A hsig.op hd.gen fun x hx =>
        U4Red.comm_mem_sup_centralizer_of_outCommFour K hOut hsig.A.prime hsig.A.odd hsig.A.pgroup
          (z_mem_normalizer_of_sig4A hsig.A) hx
    have hfixC : ∀ y ∈ fixSub α, (y : Sec H₀ H₁) ∈ centralizer ({zb} : Set (Sec H₀ H₁)) := by
      intro y hy
      have h1 : α y = y := hy
      have h2 := congrArg Subtype.val h1
      rw [show ((α y : ↥K) : Sec H₀ H₁) = zb * y * zb⁻¹ from coe_layerAut zb y] at h2
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (y : Sec H₀ H₁) * zb = (zb * y * zb⁻¹) * zb := by rw [h2]
        _ = zb * y := by group
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
    have hcommX : Subgroup.closure ((fun x : ↥K => x * (α x)⁻¹) '' (XT : Set ↥K)) = XT := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        rintro _ ⟨x, hx, rfl⟩
        have hxA : (x : Sec H₀ H₁) ∈ X := hx
        have hαx : ((α x : ↥K) : Sec H₀ H₁) ∈ X := by
          rw [coe_layerAut]
          exact (Subgroup.mem_normalizer_iff.mp hzN _).mp hxA
        exact XT.mul_mem hx (XT.inv_mem hαx)
      · set T : Subgroup ↥K :=
          Subgroup.closure ((fun x : ↥K => x * (α x)⁻¹) '' (XT : Set ↥K)) with hT
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
    obtain ⟨hXp', hXne', hcl', hN'⟩ := U4Red.core_transport ε hεcomm hXp hXne hcommX hN
    exact hCore p₀ f₀ K₀ h h.prime hp2 hq8 α' hα'2 hS p hsig.A.odd (XT.map ε.toMonoidHom) hXp'
      hXne' hcl' hN'

theorem cell87_FU4 (hInv : InvSec) (hCore : U4SurvCore) :
    Cell87 FU4 :=
  cell87_FU4_of_surv hInv (cell87Surv_FU4 hCore)

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
