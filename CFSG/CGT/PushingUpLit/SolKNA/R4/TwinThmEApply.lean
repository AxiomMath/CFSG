module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEDefs
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf16Orbit
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscBase
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinDiscThmE
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWCore

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

namespace ThmE

section Apply


theorem centPairs_of_ext {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K W H S : Subgroup G}
    (hΩ : HypOmegaGen Ω) (hK : K ∈ Ω) (hW : W ∈ WSet Ω) (hKW : K ⊓ W ∈ USet Ω)
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J)
    (hext : ∀ x ∈ H, K ⊓ conjSub x W ∈ USet Ω → CentralizersSylowPairsW Ω K (conjSub x W) H) :
    TwinThmEW.CentPairs Ω S W H := by
  intro M hM hMW J hJ R₁ R₂ hR₁ hR₁M _ hR₂ hR₂J _ hcomm a haR haW ha1 ha2
  obtain ⟨h, hhH, rfl⟩ := htrans M (TwinThmEW.mem_dstarComp_of_inf_W hΩ hW hK hM hKW hMW)
  have hU : K ⊓ conjSub h⁻¹ W ∈ USet Ω := by
    have := USet.conj hΩ.conjInvariant hMW h⁻¹
    rwa [TwinThmEW.conjSub_inf', conjSub_inv_conjSub] at this
  have hc := hext h⁻¹ (H.inv_mem hhH) hU
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  have hKtw : K ∈ twinSet Ω K := ⟨hK, z, hz, hz⟩
  have hJ' : conjSub h⁻¹ J ∈ KPerp Ω K := by
    have := KPerp_conj hΩ.conjInvariant hJ h⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hR₁M' : conjSub h⁻¹ R₁ ≤ K := by
    have := conjSub_mono (n := h⁻¹) hR₁M
    rwa [conjSub_inv_conjSub] at this
  have hR₂J' : conjSub h⁻¹ R₂ ≤ conjSub h⁻¹ J := conjSub_mono hR₂J
  have hcomm' : Commutes (conjSub h⁻¹ R₁) (conjSub h⁻¹ R₂) ∨ conjSub h⁻¹ R₂ = conjSub h⁻¹ R₁ := by
    rcases hcomm with h1 | h1
    · exact Or.inl (h1.conjSub h⁻¹)
    · exact Or.inr (by rw [h1])
  have haR' : h⁻¹ * a * h ∈ conjSub h⁻¹ R₁ ⊔ conjSub h⁻¹ R₂ := by
    have := conj_mem_conjSub (n := h⁻¹) haR
    rwa [conjSub_sup, inv_inv] at this
  have haW' : h⁻¹ * a * h ∈ conjSub h⁻¹ W := by
    have := conj_mem_conjSub (n := h⁻¹) haW
    rwa [inv_inv] at this
  have ha1' : h⁻¹ * a * h ≠ 1 := by
    intro h1
    apply ha1
    have : a = h * (h⁻¹ * a * h) * h⁻¹ := by group
    rw [this, h1]
    group
  have ha2' : (h⁻¹ * a * h) * (h⁻¹ * a * h) = 1 := by
    calc (h⁻¹ * a * h) * (h⁻¹ * a * h) = h⁻¹ * (a * a) * h := by group
      _ = 1 := by rw [ha2]; group
  have hC := hc K hKtw (conjSub h⁻¹ J) hJ' (conjSub h⁻¹ R₁) (conjSub h⁻¹ R₂)
    (RSet.conj hΩ.conjInvariant hR₁ h⁻¹) hR₁M' (RSet.conj hΩ.conjInvariant hR₂ h⁻¹) hR₂J' hcomm'
    (h⁻¹ * a * h) haR' haW' ha1' ha2'
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  have hx' : h⁻¹ * x * h ∈ Subgroup.centralizer ({h⁻¹ * a * h} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * x * h * (h⁻¹ * a * h) = h⁻¹ * (x * a) * h := by group
      _ = h⁻¹ * (a * x) * h := by rw [hx]
      _ = h⁻¹ * a * h * (h⁻¹ * x * h) := by group
  have h2 := H.mul_mem (H.mul_mem hhH (hC hx')) (H.inv_mem hhH)
  simpa [mul_assoc] using h2

@[expose] def ExtendR (r n : ℕ) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y),
    TwinCoreHypR r n Y R S t → ∀ K H W : Subgroup Y, K ∈ CoreAssembly.conjClass (tightCore R) →
      TwinThmEW.PrintedWT (CoreAssembly.conjClass (tightCore R)) K W →
      EHypSylW (CoreAssembly.conjClass (tightCore R)) K W H →
      ∀ x ∈ H, K ⊓ conjSub x W ∈ USet (CoreAssembly.conjClass (tightCore R)) →
        CentralizersSylowPairsW (CoreAssembly.conjClass (tightCore R)) K (conjSub x W) H

theorem twinThmER_of_thmEAll {r n : ℕ} (hE : ThmEAll r) (hX : ExtendR r n)
    (h4 : Thm4TwinSupplyR r n) : TwinThmER r n := by
  intro Y _ _ R S t h K H W hK hW hH
  set Ω := CoreAssembly.conjClass (tightCore R) with hΩdef
  have hΩ : HypOmegaGen Ω := h.hyp
  have hKΩ : K ∈ Ω := hK
  obtain ⟨S₀, hWat⟩ := hW.exists_at
  obtain ⟨R₀, hR₀, hR₀S, hWΩ, hWS, hWn, hT⟩ := hWat
  have hKW : K ⊓ W ∈ USet Ω :=
    TwinThmEW.inf_W_mem_USet' hΩ hWΩ hWS hKΩ (mem_RSet_of_isSylow2In hKΩ hR₀) hR₀.1 hR₀S
  have hHall : TwinThmEW.EHypAll Ω K (S₀ : Subgroup Y) W H :=
    ⟨hH.trans, centPairs_of_ext hΩ hKΩ hWΩ hKW hH.trans
      (hX Y R S t h K H W hK ⟨S₀, R₀, hR₀, hR₀S, hWΩ, hWS, hWn, hT⟩ hH)⟩
  obtain ⟨g, rfl⟩ := hK
  have hquat : ∀ L ∈ Ω, ∃ P : Subgroup Y, IsSylow2In P L ∧
      Nonempty (↥P ≃* QuaternionGroup (2 ^ (r - 2))) := by
    rintro _ ⟨g', rfl⟩
    refine ⟨conjSub g' ((S : Subgroup R).map R.subtype), h.datum.sylow_core.conj g', ⟨?_⟩⟩
    exact (Subgroup.equivMapOfInjective _ (MulAut.conj g').toMonoidHom
      (MulAut.conj g').injective).symm.trans
      ((Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans
        h.quat.some)
  have h2 : ∀ L ∈ Ω, IsPGroup 2 (↥L ⧸ classicalInvolutionOddCore ↥L) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) h.datum.twoGroup)
  have hih : EIH r (Nat.card Y) := by
    rw [h.card]
    exact ⟨h.below, h.tbelow, h.twinBelow, h4 h.below h.tbelow h.twinBelow⟩
  have hst : EStand r Ω (conjSub g (tightCore R)) S₀ R₀ W :=
    { hyp := hΩ
      cls := h.toStd.classicalClause
      quat := hquat
      two := h2
      ih := hih
      mem := hKΩ
      aEmpty := aEmpty_allR h.toStd _ hKΩ
      twin := hT
      hR := ⟨mem_RSet_of_isSylow2In hKΩ hR₀, hR₀.1, hR₀S⟩
      hW := ⟨hWΩ, hWS, hWn⟩ }
  exact hE Y Ω _ S₀ R₀ W H hst hHall

end Apply

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4
