module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf8Core
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp
public import CFSG.ClassicalInvolution.Asc77.AscC25J10

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Balance.Bootstrap


section Sec

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem secNbr_eq_of_perp (hΩ : HypOmegaGen Ω) (hc2 : IsPGroup 2 (Subgroup.zpowers c))
    {K K' J : Subgroup G} (hK : K ∈ tqMembers3 Ω c) (hJ : J ∈ tqMembers3 Ω c)
    (hperp : ∀ J₀ ∈ tqMembers3 Ω c, J₀ ∈ KPerp Ω K → J₀ = K ∨ J₀ = K')
    (h : secImg Ω c J ∈ omegaNbr (TwinDisc.secFam Ω c) (secImg Ω c K)) :
    secImg Ω c J = secImg Ω c K' := by
  set N := classicalInvolutionOddCore ↥(coreHull Ω c) with hN
  have hodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥(coreHull Ω c)
  have hΛ : HypOmegaGen (hullFam Ω c) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) (coreHull Ω c)
  have hΛ' : HypOmegaGen (TwinDisc.secFam Ω c) := hypOmegaGen_secFam hΩ hc2
  obtain ⟨n, hn, hnb⟩ := CFSG.ClassicalInvolution.Asc77.C25J.exists_conj_omegaNbr_gen (Ω := hullFam Ω c) (N := N) hΛ hΛ' hodd
    (TwinThmE.secOf_mem_hullFam hK) (TwinThmE.secOf_mem_hullFam hJ) h
  have h1 := omegaNbr_conj hΛ.conjInvariant hnb n⁻¹
  rw [conjSub_inv_conjSub] at h1
  have h2 : conjSub n⁻¹ (TwinThmE.secOf Ω c J) ∈ KPerp (hullFam Ω c) (TwinThmE.secOf Ω c K) :=
    Set.mem_insert_of_mem _ h1
  obtain ⟨J₀, hJ₀, hJ₀eq, hJ₀perp⟩ := TwinThmE.exists_lift_kPerp hΩ hc2 hK h2
  rcases hperp J₀ hJ₀ hJ₀perp with h3 | h3
  · exact absurd (hJ₀eq.trans (by rw [h3])) h1.2.1
  · have h4 : conjSub n⁻¹ (TwinThmE.secOf Ω c J) = TwinThmE.secOf Ω c K' := by
      rw [hJ₀eq, h3]
    have h5 := congrArg (conjSub n) h4
    rw [conjSub_conjSub_inv] at h5
    show (TwinThmE.secOf Ω c J).map (QuotientGroup.mk' N) =
      (TwinThmE.secOf Ω c K').map (QuotientGroup.mk' N)
    rw [h5, AscQuot.map_conjSub, show QuotientGroup.mk' N n = 1 from
      (QuotientGroup.eq_one_iff _).mpr hn, conjSub_one]

end Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinLayerGen
