module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWDefs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE189a

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section A

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.conj {K R W H : Subgroup G} {S : Sylow 2 G} (c : MinCexQ8 Ω K S R W H)
    (g : G) : MinCexQ8 Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W)
      (conjSub g H) where
  stand := c.stand.conj g
  hyp := by
    rw [coe_conjSylow]
    exact c.hyp.conj c.stand.hyp.conjInvariant g
  proper := by
    intro h
    apply c.proper
    have := congrArg (conjSub g⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_top_eq_top] at this
  minimal := c.minimal

theorem MinCexQ8.conj_of_mem (c : MinCexQ8 Ω K S R W H) {x : G} (hx : x ∈ H) :
    MinCexQ8 Ω (conjSub x K) (conjSylow x S) (conjSub x R) (conjSub x W) H := by
  have := c.conj x
  rwa [conjSub_eq_self_of_mem hx] at this

theorem MinCexQ8.center_eq_bot (h6 : E18_6Q8) (c : MinCexQ8 Ω K S R W H) :
    Subgroup.center G = ⊥ := by
  obtain ⟨-, F, -, -, -, hF⟩ := h6 G Ω K S R W H c
  rw [eq_bot_iff]
  intro x hx
  have : x ∈ Subgroup.centralizer (F : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact (Subgroup.mem_center_iff.mp hx y)
  rw [hF] at this
  exact this

theorem MinCexQ8.centralizer_ne_top (h6 : E18_6Q8) (c : MinCexQ8 Ω K S R W H) {x : G}
    (hx : x ≠ 1) : Subgroup.centralizer ({x} : Set G) ≠ ⊤ := by
  intro h
  apply hx
  have hc : x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    have : y ∈ Subgroup.centralizer ({x} : Set G) := by rw [h]; exact Subgroup.mem_top y
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  rw [c.center_eq_bot h6] at hc
  exact Subgroup.mem_bot.mp hc

theorem e189_caseA (hΩ : HypOmegaGen Ω) {K J : Subgroup G}
    {z t : G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (hz : IsUniqueInvolution K z)
    (ht : IsUniqueInvolution J t) (htz : t ≠ z) (hzt : z * t = t * z)
    (hnorm : conjSub t K = K) : (∃ g : G, g * t * g⁻¹ = z * t) ∨ J ∈ KPerp Ω K :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.e189_caseA hΩ hK hJ hz ht htz hzt hnorm

theorem AEmpty.restrict (hΩ : HypOmegaGen Ω) {Y K : Subgroup G}
    (hKY : K ≤ Y) (hA : AEmpty Ω K) : AEmpty (restrictFamily Ω Y) (K.subgroupOf Y) :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.AEmpty.restrict hΩ hKY hA

end A

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
