module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinThmEBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE
open scoped commutatorElement

namespace ThmE

section QuotCentConj

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

theorem EStand.conj {K R W : Subgroup G} {S : Sylow 2 G} (h : EStand r Ω K S R W) (g : G) :
    EStand r Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W) where
  hyp := h.hyp
  cls := h.cls
  quat := h.quat
  two := h.two
  ih := h.ih
  mem := h.hyp.conjInvariant g K h.mem
  aEmpty := aEmpty_conj h.hyp.conjInvariant h.aEmpty g
  twin := by
    obtain ⟨K', hK', hne, R', hR', hR'K', hR'S⟩ := h.twin
    refine ⟨conjSub g K', twinSet_conj h.hyp.conjInvariant hK' g,
      fun h' => hne ((conjSub_inj g).mp h'), conjSub g R', RSet.conj h.hyp.conjInvariant hR' g,
      conjSub_mono hR'K', ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hR'S
  hR := by
    obtain ⟨hR, hRK, hRS⟩ := h.hR
    refine ⟨RSet.conj h.hyp.conjInvariant hR g, conjSub_mono hRK, ?_⟩
    rw [coe_conjSylow]
    exact conjSub_mono hRS
  hW := by
    obtain ⟨hW, hWS, hWn⟩ := h.hW
    refine ⟨WSet.conj h.hyp.conjInvariant hW g, ?_, ?_⟩
    · rw [coe_conjSylow]
      exact conjSub_mono hWS
    · intro s hs
      rw [coe_conjSylow, mem_conjSub_iff] at hs
      have := hWn _ hs
      calc conjSub s (conjSub g W) = conjSub g (conjSub (g⁻¹ * s * g) W) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub g W := by rw [this]

theorem MinCex.conj {K R W H : Subgroup G} {S : Sylow 2 G} (c : MinCex r Ω K S R W H) (g : G) :
    MinCex r Ω (conjSub g K) (conjSylow g S) (conjSub g R) (conjSub g W) (conjSub g H) where
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

theorem MinCex.conj_of_mem (c : MinCex r Ω K S R W H) {x : G} (hx : x ∈ H) :
    MinCex r Ω (conjSub x K) (conjSylow x S) (conjSub x R) (conjSub x W) H := by
  have := c.conj x
  rwa [conjSub_eq_self_of_mem hx] at this

theorem MinCex.quotCent_centralizer_le_mul (c : MinCex r Ω K S R W H) {M : Subgroup G}
    (hM : M ∈ dstarComp Ω K) {J : Subgroup G} (hJ : J ∈ omegaNbr Ω M) {z t : G}
    (hz : IsUniqueInvolution M z) (ht : IsUniqueInvolution J t) (ha1 : z * t ≠ 1)
    (ha2 : (z * t) * (z * t) = 1) : Subgroup.centralizer ({z * t} : Set G) ≤ H := by
  obtain ⟨h, hhH, hh⟩ := c.hyp.trans M hM
  subst hh
  have c' := c.conj_of_mem hhH
  exact centralizer_le_mul_of_omegaNbr c'.stand.hyp c'.stand.mem c'.hyp.trans hz
    (c'.centralizer_le hz) c'.stand.hR.1 c'.stand.hR.2.1 c'.stand.hR.2.2 c'.stand.hW.1
    c'.stand.hW.2.1 c'.stand.hW.2.2 c'.hyp.cent hJ ht ha1 ha2

end QuotCentConj

end ThmE

end CFSG.CGT.PushingUpLit.SolKNA.R4

