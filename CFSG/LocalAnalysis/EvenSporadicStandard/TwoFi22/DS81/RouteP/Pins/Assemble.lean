module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.F12
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.QCent
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.ConjPin
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.RouteP.Pins.PinH

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP

open Subgroup
open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

variable {G : Type} [Group G] [Finite G] {L E : Subgroup G} {t : G}

theorem Std.nonempty_pins
    (h : Std G L E t) (hr : L.relIndex (centralizer ({t} : Set G)) = 2) :
    Nonempty (Pins G E t) := by
  obtain ⟨P⟩ := Std.nonempty_pinN h hr
  obtain ⟨ψH, hagree⟩ := Std.exists_pinH h hr P
  have htN : t ∈ normalizer (E : Set G) := Subgroup.le_normalizer h.m24.t_mem
  obtain ⟨φ, h1, h2⟩ := exists_hom_agree_of_conj (D := Model.D0) P.ψN ψH hagree htN
    (P.map_t htN) Model.g0_mem_Zq (Model.E0_le_Zq Model.t13_mem_E0)
    (Model.L0_le_Ze (Model.Q0_le_L0 (Model.E0_le_Q0 Model.t13_mem_E0)))
    Model.g0_conj_t0 Model.g0_conj_t13 (fun _ => Model.conj_g0_mem_Ze_iff)
    (fun _ => Model.conj_g0_mem_Q0_iff) Model.Ze_inf_Ze'' Model.Ze_inf_centralizer_t13
    Model.D0_le_Zq Model.f12
  exact ⟨⟨P.ψN, ψH, φ, hagree, h1, h2⟩⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP
