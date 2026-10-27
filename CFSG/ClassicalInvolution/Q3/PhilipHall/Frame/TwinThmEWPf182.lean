module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWBase
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWQ8Frame
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmQ8Eng182

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section E182

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def E18_2Q8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (K : Subgroup G) (S : Sylow 2 G)
    (R W H : Subgroup G), MinCexQ8 Ω K S R W H →
      ∀ u ∈ K, orderOf u = 4 → ∀ g : G, g * u * g⁻¹ ∈ H → g ∈ H

theorem mem_dstarComp_of_mem_USet_le_W [Finite G] (hΩ : HypOmegaGen Ω) {K J W V₀ V₁ : Subgroup G} (hK
    : K ∈ Ω) (hJ : J ∈ Ω)
    (hV₀ : V₀ ∈ USet Ω) (hV₀K : V₀ ≤ K) (hV₀W : V₀ ≤ W) (hV₁ : V₁ ∈ USet Ω) (hV₁J : V₁ ≤ J)
    (hV₁W : V₁ ≤ W) (habel : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) : J ∈ dstarComp Ω K :=
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.mem_dstarComp_of_mem_USet_le_W hΩ hK hJ hV₀
    hV₀K hV₀W hV₁ hV₁J hV₁W habel

section MinCexQ8
variable [Finite G] {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem MinCexQ8.exists_eta (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω) :
    ∃ η : Set (Subgroup G), η ∈ etaG Ω ∧ W = ⨆ V ∈ η, V ∧
      (∀ V ∈ η, V ∈ USet Ω ∧ V ≤ (S : Subgroup G)) ∧
      (∀ x ∈ W, ∀ y ∈ W, x * y = y * x) ∧ ∃ V₀ ∈ η, V₀ ≤ K := by
  exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.MinCexQ8Frame.exists_eta (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.MinCexQ8.toFrame c) hA

theorem MinCexQ8.mem_of_conjSub_eq_W (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω) {n : G}
    (hn : conjSub n W = W) : n ∈ H := by
  exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.MinCexQ8Frame.mem_of_conjSub_eq_W (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.MinCexQ8.toFrame c) (e18_1Q8 G Ω K S R W H c).1 hA hn

theorem MinCexQ8.sylow_le (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω) :
    (S : Subgroup G) ≤ H :=
  fun s hs => c.mem_of_conjSub_eq_W hA (c.stand.hW.2.2 s hs)

theorem MinCexQ8.mem_of_conj_mem (c : MinCexQ8 Ω K S R W H) (hA : EtaAbelian Ω)
    (hM : EtaMeet Ω) {u : G} (hu : u ∈ K) (hu4 : orderOf u = 4) {g : G} (hg : g * u * g⁻¹ ∈ H) :
    g ∈ H := by
  exact CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE.MinCexQ8Frame.mem_of_conj_mem (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEW.MinCexQ8.toFrame c) (e18_1Q8 G Ω K S R W H c).1 hA hM hu hu4 hg
end MinCexQ8

theorem etaAbelian_of_gen [Finite G] (hΩ : HypOmegaGen Ω) : EtaAbelian Ω :=
  fun S _ hη hinv => (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv).1

theorem etaMeet_of_gen [Finite G] (hΩ : HypOmegaGen Ω) : EtaMeet Ω :=
  fun S _ hη hηS _ hK h2 => Q3T8.Asc77.l6_11_proved G Ω hΩ S _ hη hηS _ hK h2

theorem e18_2Q8 : E18_2Q8 := by
  intro G _ _ Ω K S R W H c u hu hu4 g hg
  exact c.mem_of_conj_mem (etaAbelian_of_gen c.stand.hyp) (etaMeet_of_gen c.stand.hyp) hu hu4 hg

end E182

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
