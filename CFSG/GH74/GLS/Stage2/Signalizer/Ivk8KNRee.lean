module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KNGen
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87ReeCent
public import CFSG.LocalAnalysis.ComponentClassification.LiteratureLocalSmallReeOuter

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.Blueprint CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.LieType.Ree CFSG.LieType.Chevalley
open scoped commutatorElement

theorem kn_ree_model {Y : Type} [Group Y] (h : FRee Y) :
    ∃ f : ℕ, ReeTitsModel Y .twistedG2 3 f := by
  obtain ⟨f, -, hlie⟩ := h
  refine ⟨f, ?_⟩
  rcases hlie with ⟨hh, -⟩ | ⟨-, hh, -⟩ | ⟨-, -, hR⟩ | ⟨-, hh, -⟩
  · exact absurd hh (by decide)
  · exact absurd hh (by decide)
  · exact hR
  · exact absurd hh (by decide)

theorem kn_eq_one_of_odd_card {E : Type} [Group E] {n : ℕ} (hn : Nat.card E = 2 * n + 1) {x : E}
    (hx : x * x = 1) : x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hx)
  have h3 : orderOf x ∣ 2 * n + 1 := hn ▸ orderOf_dvd_natCard x
  rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
  · exact orderOf_eq_one_iff.1 h
  · rw [h] at h3
    omega

theorem kay_Ree :
    KAY FRee := by
  refine kay_of_kaAll ?_
  intro Y _ _ hY _ α hα2 hα1
  obtain ⟨f, hm⟩ := kn_ree_model hY
  obtain ⟨a, K, _, _, _, ha, hK, ⟨e⟩⟩ := ree_model_data_pos hm
  have hZ : center ↥(ReeTag.G2.reeGamma K a) = ⊥ := ReeTag.center_reeGamma_G2_eq_bot hK
  have hinj : Function.Injective (MulAut.conj : Y →* MulAut Y) :=
    kn_conj_injective_of_center_bot (center_eq_bot_of_mulEquiv_target e hZ)
  obtain ⟨hcyc, hcard⟩ :=
    CFSG.ComponentClassification.LiteratureLocal.SmallRee.outer_reeGamma_cyclic ha hK
  have : IsCyclic (Outer ↥(ReeTag.G2.reeGamma K a)) := hcyc
  have hker : (QuotientGroup.mk' (inner ↥(ReeTag.G2.reeGamma K a))).ker =
      innSub ↥(ReeTag.G2.reeGamma K a) := QuotientGroup.ker_mk' _
  obtain ⟨Θ, hΘ⟩ := kn_hom_of_mulEquiv e _ hker
  have hΘα : Θ α = 1 := by
    refine kn_eq_one_of_odd_card hcard ?_
    rw [← map_mul, hα2, map_one]
  obtain ⟨k, hk⟩ : ∃ k : Y, MulAut.conj k = α := by
    rw [← kn_mem_innSub, ← hΘ]
    exact hΘα
  have hk2 : k * k = 1 := by
    apply hinj
    rw [map_mul, hk, hα2, map_one]
  have hk1 : k ≠ 1 := fun h => hα1 (by rw [← hk, h, map_one])
  have hord : orderOf k = 2 := orderOf_eq_prime (by rw [sq]; exact hk2) hk1
  have hNoP : KANoP α := by
    intro p hp hp2 N hN hNn hNp
    rw [← hk, kn_fixSub_conj] at hN hNn
    exact (ree_involution_centralizer hm hord).2 p hp hp2 N hN hNn hNp
  exact ka_all_of_noP hinj hNoP (kaOutCyc_of_hom Θ hΘ) (ka_hOut_of_hom Θ hΘ α)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
