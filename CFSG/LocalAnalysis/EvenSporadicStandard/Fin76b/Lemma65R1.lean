module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WreathK
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.A6Cent

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

@[expose] def BetaData65 {G : Type*} [Group G] (E : Subgroup G) (β : G) : Prop :=
  Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8 ∧
    (E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G)) ≤
      _root_.commutator ↥(centralizer ({β} : Set G))

@[expose] def Fin76bBetaData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (z t : G) (T₀ E : Subgroup G)
    (Q : Sylow 2 G) (x β : G) (B : Subgroup G), Rest6Config L z t T₀ E Q x β B →
    WFacts L t E → BetaData65 E β

theorem fin76bNoOrderEight_of_betaData (hβ : Fin76bBetaData) : Fin76bNoOrderEight := by
  intro G _ _ L z t T₀ E Q x β B hconf hW S hS2 hSC hSmax hzS hBS u hu hu8
  obtain ⟨hz, hL64⟩ := hconf.lemma64
  obtain ⟨hD8, hDK⟩ := hβ G L z t T₀ E Q x β B hconf hW
  have hSK : S ≤ centralizer ({β} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.2 (hBS β hconf.beta_mem s hs).symm
  have hEK : E ⊓ centralizer ({β} : Set G) ≤ centralizer ({β} : Set G) := inf_le_right
  have hET : E ≤ T₀ := hconf.econfig.le
  refine no_element_of_order_eight (K := ↥(centralizer ({β} : Set G))) (z := ⟨z, hz⟩)
    (Subtype.ext hconf.cfg.z_sq) hL64
    (fun N hN P hP hP8 a ha hc => ?_)
    (D := (E ⊓ centralizer ({β} : Set G)).subgroupOf (centralizer ({β} : Set G))) ?_ ?_ ?_ hDK
    (u := ⟨u, hSK hu⟩) ?_ ?_
  · obtain ⟨e⟩ := hN
    exact sq_eq_one_of_comm_order_eight_of_le e P hP hP8 a ha hc
  · intro d hd
    have hdE : (d : G) ∈ E := (mem_subgroupOf.1 hd).1
    have := (IsPGroup.iff_orderOf.1 hconf.cfg.T₀_pgroup) ⟨(d : G), hET hdE⟩
    obtain ⟨k, hk⟩ := this
    refine ⟨k, ?_⟩
    rw [← Subgroup.orderOf_coe] at hk
    rw [← Subgroup.orderOf_coe d]
    exact hk
  · rw [← hD8]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  · intro d hd
    have hdE : (d : G) ∈ E := (mem_subgroupOf.1 hd).1
    apply Subtype.ext
    exact hconf.cfg.z_comm_of_mem_A ((hconf.cfg.T₀_le (hET hdE)))
  · rw [← Subgroup.orderOf_coe]
    exact hu8
  · intro d hd
    have hdE : (d : G) ∈ E := (mem_subgroupOf.1 hd).1
    apply Subtype.ext
    exact (mem_centralizer_iff.1 (hSC hu) (d : G) hdE).symm

end CFSG.EvenSporadicStandard.Fin76b
