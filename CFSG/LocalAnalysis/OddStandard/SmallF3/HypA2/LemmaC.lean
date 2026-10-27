module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaCA
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LemmaCB
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.PumpStep
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Setting2

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint

theorem inS_of_pumpUpLT (hC : ClosureLeaves) {G : Type} [Group G] [Finite G] (hG : HSetting G)
    {x x' : G} {K K' : Subgroup G} (h : GH74.GLS.PumpUpLT 2 x K x' K')
    (hK : InS (↥K ⧸ center ↥K)) :
    InS (↥K' ⧸ center ↥K') ∧ Nat.card (↥K ⧸ center ↥K) ≤ Nat.card (↥K' ⧸ center ↥K') := by
  obtain ⟨hKq, hK'q, hcase⟩ := pumpStep hG.balanced h
  rcases hcase with he | ⟨σ, P, hP, he⟩
  ·
    obtain ⟨e⟩ := he
    exact ⟨(inS_congr e).1 hK, le_of_eq (Nat.card_congr e.toEquiv)⟩
  ·
    obtain ⟨e⟩ := he
    have hx' : orderOf x' = 2 := h.2.1.1
    have hKle : K' ≤ centralizer ({x'} : Set G) := h.2.1.2.2.1
    have hKp : IsPComponent 2 (K'.subgroupOf (centralizer ({x'} : Set G))) :=
      h.2.1.2.2.2
    have hcomp : Omega.IsComponentIn K' (centralizer ({x'} : Set G)) :=
      isComponentIn_of_isPComponent (hG.balanced x' hx') hKle hKp
    have hCne : centralizer ({x'} : Set G) ≠ ⊤ := by
      intro htop
      have hx'center : x' ∈ Subgroup.center G := by
        have hsub : ({x'} : Set G) ⊆ Subgroup.center G :=
          Subgroup.centralizer_eq_top_iff_subset.mp htop
        exact hsub (Set.mem_singleton x')
      have hcenter_bot : Subgroup.center G = ⊥ := by
        rcases hG.simple.eq_bot_or_eq_top_of_normal (Subgroup.center G) with hb | ht
        · exact hb
        · exfalso
          obtain ⟨a, b, hab⟩ := hG.nonab
          refine hab ?_
          have ha : a ∈ Subgroup.center G := by rw [ht]; trivial
          exact (Subgroup.mem_center_iff.mp ha b).symm
      have hx'one : x' = 1 := by
        have : x' ∈ (⊥ : Subgroup G) := by rw [← hcenter_bot]; exact hx'center
        simpa using this
      rw [hx'one, orderOf_one] at hx'
      exact (by decide : (1 : ℕ) ≠ 2) hx'
    have hS : Catalog (↥K' ⧸ center ↥K') :=
      catalog_quotient_center_of_isComponentIn hG.kProper hCne hcomp
    haveI : IsSimpleGroup (↥K' ⧸ center ↥K') := hK'q.2.1
    have hKP : InS (↥P ⧸ center ↥P) := (inS_congr e).1 hK
    have hcard : Nat.card (↥K ⧸ center ↥K) = Nat.card (↥P ⧸ center ↥P) :=
      Nat.card_congr e.toEquiv
    rcases hKP with hPA | hPB
    · obtain ⟨hSA, hlt⟩ := inSA_of_properFixedComp hC hS hP hPA
      exact ⟨Or.inl hSA, by rw [hcard]; exact hlt.le⟩
    · obtain ⟨hSS, hlt⟩ := inS_of_properFixedComp_B hC hS hP hPB
      exact ⟨hSS, by rw [hcard]; exact hlt.le⟩

end CFSG.OddStandard.SmallF3.HypA2
