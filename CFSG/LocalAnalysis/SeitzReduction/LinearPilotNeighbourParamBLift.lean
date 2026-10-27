module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotBLiftFusion
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRootTorusNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SeitzBranches
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotSetup

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.SeitzReduction.F4Pilot (HasBLift oddCoreLift)

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem bLift_rootTorus_of_fused_of_seitzSetting (hset : SeitzSetting G L) {n f : ℕ}
    {K : Type} [Field K] (hKc : Nat.card K = 2 ^ f) (hq : 4 ≤ Nat.card K)
    (e : L ≃* LinearFlag.projectiveSL n K) (hn : 5 ≤ n) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {a b : Fin n} (hab : a ≠ b)
    {X : Subgroup G} (hX : X = ((rootTorus (K := K) hab).map e.symm.toMonoidHom).map L.subtype)
    {D : Subgroup G}
    (hDe : D = ((blockSL (({a, b} : Finset (Fin n))ᶜ)).map e.symm.toMonoidHom).map L.subtype)
    {z g : G} (hzD : z ∈ D) (hz : orderOf z = 2) (hg : g⁻¹ * t * g = t * z)
    (hzP : ∃ P : Subgroup G, ⁅P, P⁆ = P ∧ P ≤ L ∧ z ∈ P ∧ P ≤ centralizer ({z} : Set G)) :
    t ∈ centralizer (X : Set G) ∧
      D.subgroupOf (centralizer (X : Set G)) ≤
          centralizer (oddCore (centralizer (X : Set G)) : Set (centralizer (X : Set G))) ∧
        ∀ K₁ K₂ : Subgroup (centralizer (X : Set G) ⧸ oddCore (centralizer (X : Set G))),
          CFSG.IsComponent K₁ → CFSG.IsComponent K₂ →
          ⁅K₁, (D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))⁆ ≠ ⊥ →
          ⁅K₂, (D.subgroupOf (centralizer (X : Set G))).map
            (QuotientGroup.mk' (oddCore (centralizer (X : Set G))))⁆ ≠ ⊥ →
          HasBLift K₁ ∧ HasBLift (K₁ ⊔ K₂) := by
  have := finite_of_card_eq_two_pow hKc
  have := charP_two_of_card_eq_two_pow hKc
  have hstd := hset.standardSetting
  have hL := hstd.standard
  have hLt := CFSG.EvenSmallLie.centralizer_le_normalizer_of_standard hL htC ht
  have hOut := isSolvable_outer_of_mulEquiv (by omega) e
  have hcard : (({a, b} : Finset (Fin n))ᶜ).card = n - 2 := by
    rw [Finset.card_compl, Fintype.card_fin, Finset.card_pair hab]
  obtain ⟨-, htX, hXc, hXo, hXJ, hD, -, -, -, hZ, -⟩ :=
    neighbour_data_rootTorus e hn hq hab htC hX hDe
  have hDq : CFSG.IsQuasisimple D := hDe ▸ isQuasisimple_map_blockSL (L := L) e
    (I := ({a, b} : Finset (Fin n))ᶜ) (by omega) (by omega) (Or.inl (by omega))
  have hDL : D ≤ L := by
    rw [hDe]
    exact map_subtype_le _
  have hconj : ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ L → P ≤ centralizer ({z} : Set G) →
      P ≤ conjugate L g := by
    intro P hP hPL hPz
    have hPt : P ≤ centralizer ({t} : Set G) := fun p hp =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC p (hPL hp))
    have hPtg : P ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
      intro p hp
      rw [hg, mem_centralizer_singleton_iff]
      have h1 : p * t = t * p := mem_centralizer_singleton_iff.1 (hPt hp)
      have h2 : p * z = z * p := mem_centralizer_singleton_iff.1 (hPz hp)
      calc p * (t * z) = (p * t) * z := by group
        _ = (t * p) * z := by rw [h1]
        _ = t * (p * z) := by group
        _ = t * (z * p) := by rw [h2]
        _ = t * z * p := by group
    exact (std_perfect_le_inf_conjugate hstd hOut htC ht g hP hPt hPtg).trans inf_le_right
  set R : Subgroup G := ((rootSL2 (K := K) a b).map e.symm.toMonoidHom).map L.subtype with hR
  have hRq : CFSG.IsQuasisimple R := by
    rw [hR, rootSL2_eq]
    exact isQuasisimple_map_blockSL (L := L) e (I := {a, b})
      (by rw [Finset.card_pair hab]; omega) (by rw [Finset.card_pair hab]) (Or.inr hq)
  have hRD : R ≤ centralizer (D : Set G) := by
    rw [hR, hDe]
    refine map_symm_le_centralizer_map_symm e fun x hx => ?_
    rw [mem_centralizer_iff]
    intro d hd
    rw [rootSL2_eq] at hx
    exact (commute_blockSL_of_disjoint disjoint_compl_right x hx d hd).eq.symm
  have hRz : R ≤ centralizer ({z} : Set G) := fun r hr =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (hRD hr) z hzD).symm
  have hXg : X ≤ conjugate L g :=
    hXJ.trans (hconj R (isPerfect_iff.mp hRq.1) (map_subtype_le _) hRz)
  have hzg : z ∈ conjugate L g := by
    obtain ⟨P, hP, hPL, hzP', hPz⟩ := hzP
    exact hconj P hP hPL hPz hzP'
  have hmain := le_centralizer_oddCore_of_fused hq e htC ht hLt hXc hXo htX hD hDq hZ hzD hz hg
    hXg hzg
  have hDO : D.subgroupOf (centralizer (X : Set G)) ≤
      centralizer (oddCore (centralizer (X : Set G)) : Set (centralizer (X : Set G))) := by
    intro d hd
    rw [mem_centralizer_iff]
    intro c hc
    exact Subtype.ext (hmain c ⟨c, hc, rfl⟩ d (mem_subgroupOf.1 hd))
  exact ⟨htX, hDO, fun K₁ K₂ hK₁ hK₂ h₁ h₂ =>
    hasBLift_of_isComponent_of_le_centralizer hDO hK₁ hK₂ h₁ h₂⟩

end CFSG.SeitzReduction.LinearPilot
