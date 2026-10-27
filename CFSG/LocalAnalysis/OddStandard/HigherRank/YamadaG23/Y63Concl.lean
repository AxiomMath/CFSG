module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y63C1

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

structure Y63Concl (c : Ctx6 G L) : Prop where
  cen_eq : cen (y63Q c) = zpowers c.s.fr.z
  uniq : ∀ U : Subgroup G, U ≤ y63Q c → Y63ZE64 (zpowers c.s.fr.z) U → U = C1 c.e
  good : ∀ x ∈ S3 c.s, orderOf x = 2 → 2 ^ 7 ≤ Nat.card ↥(centEl (y63Q c) x) →
    x ∉ ⁅centEl (y63Q c) x, centEl (y63Q c) x⁆ →
      x ∈ C1 c.e ∧ c.s.fr.z ∈ ⁅centEl (y63Q c) x, centEl (y63Q c) x⁆

theorem y63_concl (hHS : HSSylowFacts) (c : Ctx6 G L) (hH : F33Hyp c.s c.e)
    (hF : c.toCtx5.Facts5) (h62 : c.Fact62) (hRT : c.s.R = c.s.T) : Y63Concl c := by
  have hY := y63_hyps c hH hF hRT
  have ht2 : c.s.t ^ 2 = 1 := by
    simpa [c.s.t_order] using pow_orderOf_eq_one c.s.t
  obtain ⟨hcard2, U, hUQ, hUZ, huniq, hgood⟩ :=
    hHS G (y63Q c) (S3 c.s) (M3 c.s) c.s.fr.S c.s.t hY.S3_le hY.card h62 hY.t_mem
      hY.t_not_mem ht2 hY.M_le hY.M_norm hY.M_comm hY.M_equiv hY.S_le hY.S_card hY.S_sup
      hY.omega_le hY.t_cent hY.t_inv
  have hz2 : orderOf c.s.fr.z = 2 := s3_z_order c.s (lfactsA_of_setting hH.hS hH.hZ c.s)
  have hcardz : Nat.card ↥(zpowers c.s.fr.z) = 2 := by simp [hz2]
  have hzle : zpowers c.s.fr.z ≤ cen (y63Q c) :=
    Subgroup.zpowers_le.mpr (y63_z_mem_cen_Q c hH hF hRT)
  have hZ : cen (y63Q c) = zpowers c.s.fr.z :=
    (Subgroup.eq_of_le_of_card_ge hzle (by rw [hcard2, hcardz])).symm
  have hCU : C1 c.e = U :=
    huniq (C1 c.e) (y63_C1_le_Q c hH) (hZ.symm ▸ y63_C1_ZE64 c hH)
  refine ⟨hZ, ?_, ?_⟩
  · intro U' hU' hU'Z
    exact (huniq U' hU' (hZ.symm ▸ hU'Z)).trans hCU.symm
  · intro x hxS hx2 hcardx hxnot
    obtain ⟨hxU, hzC⟩ := hgood x hxS hx2 hcardx hxnot
    exact ⟨by rw [hCU]; exact hxU, hzC (hzle (Subgroup.mem_zpowers c.s.fr.z))⟩

end CFSG.OddStandard.HigherRank.YamadaG23
