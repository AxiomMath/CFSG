module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk714SporM12J2
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcL
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporMcLOuter

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open CFSG CFSG.Blueprint CFSG.GH74.GLS CFSG.GH74.GLS.IVK Subgroup
  CFSG.ComponentClassification.RestrictedStd.Spor CFSG.ComponentClassification.OuterAutomorphisms

theorem ivk714_mcl :
    Ivk714Empty (fun X _ => NativeSporadic.IsSporadic X .McL) := by
  intro K _ _ hs hK z hz h
  obtain ⟨e⟩ := hK
  have hZ : Subgroup.center K = ⊥ := h.center_eq_bot
  obtain ⟨B, hB, -, ⟨hq⟩, -⟩ := exists_alt7_component (C := ↥(fixedSubgroup K z)) h
  have hcard : Nat.card (↥B ⧸ center ↥B) = 2520 := by
    rw [Nat.card_congr hq.toEquiv]
    exact card_alt7
  by_cases hin : z ∈ inner K
  · obtain ⟨t, ht⟩ := hin
    have ht2 : orderOf t = 2 := orderOf_eq_two_of_conj hZ ht hz
    have hfix : fixedSubgroup K z = centralizer ({t} : Set K) := by
      subst ht
      ext x
      show MulAut.conj t x = x ↔ _
      rw [Subgroup.mem_centralizer_singleton_iff]
      simp only [MulAut.conj_apply]
      rw [mul_inv_eq_iff_eq_mul, eq_comm]
    have hcomps := CompsSatisfy.of_mulEquiv (isoInvariant_quotient_center_equiv _)
      (MulEquiv.subgroupCongr hfix) (mcl_inner_comps e t ht2)
    obtain ⟨θ⟩ := hcomps B hB
    rw [Nat.card_congr θ.toEquiv, CFSG.Sporadic.SmallOddCore.card_mclX] at hcard
    omega
  · have hfix : fixedSubgroup K z = CFSG.Sporadic.Schreier.fixSub z := by
      ext x
      exact Iff.rfl
    have hcomps := CompsSatisfy.of_mulEquiv (isoInvariant_card_quotient_center _)
      (MulEquiv.subgroupCongr hfix) (mcl_outer_comps e z (ivk714_sq_eq_one hz) hin)
    have h7920 : Nat.card (↥B ⧸ center ↥B) ∈ ({7920} : Set ℕ) := hcomps B hB
    rw [hcard] at h7920
    simp at h7920

end CFSG.GH74.GLS.IVK.Proofs2
