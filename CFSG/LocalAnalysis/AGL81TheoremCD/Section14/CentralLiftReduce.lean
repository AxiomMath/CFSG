module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Inputs
import CFSG.CGT.Stroth77.Extension22FourComm
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseXfer

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

theorem kFactCentralLift_of_quotient
    (hcase : ∀ q p : ℕ, q.Prime → q ≠ 2 → p.Prime → p ≠ 2 → p ≠ q →
      ∀ (X : Type) [Group X] [Finite X] (K : Subgroup X), CFSG.IsQuasisimple ↥K →
        CFSG.LocalAnalysis.RankThreeTheoremC.NineFourListGroup q (↥K ⧸ Subgroup.center ↥K) →
        Odd (Nat.card (Subgroup.center ↥K)) → ¬ q ∣ Nat.card (Subgroup.center ↥K) →
        p ∣ Nat.card (Subgroup.center ↥K) →
        ∀ b : X, b ∈ Subgroup.normalizer (K : Set X) → orderOf b = p →
          b ∉ Subgroup.centralizer (K : Set X) →
        ∀ H : Subgroup (↥K ⧸ Subgroup.center ↥K), H ≠ ⊤ →
          (∃ S : Sylow q (↥K ⧸ Subgroup.center ↥K),
            Subgroup.normalizer ((S : Subgroup (↥K ⧸ Subgroup.center ↥K)) : Set _) ≤ H) →
          ¬ ((K ⊓ Subgroup.centralizer ({b} : Set X)).subgroupOf K).map
              (QuotientGroup.mk' (Subgroup.center ↥K)) ≤ H) :
    KFactCentralLift := by
  intro q p hq hq2 hp hp2 hpq X _ _ K hK hlist hodd hqZ hpZ b hbN hbord hbC K₁ hK₁ hZK₁
    hSyl hle
  haveI : Fact q.Prime := ⟨hq⟩
  let Z : Subgroup ↥K := Subgroup.center ↥K
  obtain ⟨S, hS, hSN⟩ := hSyl
  obtain ⟨Q, hQmap⟩ := hS
  have hZK₁' : Z ≤ K₁.subgroupOf K := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    exact hZK₁ (Subgroup.mem_map_of_mem K.subtype hz)
  have hHne : (K₁.subgroupOf K).map (QuotientGroup.mk' Z) ≠ ⊤ := by
    intro htop
    exact not_le_of_gt hK₁ (Subgroup.subgroupOf_eq_top.mp
      (CFSG.eq_top_of_le_of_map_quotient_eq_top hZK₁' htop))
  have hNQ : Subgroup.normalizer (Q : Set ↥K) ≤ K₁.subgroupOf K := by
    rw [← Subgroup.map_subtype_le_map_subtype (G' := K)]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_of_lt hK₁)]
    exact (le_inf (Subgroup.map_subtype_le (Subgroup.normalizer (Q : Set ↥K)))
      ((Subgroup.le_normalizer_map (H := (Q : Subgroup ↥K)) K.subtype).trans_eq
        (by rw [hQmap]))).trans hSN
  have hN : Subgroup.normalizer
      (((Q : Subgroup ↥K).map (QuotientGroup.mk' Z)) : Set (↥K ⧸ Z)) ≤
      (K₁.subgroupOf K).map (QuotientGroup.mk' Z) := by
    rw [← CFSG.LocalAnalysis.RankThreeTheoremC.map_mk_normalizer_eq Z hq
      (hq.coprime_iff_not_dvd.mpr hqZ) Q.isPGroup']
    exact Subgroup.map_mono hNQ
  have hSbar : Subgroup.normalizer
      (((Q.mapSurjective (QuotientGroup.mk'_surjective Z) : Sylow q (↥K ⧸ Z)) :
        Subgroup (↥K ⧸ Z)) : Set (↥K ⧸ Z)) ≤ (K₁.subgroupOf K).map (QuotientGroup.mk' Z) := by
    have hcoe : ((Q.mapSurjective (QuotientGroup.mk'_surjective Z) : Sylow q (↥K ⧸ Z)) :
        Subgroup (↥K ⧸ Z)) = (Q : Subgroup ↥K).map (QuotientGroup.mk' Z) := by
      simp only [Sylow.coe_mapSurjective]
    rw [hcoe]
    exact hN
  exact hcase q p hq hq2 hp hp2 hpq X K hK hlist hodd hqZ hpZ b hbN hbord hbC
    ((K₁.subgroupOf K).map (QuotientGroup.mk' Z)) hHne
    ⟨Q.mapSurjective (QuotientGroup.mk'_surjective Z), hSbar⟩
    (Subgroup.map_mono (Subgroup.subgroupOf_mono K hle))

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14
