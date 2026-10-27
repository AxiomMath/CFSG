module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HSubFinal
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.HGenProof
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.StrongEmbedInput
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.OpPrimeCoreLe
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.WeakBlockExists

public section

open CFSG.RankThreeCoreUniqueness.Helpers

namespace CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem d1PlusCore_le {p : ℕ} (H : Subgroup G)
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
    d1PlusCore p H K ≤ H := by
  unfold d1PlusCore
  exact Subgroup.map_subtype_le _

end CFSG.AGLEmbedding

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M Q H : Subgroup G} {p : ℕ}

theorem xSub_le_H (p : ℕ) (M H : Subgroup G) : xSub p M H ≤ H := by
  unfold xSub
  exact CFSG.AGLEmbedding.d1PlusCore_le (p := p) H (kStar p M H)

theorem xSub_subgroupOf_normal_of_kSub_normal
    (hK : ((kSub p M H).subgroupOf H).Normal) :
    ((xSub p M H).subgroupOf H).Normal := by
  have hKstar : (kStar p M H).Normal :=
    hK.map (QuotientGroup.mk' (primeComplementCore (G := H) p))
      (QuotientGroup.mk'_surjective _)
  haveI : (kStar p M H).Normal := hKstar
  have hsub : ((xSub p M H).subgroupOf H) =
      (Subgroup.centralizer (kStar p M H : Set (H ⧸ primeComplementCore (G := H) p))).comap
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [xSub]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [hsub]
  exact Subgroup.Normal.comap inferInstance _

theorem xSub_normal_of_kSub_normal (hK : ((kSub p M H).subgroupOf H).Normal) :
    H ≤ Subgroup.normalizer (xSub p M H : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (xSub_le_H p M H)).mp
    (xSub_subgroupOf_normal_of_kSub_normal hK)

theorem xSub_normal_of_pLayerIn_le (hL : pLayerIn p H ≤ M) :
    H ≤ Subgroup.normalizer (xSub p M H : Set G) :=
  xSub_normal_of_kSub_normal (kSub_normal_of_le hL)

theorem not_isSolvable_of_twelveCtx
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour) (h : TwelveCtx G M p Q H) :
    ¬ Group.IsSolvable M := by
  obtain ⟨L, hL⟩ := weakBlockSet_nonempty h1 h2 h25 h84 h
  exact not_isSolvable_of_mem_weakBlockSet hL

theorem relPPrimeCore_le_M_of_twelveCtx (h : TwelveCtx G M p Q H) :
    relPPrimeCore p H ≤ M := by
  obtain ⟨E, hEQ, hE, hEc, hΓ⟩ := h.exists_E_sq
  exact relPPrimeCore_le_of_gamma (Q := Q) h.p_prime (hEQ.trans h.Q_le_H) hE hEc hΓ

theorem not_dvd_card_xSub_inf_of_twelveCtx
    (h1 : CFSG.CGT.PushingUpLit.AschbacherTheoremOneK)
    (h2 : CFSG.CGT.PushingUpLit.AschbacherTheoremTwoK)
    (h25 : CFSG.CGT.PushingUpLit.SolomonAlternatingBlockK)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour) (h : TwelveCtx G M p Q H)
    (hI : NineNineOneInput) {d : ℕ} (hd : d ∈ sigmaSet G M) :
    ¬ d ∣ Nat.card (xSub p M H ⊓ M : Subgroup G) := by
  haveI : Fact p.Prime := ⟨h.p_prime⟩
  haveI : Fact d.Prime :=
    ⟨CFSG.RankThreeCoreUniqueness.Helpers.sigmaA_prime d hd.1⟩
  have hns : ¬ Group.IsSolvable M := not_isSolvable_of_twelveCtx h1 h2 h25 h84 h
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded d M :=
    isStronglyPEmbedded_of_twelveCtx' h hns d hd
  refine not_dvd_card_xSub_inf_of_glue (M := M) (H := H)
    (relPPrimeCore_le_M_of_twelveCtx h) ?_ h.not_H_le_M hstr
  intro hL
  exact le_kSub_sup_inf h hI hL

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
