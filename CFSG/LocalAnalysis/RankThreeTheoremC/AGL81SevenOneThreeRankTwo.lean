module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OutTowerThreeRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81SevenFourTwoSteps
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1AlphaList3
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Inputs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineThreeOutPClosedOf
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterSylowClassical
import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration
open CFSG.ComponentClassification.OuterAutomorphisms (Outer centerQuotient_outer_injective)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple (ExceptionalTowers)
open CFSG.LocalAnalysis.RankThreeUC.AGL81C (IsPClosedMod)

theorem sylow_normal_of_injective {A B : Type*} [Group A] [Group B] {p : ℕ} {f : A →* B}
    (hf : Function.Injective f) (h : ∀ P : Sylow p B, (P : Subgroup B).Normal) :
    ∀ P : Sylow p A, (P : Subgroup A).Normal := by
  intro P
  obtain ⟨Q, hQ⟩ := P.exists_comap_eq_of_injective hf
  rw [← hQ]
  exact (h Q).comap f

theorem isPClosedMod_of_normal_sup_sylow {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    {U : Subgroup X} [U.Normal] (R : Sylow p X) (h : ((R : Subgroup X) ⊔ U).Normal) :
    IsPClosedMod p U := by
  refine ⟨(R : Subgroup X) ⊔ U, h, le_sup_right, ?_, fun hdvd =>
    R.not_dvd_index (hdvd.trans (Subgroup.index_dvd_of_le le_sup_left))⟩
  obtain ⟨n, hn⟩ := R.isPGroup'.exists_card_eq
  have hdvd : U.relIndex (R : Subgroup X) ∣ p ^ n := hn ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd
  exact ⟨k, (Subgroup.relIndex_sup_right (H := (R : Subgroup X)) (K := U)).trans hk⟩

theorem sylow_normal_outer_three_of_cover (hT : ExceptionalTowers) (hA : KFactAlphaListM3Wide)
    (hN : KFactProofs.T29.NoncyclicCentreRank) {L : Type} [Group L] [Finite L]
    (hq : Open.IsQuasisimple L) (hcat : IsCatalogGroup (L ⧸ Subgroup.center L))
    (hrk : Open.pRank 3 (⊤ : Subgroup L) ≤ 2) (h3 : 3 ∣ Nat.card (Subgroup.center L)) :
    ∀ P : Sylow 3 (Outer (L ⧸ Subgroup.center L)),
      (P : Subgroup (Outer (L ⧸ Subgroup.center L))).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  obtain ⟨a, b, hab⟩ :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hq
  have hZ : Subgroup.center (L ⧸ Subgroup.center L) = ⊥ :=
    CFSG.Sporadic.Schreier.center_eq_bot_of_simple inferInstance hab
  set N : Subgroup L := GL83.I243.Cover.primeCentre 3 L
  have hqN : Open.IsQuasisimple (L ⧸ N) := GL83.I243.Cover.isQuasisimple_quotient hq
  obtain ⟨eN⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hq
  have hcatN : IsCatalogGroup ((L ⧸ N) ⧸ Subgroup.center (L ⧸ N)) :=
    IsCatalogGroup.of_mulEquiv eN hcat
  have hNc : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp GL83.I243.Cover.coprime_card_primeCentre
  have hneN : Subgroup.center (L ⧸ N) ≠ ⊥ := by
    rw [GL83.I243.Cover.center_quotient_eq_map hq]
    intro h
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact hNc (h3.trans (Subgroup.card_dvd_of_le h))
  have hZpN : IsPGroup 3 (Subgroup.center (L ⧸ N)) :=
    GL83.I243.Cover.isPGroup_center_quotient (p := 3) hq
  have hrkN : Open.pRank 3 (⊤ : Subgroup (L ⧸ N)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq N hNc]
    exact hrk
  have hcyc : IsCyclic (Subgroup.center (L ⧸ N)) := by
    by_contra hnc
    have := hN (L ⧸ N) hqN hcatN hZpN hnc
    omega
  rcases hA (L ⧸ N) hqN hcatN hneN hZpN hcyc (by omega) with
    he | he | he | he | ⟨⟨d, hv⟩, hd, he⟩ <;> obtain ⟨e⟩ := he
  · haveI := Hyp111.finite_outer (alternatingGroup (Fin 6))
    exact Hyp111.sylow_normal_outer_of_mulEquiv (eN.symm.trans e) (Hyp111.sylow_normal_of_not_dvd
      (not_dvd_card_outer_alternatingGroup 6 (by norm_num) 3 Nat.prime_three (by norm_num)))
  · haveI := Hyp111.finite_outer (alternatingGroup (Fin 7))
    exact Hyp111.sylow_normal_outer_of_mulEquiv (eN.symm.trans e) (Hyp111.sylow_normal_of_not_dvd
      (not_dvd_card_outer_alternatingGroup 7 (by norm_num) 3 Nat.prime_three (by norm_num)))
  · exact sylow_normal_outer_of_outTowerAt hZ
      (OutTowerAt.of_mulEquiv (eN.symm.trans e) (hT.sporadic .M22 3 Nat.prime_three (by norm_num)))
  · exact sylow_normal_outer_of_outTowerAt hZ
      (OutTowerAt.of_mulEquiv (eN.symm.trans e) (hT.sporadic .ONan 3 Nat.prime_three (by norm_num)))
  · rcases hd with ⟨q, hdq, -⟩ | ⟨q, hdq, -⟩
    · dsimp only at hdq
      subst hdq
      exact Hyp111.sylow_normal_outer_of_mulEquiv (eN.symm.trans e)
        (Hyp111.sylow_normal_outer_A2 (by norm_num) q hv)
    · dsimp only at hdq
      subst hdq
      exact Hyp111.sylow_normal_outer_of_mulEquiv (eN.symm.trans e)
        (Hyp111.sylow_normal_outer_twistedA2 (by norm_num) q hv)

theorem sylow_normal_outer_three_of_quasisimple (hT : ExceptionalTowers)
    (hA : KFactAlphaListM3Wide) (hN : KFactProofs.T29.NoncyclicCentreRank) {L : Type} [Group L]
    [Finite L] (hq : Open.IsQuasisimple L) (hcat : IsCatalogGroup (L ⧸ Subgroup.center L))
    (hrk : Open.pRank 3 (⊤ : Subgroup L) ≤ 2) :
    ∀ P : Sylow 3 (Outer L), (P : Subgroup (Outer L)).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsPerfect L := ⟨hq.1⟩
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hq.2
  refine sylow_normal_of_injective (centerQuotient_outer_injective L) ?_
  by_cases h3 : 3 ∣ Nat.card (Subgroup.center L)
  · exact sylow_normal_outer_three_of_cover hT hA hN hq hcat hrk h3
  · refine sylow_normal_outer_three_of_simple hT
      (CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian L hq) hcat
      (RankLE2.of_pRank Nat.prime_three ?_)
    rw [CFSG.SectionRank.pRank_quotient_eq (Subgroup.center L) h3]
    exact hrk

theorem sevenOneThreeRankTwo_of_kFacts (hT : ExceptionalTowers) (hA : KFactAlphaListM3Wide)
    (hN : KFactProofs.T29.NoncyclicCentreRank) : SevenOneThreeRankTwo := by
  intro X _ _ hK L hL hLn hL3 _
  haveI := hLn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.1.2.1
  have hq : Open.IsQuasisimple L := ⟨hL.1.1.commutator_eq_top, hL.1.2.1⟩
  have hcat : IsCatalogGroup (L ⧸ Subgroup.center L) :=
    (catalogSimpleSections_iff_isKGroup.mpr hK).surjective_image L
      (QuotientGroup.mk' (Subgroup.center L)) (QuotientGroup.mk'_surjective _) hL.1.2.2
  have hrk : Open.pRank 3 (⊤ : Subgroup L) ≤ 2 := by
    have h := CFSG.SectionRank.pRank_le_map Nat.prime_three.one_lt L.subtype L.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype, hL3] at h
  obtain ⟨R⟩ : Nonempty (Sylow 3 X) := inferInstance
  exact isPClosedMod_of_normal_sup_sylow R (Hyp111.normal_sup_sup_centralizer_of_outer L R
    (sylow_normal_outer_three_of_quasisimple hT hA hN hq hcat hrk))

end CFSG.LocalAnalysis.RankThreeTheoremC.SevenFourTwo
