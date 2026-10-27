module

public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows
import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.AGL81TheoremC.CoprimeGamma
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements
import CFSG.LocalAnalysis.RankThreeTheoremC.PConstrainedOvergroups
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.O1517b

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_two_le_pRank {M R Q : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M) (hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M)
    (hQM : Q ≤ M) (hQ : IsPGroup 3 Q) (hQ2 : 2 ≤ CFSG.Open.pRank 3 Q) :
    normalizer (Q : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQsub : IsPGroup 3 (Q.subgroupOf M) := hQ.comap_subtype
  obtain ⟨S, hQS⟩ := hQsub.exists_le_sylow
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup M).map M.subtype) M := ⟨S, rfl⟩
  have hQS' : Q ≤ (S : Subgroup M).map M.subtype := by
    rw [← map_subgroupOf_eq_of_le hQM]
    exact map_mono hQS
  obtain ⟨k, hk, hconj⟩ := hR.exists_mem_conj hSyl
  set φ : MulAut G := MulAut.conj k⁻¹ with hφ
  have hφx : ∀ x : G, φ x = k⁻¹ * x * k := fun x => by simp [hφ, MulAut.conj_apply]
  have hQ'R : Q.map φ.toMonoidHom ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    have := (hconj x).mp (hQS' hx)
    simpa [hφx] using this
  have hrank : 2 ≤ CFSG.Open.pRank 3 (Q.map φ.toMonoidHom) := by
    rwa [CFSG.RankThreeCoreUniqueness.Helpers.pRank_map_automorphism 3 (by norm_num) Q φ]
  have hN : normalizer ((Q.map φ.toMonoidHom : Subgroup G) : Set G) ≤ M :=
    (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 2 3 R _ hQ'R hrank).trans hΓ
  intro g hg
  have h1 : φ g ∈ normalizer ((Q.map φ.toMonoidHom : Subgroup G) : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq]
    exact ⟨g, hg, rfl⟩
  have h2 : k⁻¹ * g * k ∈ M := by
    have := hN h1
    rwa [hφx] at this
  have : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
  rw [this]
  exact M.mul_mem (M.mul_mem hk h2) (M.inv_mem hk)

theorem isSylowOf_of_isSylowOf_inf {M R H P : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M) (hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P (M ⊓ H)) (hP2 : 2 ≤ CFSG.Open.pRank 3 P) :
    CFSG.ABGLocalTools.IsSylowOf 3 P H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.ABGLocalTools.isSylowOf_of_normalizer_inf_le (H := M) (M := H) hP ?_
  exact inf_le_left.trans
    (normalizer_le_of_two_le_pRank hR hΓ (hP.le.trans inf_le_left) hP.isPGroup hP2)

theorem relPPrimeCore_le_of_two_le_pRank {M R H E : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M) (hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M)
    (hEM : E ≤ M) (hEH : E ≤ H) (hE : CFSG.Open.IsElemAbelian 3 E) (hcard : Nat.card E = 27) :
    CFSG.Open.relPPrimeCore 3 H ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine CFSG.LocalAnalysis.AGL81TheoremC.relPPrimeCore_le_of_glbCore_le (p := 3) (k := 2) hE
    (by rw [hcard]; norm_num) hEH ?_
  change CFSG.Open.rankThreeGamma 2 3 E ≤ M
  rw [CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff]
  intro Q hQE hQ2
  exact normalizer_le_of_two_le_pRank hR hΓ (hQE.trans hEM)
    ((CFSG.Open.IsElemAbelian.isPGroup hE).to_le hQE) hQ2

theorem le_of_normal_of_dvd_of_strong {p : ℕ} (hp : p.Prime) {H M N : Subgroup G}
    (hN : (N.subgroupOf H).Normal) (hNH : N ≤ H) (hNM : N ≤ M) (hdvd : p ∣ Nat.card N)
    (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) : H ≤ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hHM
  have hNHM : N ≤ H ⊓ M := le_inf hNH hNM
  have hY := hM.subgroupOf hHM (hdvd.trans (Subgroup.card_dvd_of_le hNHM))
  have hle : N.subgroupOf H ≤ (H ⊓ M).subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hNHM (Subgroup.mem_subgroupOf.mp hx))
  haveI := hN
  refine hY.not_dvd_card_of_normal_le hle ?_
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]

section Lemma5

variable {p : ℕ} [Fact p.Prime] {H : Subgroup G}

theorem le_of_isPConstrained_aux_isSylowOf (Ps : Sylow p H) :
    CFSG.ABGLocalTools.IsSylowOf p ((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H) (CFSG.Op_p'p p H) := by
  have hPs : CFSG.ABGLocalTools.IsSylowOf p (Ps : Subgroup H) ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr
      ⟨le_top, Ps.isPGroup', by rw [relIndex_top_right]; exact Ps.not_dvd_index⟩
  exact hPs.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr inferInstance).ge

theorem le_of_isPConstrained_aux_le_normalizer (Ps : Sylow p H) :
    (Ps : Subgroup H).map H.subtype ≤
      normalizer ((((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype : Subgroup G) : Set G) := by
  have hPQ : (Ps : Subgroup H) ≤
      normalizer (((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H : Subgroup H) : Set H) := by
    refine le_trans (le_inf le_normalizer ?_) inf_normalizer_le_normalizer_inf
    rw [normalizer_eq_top_iff.mpr (CFSG.Op_p'p_normal p H)]
    exact le_top
  exact CFSG.LocalAnalysis.RankThreeTheoremC.map_subtype_le_normalizer_map_subtype hPQ

theorem le_of_isPConstrained_aux_inf_centralizer_le (Ps : Sylow p H)
    (hH : CFSG.ABGLocalTools.IsPConstrained p H) :
    (Ps : Subgroup H).map H.subtype ⊓ centralizer
        ((((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype : Subgroup G) : Set G) ≤
      ((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype := by
  have hcent := hH _ (le_of_isPConstrained_aux_isSylowOf Ps)
  rintro _ ⟨⟨x, hxPs, rfl⟩, hgC⟩
  have hx : x ∈ centralizer (((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H : Subgroup H) : Set H) := by
    rw [mem_centralizer_iff]
    intro q hq
    apply Subtype.ext
    exact mem_centralizer_iff.mp hgC q ⟨q, hq, rfl⟩
  exact ⟨x, ⟨hxPs, hcent hx⟩, rfl⟩

theorem le_of_isPConstrained_aux_le_of_normalizer_le {M : Subgroup G} (Ps : Sylow p H)
    (hKM : (CFSG.pPrimeCore p H).map H.subtype ≤ M)
    (hNR : normalizer ((((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype : Subgroup G) : Set G)
      ≤ M) : H ≤ M := by
  have hsyl := le_of_isPConstrained_aux_isSylowOf Ps
  have hsup : CFSG.pPrimeCore p H ⊔ ((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H) = CFSG.Op_p'p p H :=
    (CFSG.ABGLocalTools.sup_eq_Op_p'p_iff_isSylowOf Ps.isPGroup'.to_inf_left).mpr hsyl
  have hsylG : CFSG.ABGLocalTools.IsSylowOf p
      (((Ps : Subgroup H) ⊓ CFSG.Op_p'p p H).map H.subtype) ((CFSG.Op_p'p p H).map H.subtype) :=
    (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H).mpr hsyl
  have hfrat := CFSG.LocalAnalysis.RankThreeTheoremC.le_sup_normalizer_of_isSylowOf
    (CFSG.ABGLocalTools.le_normalizer_map_subtype H (CFSG.Op_p'p p H)) hsylG
  have hY : (CFSG.Op_p'p p H).map H.subtype ≤ M := by
    rw [← hsup, Subgroup.map_sup]
    exact sup_le hKM (le_normalizer.trans hNR)
  exact hfrat.trans (sup_le hY hNR)

end Lemma5

theorem le_of_isPConstrained_of_three_le_pRank {M R H P : Subgroup G}
    (hR : CFSG.ABGLocalTools.IsSylowOf 3 R M) (hΓ : CFSG.Open.rankThreeGamma 2 3 R ≤ M)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P H) (hPM : P ≤ M) (hP3 : 3 ≤ CFSG.Open.pRank 3 P)
    (hH : CFSG.ABGLocalTools.IsPConstrained 3 ↥H) (hK : CFSG.Open.relPPrimeCore 3 H ≤ M) :
    H ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Ps, rfl⟩ := hP
  set P : Subgroup G := (Ps : Subgroup H).map H.subtype
  set U : Subgroup G := ((Ps : Subgroup H) ⊓ CFSG.Op_p'p 3 H).map H.subtype
  have hUP : U ≤ P := Subgroup.map_mono inf_le_left
  have hPp : IsPGroup 3 P := Ps.isPGroup'.map H.subtype
  have hUp : IsPGroup 3 U := hPp.to_le hUP
  have hPnorm : P ≤ normalizer (U : Set G) := le_of_isPConstrained_aux_le_normalizer Ps
  have hC : P ⊓ centralizer (U : Set G) ≤ U := le_of_isPConstrained_aux_inf_centralizer_le Ps hH
  have hU2 : 2 ≤ CFSG.Open.pRank 3 U := by
    by_cases hcyc : IsCyclic U
    · exfalso
      obtain ⟨A, hAP, hA, hAc⟩ :=
        CFSG.RankThreeCoreUniqueness.Helpers.pRank_attained 3 P (by omega)
      have hle := CFSG.LocalAnalysis.RankThreeTheoremC.card_le_of_isCyclic_of_centralizer_le
        (p := 3) (by norm_num) hPp hUP hPnorm hC hcyc hAP hA
      rw [hAc] at hle
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 hle
      omega
    · exact CFSG.LocalAnalysis.RankThreeTheoremC.two_le_pRank_of_not_isCyclic Nat.prime_three
        (by norm_num) hUp hcyc
  have hNU : normalizer (U : Set G) ≤ M :=
    normalizer_le_of_two_le_pRank hR hΓ (hUP.trans hPM) hUp hU2
  have hKM : (CFSG.pPrimeCore 3 H).map H.subtype ≤ M :=
    (CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple.relPPrimeCore_eq_map
      Nat.prime_three H).ge.trans hK
  exact le_of_isPConstrained_aux_le_of_normalizer_le Ps hKM hNU

end CFSG.LocalAnalysis.RankThreeUC.S15.O1517b
