module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseSylow
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3Sp62CloseXfer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscapeAux
import CFSG.LocalAnalysis.AGLEmbedding.Sp48DataDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

theorem sp62Close_frame [Fact (Nat.Prime 3)] (hSchur : KFactChevTwoSurvivorSchur)
    (hK1 : KFactSp62Frame) {P : Sylow 3 G} {M H R L : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)} {d : TauCeti.ValidLieTypeIndex}
    (c : Sp62CloseCtx P M H R L Rbar K d) :
    ∃ (J : Subgroup G) (b : G), ElemFrame3 (P : Subgroup G) J (Subgroup.zpowers b) ∧ J ≤ H ∧
      48 ∣ (Subgroup.centralizer (J : Set G)).relIndex (Subgroup.normalizer (J : Set G) ⊓ H) ∧
      (Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G)).relIndex
        (Subgroup.normalizer (J : Set G) ⊓ H) = 3 ∧
      ¬ Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) ≤ M := by
  set O := primeComplementCore (G := H) 3 with hO
  set π := QuotientGroup.mk' O with hπ
  obtain ⟨hZ, -, ⟨eK⟩, -⟩ := stmtChevTwoSocle3_of hSchur 3 P M H R Rbar c.cfg K c.comp c.uniq
    c.cent d (Or.inl ⟨rfl, c.idx⟩) c.iso
  have hCK := c.cfg.centralizer_eq_bot c.comp c.uniq c.cent hZ
  obtain ⟨Jb, bb, hJbT, hJbel, hJbcard, hJbuniq, hJbcent, hJb48, hbbJ, hbb3, hbbidx, hbbY⟩ :=
    hK1 _ K d c.idx (normal_of_forall_isComponentOf_eq c.comp c.uniq) ⟨eK⟩ hCK Rbar
  have hRH : R ≤ H := c.cfg.ext.le_H
  have hR3 : IsPGroup 3 R := c.cfg.ext.isPGroup
  have hRM : R ≤ M := c.rp ▸ c.cfg.ext.sylow_le
  have hrbar : (Rbar : Subgroup (H ⧸ O)) = (R.subgroupOf H).map π := c.cfg.rbar
  have hOcop : Nat.Coprime 3 (Nat.card O) := primeComplementCore_coprime 3
  have hPR : (P : Subgroup G) = R := c.rp.symm
  obtain ⟨J, hJH, hJR, hJmap, hJlift, ψ, -⟩ :=
    exists_lift_of_le_map Nat.prime_three hRH hR3 O hOcop (hJbT.trans hrbar.le)
  have hJ3 : IsPGroup 3 J := hR3.to_le hJR
  have hJel : IsElemAbelian 3 J := isElemAbelian_of_mulEquiv ψ hJbel
  have hJcard : Nat.card J = 3 ^ 3 := by
    rw [Nat.card_congr ψ.toEquiv]
    exact hJbcard
  have hbbR : bb ∈ (R.subgroupOf H).map π := hrbar ▸ hJbT hbbJ
  obtain ⟨x, hxR, hxπ⟩ := hbbR
  have hbR : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hxR
  have hbJ : (x : G) ∈ J := hJlift x hbR (hxπ ▸ hbbJ)
  have hbH : (x : G) ∈ H := x.2
  have hbord : orderOf (x : G) = 3 := by
    rw [← orderOf_mk_eq_of_isPGroup hRH hR3 hbR]
    have : π ⟨(x : G), hRH hbR⟩ = bb := hxπ
    rw [this]
    exact hbb3
  have hBJ : Subgroup.zpowers (x : G) ≤ J := Subgroup.zpowers_le.mpr hbJ
  have hBmap : ((Subgroup.zpowers (x : G)).subgroupOf H).map π = Subgroup.zpowers bb :=
    (map_mk_subgroupOf_zpowers O hbH).trans (by rw [hπ] at hxπ; exact congrArg _ hxπ)
  refine ⟨J, x, ⟨hPR ▸ hJR, hJel, hJcard, hBJ, ?_, ?_, ?_⟩, hJH, ?_, ?_, ?_⟩
  ·
    rw [Nat.card_zpowers, hbord]
  ·
    intro J' hJ'P hJ'el hJ'card
    have hJ'R : J' ≤ R := hPR ▸ hJ'P
    have hJ'H : J' ≤ H := hJ'R.trans hRH
    have hJ'bT : (J'.subgroupOf H).map π ≤ (Rbar : Subgroup (H ⧸ O)) :=
      hrbar ▸ Subgroup.map_mono (Subgroup.comap_mono hJ'R)
    have hJ'bel : IsElemAbelian 3 ((J'.subgroupOf H).map π) :=
      CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 3
        (isElemAbelian_subgroupOf hJ'el H) π
    have hJ'bcard : Nat.card ((J'.subgroupOf H).map π) = 3 ^ 3 := by
      have h1 : Nat.card ((J'.subgroupOf H).map π) = Nat.card (J'.subgroupOf H) :=
        card_map_mk_of_isPGroup Nat.prime_three O hOcop (hR3.to_le hJ'R).comap_subtype
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJ'H).toEquiv]
      exact hJ'card
    have heq : (J'.subgroupOf H).map π = Jb := hJbuniq _ hJ'bT hJ'bel hJ'bcard
    have hJ'J : J' ≤ J := fun y hy =>
      hJlift ⟨y, hJ'H hy⟩ (hJ'R hy)
        (heq ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy))
    exact Subgroup.eq_of_le_of_card_ge hJ'J (by rw [hJ'card, hJcard])
  ·
    rintro y ⟨hyP, hyC⟩
    have hyR : y ∈ R := hPR ▸ hyP
    have hyH : y ∈ H := hRH hyR
    have hmem : π ⟨y, hyH⟩ ∈ (Rbar : Subgroup (H ⧸ O)) ⊓ Subgroup.centralizer (Jb : Set _) :=
      ⟨hrbar ▸ ⟨⟨y, hyH⟩, Subgroup.mem_subgroupOf.mpr hyR, rfl⟩,
        Subgroup.mem_centralizer_iff.mpr fun jb hjb => by
          rw [← hJmap] at hjb
          obtain ⟨j, hj, rfl⟩ := hjb
          have hcomm := Subgroup.mem_centralizer_iff.mp hyC j (Subgroup.mem_subgroupOf.mp hj)
          rw [← map_mul, ← map_mul]
          exact congrArg π (Subtype.ext hcomm)⟩
    exact hJlift ⟨y, hyH⟩ hyR (hJbcent hmem)
  ·
    have h3 := relIndex_centralizer_eq_of_quotient Nat.prime_three O hOcop hJH hJ3
    rw [hJmap] at h3
    rw [h3]
    exact hJb48
  ·
    have h4 := relIndex_normalizer_eq_of_quotient Nat.prime_three O hOcop hJH hBJ hJ3
    rw [hBmap, hJmap] at h4
    rw [h4]
    exact hbbidx
  ·
    intro hCM
    have hX0T : (Rbar : Subgroup (H ⧸ O)) ≤ ((H ⊓ M).subgroupOf H).map π :=
      hrbar ▸ Subgroup.map_mono (Subgroup.comap_mono (le_inf hRH hRM))
    refine hbbY _ hX0T c.cfg.red.ne_top fun y hy => ?_
    have he : IsPGroup 3 (Subgroup.zpowers x) :=
      hR3.comap_subtype.to_le (Subgroup.zpowers_le.mpr hxR)
    have hy' : y ∈ Subgroup.centralizer ({π x} : Set (H ⧸ O)) := by
      rw [hxπ]
      exact hy
    obtain ⟨g, hg, rfl⟩ := exists_mem_centralizer_mk_eq Nat.prime_three O hOcop he hy'
    have hgc : (g : G) * (x : G) = (x : G) * (g : G) :=
      congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
    have hgC : (g : G) ∈
        Subgroup.centralizer ((Subgroup.zpowers (x : G) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_left (Commute.symm (show Commute (g : G) (x : G) from hgc)) k).eq)
    exact ⟨g, Subgroup.mem_subgroupOf.mpr ⟨g.2, hCM hgC⟩, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC
