module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217Structure

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoProof
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTen
import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineEightB
import CFSG.ClassicalGroups.PCoreSection

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.AGL81C

variable {G : Type} [Group G] [Finite G] {M Q H F : Subgroup G} {q : ℕ}

theorem isNineThreeIndex_of_isNineFourIndex {p : ℕ} {i : TauCeti.CFSGIndex}
    (h : CFSG.LocalAnalysis.RankThreeTheoremC.IsNineFourIndex p i) :
    CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.IsNineThreeIndex p i := by
  cases i with
  | cyclic n m => exact h
  | alternating n hn =>
      rcases h with ⟨hp3, hn6⟩ | ⟨hp5, hn10⟩
      · exact Or.inl ⟨hp3, Or.inl hn6⟩
      · exact Or.inr ⟨hp5, hn10⟩
  | sporadic s =>
      rcases h with ⟨hp3, hs⟩ | ⟨hp5, hs⟩ | ⟨hp11, hs⟩
      · exact Or.inl ⟨hp3, Or.inl hs⟩
      · exact Or.inr (Or.inl ⟨hp5, Or.inl hs⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨hp11, hs⟩))
  | lie d =>
      obtain ⟨d1, hv⟩ := d
      rcases h with h1 | h2 | h3 | h4 | h5
      · obtain ⟨r, hrp, hre, hrd⟩ := h1
        exact Or.inl ⟨r, hrp, hre, hrd⟩
      · obtain ⟨r, hrp, hrd⟩ := h2
        exact Or.inr (Or.inl ⟨r, hrp, hrd⟩)
      · obtain ⟨hp3, m, hmd⟩ := h3
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3, m, hmd⟩))))
      · obtain ⟨hp3, h4a | h4b⟩ := h4
        · obtain ⟨r, hrp, hre, hrd⟩ := h4a
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3,
            Or.inl ⟨r, hrp, hre, Or.inl hrd⟩⟩)))))
        · obtain ⟨r, hrp, hre, hrd⟩ := h4b
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hp3,
            Or.inr (Or.inl ⟨r, hrp, hre, hrd⟩)⟩)))))
      · obtain ⟨hp5, h5a | h5b⟩ := h5
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp5, Or.inl h5a⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hp5,
            Or.inr (Or.inl h5b)⟩)))))

private theorem starImg_inf_centralizer_eq_bot (s : Setting1417 G M Q H F q)
    {S : Subgroup G} (hSH : S ≤ H) (hSX : S ⊓ AGL81C.xSub q M H = ⊥) :
    AGL81C.starImg q H S ⊓
      Subgroup.centralizer (AGL81C.kStar q M H : Set (StarGroup q H)) = ⊥ := by
  classical
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  let π : ↥H →* StarGroup q H := QuotientGroup.mk' O
  have hxSub : (AGL81C.xSub q M H).subgroupOf H =
      (Subgroup.centralizer (AGL81C.kStar q M H : Set (StarGroup q H))).comap π := by
    dsimp only [AGL81C.xSub, CFSG.AGLEmbedding.d1PlusCore]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  rw [eq_bot_iff]
  intro y hy
  rcases hy with ⟨hyS, hyC⟩
  obtain ⟨x, hxS, rfl⟩ := Subgroup.mem_map.mp hyS
  have hxX : x ∈ (AGL81C.xSub q M H).subgroupOf H := by
    rw [hxSub]
    exact hyC
  have hx : x ∈ (S ⊓ AGL81C.xSub q M H).subgroupOf H := by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨Subgroup.mem_subgroupOf.mp hxS, Subgroup.mem_subgroupOf.mp hxX⟩
  rw [hSX] at hx
  rw [Subgroup.bot_subgroupOf, Subgroup.mem_bot] at hx
  rw [hx, map_one, Subgroup.mem_bot]

private theorem card_le_card_starImg (s : Setting1417 G M Q H F q) {S : Subgroup G}
    (hSH : S ≤ H) (hSX : S ⊓ AGL81C.xSub q M H = ⊥) :
    Nat.card ↥S ≤ Nat.card ↥(AGL81C.starImg q H S) := by
  classical
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  let π : ↥H →* StarGroup q H := QuotientGroup.mk' O
  have hxSub : (AGL81C.xSub q M H).subgroupOf H =
      (Subgroup.centralizer (AGL81C.kStar q M H : Set (StarGroup q H))).comap π := by
    dsimp only [AGL81C.xSub, CFSG.AGLEmbedding.d1PlusCore]
    exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  let φ : ↥S → ↥(AGL81C.starImg q H S) := fun a =>
    ⟨π ⟨(a : G), hSH a.2⟩, by
      rw [AGL81C.starImg]
      exact Subgroup.mem_map.mpr ⟨⟨(a : G), hSH a.2⟩,
        Subgroup.mem_subgroupOf.mpr a.2, rfl⟩⟩
  refine Nat.card_le_card_of_injective φ ?_
  intro a b hab
  apply Subtype.ext
  have hπ : π ⟨(a : G), hSH a.2⟩ = π ⟨(b : G), hSH b.2⟩ := congrArg Subtype.val hab
  have hprod : (⟨(a : G), hSH a.2⟩ : ↥H)⁻¹ * ⟨(b : G), hSH b.2⟩ = 1 := by
    have h1 : (⟨(a : G), hSH a.2⟩ : ↥H)⁻¹ * ⟨(b : G), hSH b.2⟩ ∈ O := by
      rw [← QuotientGroup.eq_one_iff (N := O)]
      change π ((⟨(a : G), hSH a.2⟩ : ↥H)⁻¹ * ⟨(b : G), hSH b.2⟩) = 1
      rw [map_mul, map_inv, hπ, inv_mul_cancel]
    have h2 : (⟨(a : G), hSH a.2⟩ : ↥H)⁻¹ * ⟨(b : G), hSH b.2⟩ ∈ S.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact S.mul_mem (S.inv_mem a.2) b.2
    have h3 : (⟨(a : G), hSH a.2⟩ : ↥H)⁻¹ * ⟨(b : G), hSH b.2⟩ ∈
        (AGL81C.xSub q M H).subgroupOf H := by
      rw [hxSub]
      show π ((⟨(a : G), hSH a.2⟩ : ↥H)⁻¹ * ⟨(b : G), hSH b.2⟩) ∈
        Subgroup.centralizer (AGL81C.kStar q M H : Set (StarGroup q H))
      rw [map_mul, map_inv, hπ, inv_mul_cancel]
      exact Subgroup.one_mem _
    have h4 : (⟨(a : G), hSH a.2⟩ : ↥H)⁻¹ * ⟨(b : G), hSH b.2⟩ ∈
        (S ⊓ AGL81C.xSub q M H).subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact ⟨Subgroup.mem_subgroupOf.mp h2, Subgroup.mem_subgroupOf.mp h3⟩
    rw [hSX] at h4
    rwa [Subgroup.bot_subgroupOf, Subgroup.mem_bot] at h4
  have hval : (a : G) = (b : G) := by
    have h := congrArg (fun z : ↥H => (z : G)) hprod
    exact inv_mul_eq_one.mp (by simpa using h)
  exact hval

private theorem exists_sylow_kStar_data (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen) {S : Subgroup G} (hSHM : S ≤ H ⊓ M)
    (hSnormal : (S.subgroupOf (H ⊓ M)).Normal) :
    ∃ (T : Sylow q ↥(AGL81C.kStar q M H)),
      (AGL81C.kStar q M H).Normal ∧
      (T : Subgroup ↥(AGL81C.kStar q M H)).map (AGL81C.kStar q M H).subtype ≤
        Subgroup.normalizer (AGL81C.starImg q H S : Set (StarGroup q H)) := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let O : Subgroup ↥H :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q
  haveI hOn : O.Normal := by
    change (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q).Normal
    infer_instance
  let π : ↥H →* StarGroup q H := QuotientGroup.mk' O
  let Kstar : Subgroup (StarGroup q H) := AGL81C.kStar q M H
  have hstruct := s.kStructure h1
  have hKnormal : Kstar.Normal :=
    hstruct.1.map π (QuotientGroup.mk'_surjective O)
  haveI : Kstar.Normal := hKnormal
  have hSH : S ≤ H := hSHM.trans inf_le_left
  have hHM_le_normS : H ⊓ M ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hSHM).mp hSnormal
  have hQN : Q.subgroupOf H ≤ Subgroup.normalizer (S.subgroupOf H : Set ↥H) := by
    have h1 : Q ≤ Subgroup.normalizer (S : Set G) :=
      (le_inf s.nine.Q_le_H s.Q_le_M).trans hHM_le_normS
    have h2 : (Subgroup.normalizer (S : Set G)).subgroupOf H =
        Subgroup.normalizer (S.subgroupOf H : Set ↥H) :=
      Subgroup.subgroupOf_normalizer_eq hSH
    rw [← h2]
    exact Subgroup.comap_mono h1
  have hQstar_le : AGL81C.starImg q H Q ≤
      Subgroup.normalizer (AGL81C.starImg q H S : Set (StarGroup q H)) := by
    have hmap := Subgroup.le_normalizer_map (f := π) (H := S.subgroupOf H)
    exact (Subgroup.map_mono hQN).trans hmap
  have hQbar : CFSG.ABGLocalTools.IsSylowOf q (AGL81C.starImg q H Q) ⊤ :=
    s.isSylowOf_starImg s.sylowH
  have hKstar_syl : CFSG.ABGLocalTools.IsSylowOf q
      (AGL81C.starImg q H Q ⊓ Kstar) Kstar :=
    hQbar.inf_of_le_normalizer le_top
      (Subgroup.le_normalizer_of_normal (H := Kstar))
  obtain ⟨T, hT⟩ := hKstar_syl.exists_sylow_eq_subgroupOf
  have hTmap : (T : Subgroup ↥Kstar).map Kstar.subtype =
      AGL81C.starImg q H Q ⊓ Kstar := by
    rw [hT, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hTnorm : (T : Subgroup ↥Kstar).map Kstar.subtype ≤
      Subgroup.normalizer (AGL81C.starImg q H S : Set (StarGroup q H)) := by
    rw [hTmap]
    exact inf_le_left.trans hQstar_le
  exact ⟨T, hKnormal, hTnorm⟩

theorem Setting1417.card_pCoreOf_two_le_two (s : Setting1417 G M Q H F q)
    (h1 : NineFourTwoSigmaGen)
    (hNT : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.KFactNineThreeNoTwo)
    (hL34 : KFactL34InvTwo) :
    Nat.card ↥(CFSG.Open.pCoreOf 2 (H ⊓ M)) ≤ 2 := by
  classical
  haveI : Fact q.Prime := ⟨s.qPrime⟩
  let S : Subgroup G := CFSG.Open.pCoreOf 2 (H ⊓ M)
  change Nat.card ↥S ≤ 2
  have hSHM : S ≤ H ⊓ M := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 (H ⊓ M)
  have hSH : S ≤ H := hSHM.trans inf_le_left
  have hSX : S ⊓ AGL81C.xSub q M H = ⊥ := by
    have h := s.nine.nineEight_three
    rw [s.pCoreOf_two_eq_bot] at h
    exact h
  have hSstar_inf := starImg_inf_centralizer_eq_bot s hSH hSX
  have hcardS := card_le_card_starImg s hSH hSX
  have hSstar_p : IsPGroup 2 (AGL81C.starImg q H S) := by
    have hS2 : IsPGroup 2 S :=
      CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 (H ⊓ M)
    exact (hS2.comap_subtype (K := H)).map (QuotientGroup.mk'
      (CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) q))
  have hSnormal : (S.subgroupOf (H ⊓ M)).Normal := by
    have hseq : S.subgroupOf (H ⊓ M) = CFSG.pCore 2 ↥(H ⊓ M) := by
      dsimp only [S, CFSG.Open.pCoreOf]
      exact Subgroup.comap_map_eq_self_of_injective (H ⊓ M).subtype_injective _
    rw [hseq]
    infer_instance
  obtain ⟨T, hKnormal, hTnorm⟩ := exists_sylow_kStar_data s h1 hSHM hSnormal
  let Kstar : Subgroup (StarGroup q H) := AGL81C.kStar q M H
  haveI : Kstar.Normal := hKnormal
  have hstruct := s.kStructure h1
  by_cases h34 : q = 3 ∧ CFSG.AGLEmbedding.IsLinThreeFour ↥Kstar
  ·
    obtain ⟨rfl, h34⟩ := h34
    have hrel : (Subgroup.centralizer (Kstar : Set (StarGroup 3 H))).relIndex
        (AGL81C.starImg 3 H S) ≤ 2 :=
      hL34 (StarGroup 3 H) Kstar hKnormal h34 T (AGL81C.starImg 3 H S) hSstar_p hTnorm
    have hcardSstar : Nat.card ↥(AGL81C.starImg 3 H S) ≤ 2 := by
      have h := Subgroup.relIndex_mul_card
        (H := Subgroup.centralizer (Kstar : Set (StarGroup 3 H)))
        (K := AGL81C.starImg 3 H S)
      rw [inf_comm, hSstar_inf, Subgroup.card_bot, mul_one] at h
      rw [← h]
      exact hrel
    exact hcardS.trans hcardSstar
  ·
    obtain ⟨i, hi4, hiso⟩ := hstruct.2.2.2.2
    have hi3 : CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111.IsNineThreeIndex q i :=
      isNineThreeIndex_of_isNineFourIndex hi4
    have hcent : AGL81C.starImg q H S ≤
        Subgroup.centralizer (Kstar : Set (StarGroup q H)) :=
      hNT q (StarGroup q H) Kstar hKnormal s.qPrime s.q_ne_two ⟨i, hi3, hiso⟩ h34
        T (AGL81C.starImg q H S) hSstar_p hTnorm
    have hSstar_bot : AGL81C.starImg q H S = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyC := hcent hy
      have hmem : y ∈ AGL81C.starImg q H S ⊓
          Subgroup.centralizer (Kstar : Set (StarGroup q H)) := ⟨hy, hyC⟩
      rwa [hSstar_inf, Subgroup.mem_bot] at hmem
    have hcardSstar : Nat.card ↥(AGL81C.starImg q H S) = 1 := by
      rw [hSstar_bot, Subgroup.card_bot]
    omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.O1217
