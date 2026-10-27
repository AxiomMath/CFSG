module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511D
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K89Sp
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1511Defs

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup

theorem exists_sylow_of_K89Sp_aux1 {X Y : Type} [Group X] [Group Y] {A : Subgroup X}
    {B : Subgroup Y} (f : A ≃* B) (h : IsLThreeTwoPow (↥B ⧸ CFSG.pCore 2 ↥B)) :
    IsLThreeTwoPow (↥A ⧸ CFSG.pCore 2 ↥A) :=
  isLThreeTwoPow_of_mulEquiv_aux1
    (QuotientGroup.congr (CFSG.pCore 2 ↥A) (CFSG.pCore 2 ↥B) f (CFSG.pCore_map_iso 2 f)) h

theorem exists_sylow_of_K89Sp (hK : K89Sp) {G : Type} [Group G] [Finite G] {M H : Subgroup G}
    (hHK : IsKGroup ↥H) (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M) (hHM : ¬ H ≤ M)
    {Y : Subgroup G} (hY : Y ≤ H ⊓ M) (hrk : CFSG.Open.pRank 3 (H ⊓ M) ≤ 1)
    (hYq : IsLThreeTwoPow (↥Y ⧸ CFSG.pCore 2 ↥Y)) (h3 : 3 ∣ Nat.card Y) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S H ∧ S ≤ M ∧
      normalizer (S : Set G) ⊓ H ≤ M := by
  have hNH : H ⊓ M ≤ H := inf_le_left
  have h3N : 3 ∣ Nat.card ↥(H ⊓ M) := h3.trans (Subgroup.card_dvd_of_le hY)
  have hSP := isStronglyPEmbedded_subgroupOf_inf hM hHM h3N
  have hrkN : CFSG.Open.pRank 3 ((H ⊓ M).subgroupOf H) ≤ 1 := by
    rw [CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 3 Nat.prime_three _ _
      (Subgroup.subgroupOfEquivOfLe hNH)]
    exact hrk
  have hYH : Y ≤ H := hY.trans inf_le_left
  have hY' : Y.subgroupOf H ≤ (H ⊓ M).subgroupOf H := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hY (Subgroup.mem_subgroupOf.mp hx))
  have hYq' : IsLThreeTwoPow (↥(Y.subgroupOf H) ⧸ CFSG.pCore 2 ↥(Y.subgroupOf H)) :=
    exists_sylow_of_K89Sp_aux1 (Subgroup.subgroupOfEquivOfLe hYH) hYq
  have hHK' : CFSG.Open.IsKGroup ↥H := CFSG.KCore.KGroupAllSimple.kGroupNonab hHK
  obtain ⟨S', hS'syl, hS'N, hS'norm⟩ :=
    hK ↥H hHK' ((H ⊓ M).subgroupOf H) (Y.subgroupOf H) hSP hrkN hY' hYq'
  refine ⟨S'.map H.subtype, ?_, ?_, ?_⟩
  · have h1 := (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff H (A := S') (B := ⊤)).mpr hS'syl
    have htop : (⊤ : Subgroup ↥H).map H.subtype = H := by
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, Subgroup.mem_top _, rfl⟩
    rw [htop] at h1
    exact h1
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hS'N hy))).2
  · intro g hg
    obtain ⟨hgN, hgH⟩ := Subgroup.mem_inf.mp hg
    have hmemS : ∀ y : ↥H, (y : G) ∈ S'.map H.subtype ↔ y ∈ S' := fun y =>
      Subgroup.mem_map_iff_mem H.subtype_injective
    have hg'N : (⟨g, hgH⟩ : ↥H) ∈ normalizer (S' : Set ↥H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      exact (hmemS y).symm.trans ((Subgroup.mem_normalizer_iff.mp hgN (y : G)).trans
        (hmemS (⟨g, hgH⟩ * y * (⟨g, hgH⟩ : ↥H)⁻¹)))
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hS'norm hg'N))).2

open KFactsPair in
theorem false_of_Y_O2form_gen (hK89 : K89Sp) (hK3 : K3DvdL3) {G : Type} [Group G] [Finite G]
    {M T : Subgroup G} (hstand : CFSG.LocalAnalysis.AGL81TheoremCD.StandingGen G)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M)
    (hN : ¬ normalizer (T : Set G) ≤ M)
    (hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M)
    {Ti : Subgroup ↥M} (hne : Ti ≠ ⊥) (hle : Ti ≤ T.subgroupOf M)
    (hchar : (Ti.subgroupOf (T.subgroupOf M)).Characteristic)
    (hrk : CFSG.Open.pRank 3 (normalizer (Ti : Set ↥M)) ≤ 1)
    {Y : Subgroup ↥M} (hY : Y ≤ normalizer (Ti : Set ↥M))
    (hYq : IsLThreeTwoPow (↥Y ⧸ CFSG.pCore 2 ↥Y)) : False := by
  have hTM : T ≤ M := hT.le
  obtain ⟨hTi'T, hTi'char⟩ := map_subtype_characteristic hTM hle hchar
  have hTi'M : Ti.map M.subtype ≤ M := Subgroup.map_subtype_le Ti
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G,
      normalizer ((Ti.map M.subtype : Subgroup G) : Set G) = H := ⟨_, rfl⟩
  have hND : normalizer (T : Set G) ≤ H := by
    rw [← hHdef]
    exact normalizer_le_normalizer_of_characteristic hTi'T hTi'char
  have hTN : T ≤ normalizer (T : Set G) := Subgroup.le_normalizer
  have hTH : T ≤ H := hTN.trans hND
  have hHM : ¬ H ≤ M := fun h => hN (hND.trans h)
  have hMtop : M ≠ ⊤ := fun h => hN (by rw [h]; exact le_top)
  have hTi'ne : Ti.map M.subtype ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have hxG : (x : G) ∈ Ti.map M.subtype := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hxG
    rw [Subgroup.mem_bot]
    exact Subtype.ext hxG
  have hHtop : H ≠ ⊤ := by
    intro htop
    rw [← hHdef] at htop
    have hnorm : (Ti.map M.subtype).Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hstand.simple.eq_bot_or_eq_top_of_normal (Ti.map M.subtype) with h | h
    · exact hTi'ne h
    · have htopM : (⊤ : Subgroup G) ≤ M := by
        rw [← h]
        exact hTi'M
      exact hMtop (top_le_iff.mp htopM)
  have hHK0 : CFSG.Open.IsKGroup ↥H := hstand.kProper.isKGroup H hHtop
  have hHK : CFSG.IsKGroup ↥H :=
    CFSG.KCore.KGroupNonab.kGroupAllSimple CFSG.Assembly.inCatalog_isoInvariant
      CFSG.Assembly.inCatalog_containsAbelianSimple hHK0
  have hInf : H ⊓ M = (normalizer (Ti : Set ↥M)).map M.subtype := by
    rw [← hHdef]
    exact false_of_threeComponent_aux2 Ti
  have hY' : Y.map M.subtype ≤ H ⊓ M := by
    rw [hInf]
    exact Subgroup.map_mono hY
  have hrk' : CFSG.Open.pRank 3 (H ⊓ M) ≤ 1 := by
    rw [hInf, ← CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 3
      Nat.prime_three _ _
      ((normalizer (Ti : Set ↥M)).equivMapOfInjective M.subtype M.subtype_injective)]
    exact hrk
  have hYq' : IsLThreeTwoPow (↥(Y.map M.subtype) ⧸ CFSG.pCore 2 ↥(Y.map M.subtype)) :=
    exists_sylow_of_K89Sp_aux1 (Y.equivMapOfInjective M.subtype M.subtype_injective).symm hYq
  have h3 : 3 ∣ Nat.card ↥(Y.map M.subtype) := by
    rw [Subgroup.card_map_of_injective M.subtype_injective]
    exact (hK3 _ hYq).trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨S, hS, hSM, hSN⟩ :=
    exists_sylow_of_K89Sp hK89 hHK hstrong hHM hY' hrk' hYq' h3
  have hfin := normalizer_inf_le_of_sylow hT hTH hS hSM hSN
  exact hN (fun x hx => hfin (Subgroup.mem_inf.mpr ⟨hx, hND hx⟩))

end CFSG.LocalAnalysis.RankThreeUC.S15
