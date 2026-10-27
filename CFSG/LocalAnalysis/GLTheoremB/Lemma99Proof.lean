module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Gamma
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Glue

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Setting

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem le_normalizer_of_block (i113 : Input11_3) (hSt : GLStanding G m p) {B M : Subgroup G}
    (hB : IsBOneMax p B) (hM : IsPreUniquenessTwoLocal p B M) {L : Subgroup G}
    (hL : GLAPComponent p M L) (hbl : IsGLBlock M L) : B ≤ Subgroup.normalizer (L : Set G) := by
  by_contra hnB
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have hBM := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hMtop : M ≠ ⊤ := isTwoLocal_ne_top hSt hM.1.1
  have hnB' : ¬ B.subgroupOf M ≤ Subgroup.normalizer ((L.subgroupOf M : Subgroup ↥M) : Set ↥M) := by
    intro h
    apply hnB
    intro b hb
    have h1 := h ((Subgroup.mem_subgroupOf).2 hb : (⟨b, hBM hb⟩ : ↥M) ∈ B.subgroupOf M)
    rw [normalizer_subgroupOf_eq hL.1] at h1
    exact h1
  have hcen := i113 ↥M (isKGroup_of_isKProper hSt.kProper hMtop) p hp hp2 (B.subgroupOf M)
    (glaIsBmax_subgroupOf hSt hB hM.1.1 hBM) (L.subgroupOf M) (glaPComponent_top hL) hnB'
  apply hcen
  let t : ↥(L.subgroupOf M) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hL.1
  let Φ : (↥(L.subgroupOf M) ⧸ GLAPPrimeCore p ↥(L.subgroupOf M)) ≃*
      (↥L ⧸ GLAPPrimeCore p ↥L) := QuotientGroup.congr _ _ t (glaPPrimeCore_map_iso p t)
  have h1 := Subgroup.map_center_eq Φ
  rw [center_quotient_eq_bot_of_block hp hp2 hL hbl] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ Φ.injective).1 h1

omit [Finite G] in
theorem piLayer_le (p : ℕ) (H : Subgroup G) : piLayer p H ≤ H :=
  iSup₂_le fun _ hJ => hJ.1.1

theorem lemma99_of_inputs (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23)
    (i19 : Input19Delta) (i19' : Input19_1_6) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (h95 : Prop95) (i113 : Input11_3) (i279 : Input27_9_3) : Lemma99 := by
  intro G _ _ m p hSt B M hB hM D hDB hD L hL hnc
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have h91 := lemma91ii_of_inputs i20 i11 l23
  have h94 := lemma94_of_lemma91ii_lemma92 h91 (lemma92_of_inputs h91 i19 i19')
  have hBM := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hΓM : gammaD D ≤ M := (h94 G m p hSt B M hB hM D hDB hD).2
  have hhyp := prop95Hyp_of h91 h94 hSt hB hM hDB hD
  obtain ⟨-, -, h3⟩ := h95 G m p hSt M D hhyp
  obtain ⟨hΓN, hcent | ⟨hbl, hcases⟩⟩ := h3 L hL
  · exact absurd hcent hnc
  have hBL : B ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_block i113 hSt hB hM hL hbl
  have hΓL : gammaD D ≤ Subgroup.normalizer (L : Set G) := fun g hg =>
    mem_normalizer_of_barX_normalizes hp le_rfl hL (hΓM hg) (Subgroup.le_normalizer (hΓM hg))
      (hΓN ⟨⟨g, hΓM hg⟩, (Subgroup.mem_subgroupOf).2 hg, rfl⟩)
  have hData : Lemma99Data p B M D L := by
    rcases hcases with hα | hβ | hγ
    · exact lemma99Data_of_acts i279 hSt hB hM hDB hD hL hΓM hΓN hBL
        (Or.inl (ActsAsTransposition.of_prop95Alpha hα))
    · exact lemma99Data_of_acts i279 hSt hB hM hDB hD hL hΓM hΓN hBL
        (Or.inr (ActsAsTransvection.of_prop95Beta hβ))
    · exact lemma99Data_of_gamma h91 hSt hB hM hDB hD hL hbl hΓM hΓN hBL hnc hγ
  obtain ⟨D₀, K, hD₀, hK, hgen⟩ := hData
  refine ⟨D₀, K, hD₀, fun d hd => ?_, hgen⟩
  obtain ⟨hdD, hd1⟩ := hD₀ d hd
  obtain ⟨hK1, hKπ, hBK, hΓK, hncK⟩ := hK d hd
  have hKM : K d ≤ M := hK1.1.trans (inf_le_left.trans hL.1)
  have hKpi : IsPiGroup p (↥(K d) ⧸ GLAPPrimeCore p ↥(K d)) := isPiGroup_quot_of_barX hp hKM hKπ
  have hKlayer : K d ≤ piLayer p (L ⊓ Subgroup.centralizer ({d} : Set G)) :=
    le_iSup₂_of_le (K d) ⟨hK1, hKpi⟩ le_rfl
  exact ⟨glaPComponent_of_le hp hK1 hKlayer (piLayer_le p _), ⟨hBK, hΓK⟩, hncK,
    lemma99_piece hSch i20 i11 l23 hSt hB hM hDB hdD hd1 hL hΓL hΓM hK1 hKπ hΓK hncK⟩

end Setting

end CFSG.LocalAnalysis.GLTheoremB
