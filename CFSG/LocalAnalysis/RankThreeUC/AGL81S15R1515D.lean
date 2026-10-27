module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RowStmts
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512B
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512E
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1512F
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1515A

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup KFactsPair
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

section Row1516

variable {X : Type} [Group X] [Finite X]

@[expose] def KA10Gen : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (Ls P₁ P₂ : Subgroup Y),
    Nonempty (↥Ls ≃* alternatingGroup (Fin 10)) → P₁ ≤ Ls → P₂ ≤ Ls →
    Nonempty (↥P₁ ≃* Equiv.Perm (Fin 8)) → IsTwoFourSFive P₂ → oddHull P₁ ⊔ oddHull P₂ = Ls

theorem lift_alt_data (hAlt : LieOddRankAlt) (hKSMAlt : KSMAlt) {T L : Subgroup X}
    {Ls : Subgroup (X ⧸ gnC T)} (hX : GNSetting X T) (hLs : IsComponentOf Ls ⊤)
    (hL : LiftOf T L Ls) {n : ℕ} (hn : 8 ≤ n)
    (e : Nonempty (↥Ls ≃* alternatingGroup (Fin n))) :
    Nat.card (Subgroup.center ↥(barO2 L)) = 1 ∧ AltRanks T L n := by
  obtain ⟨⟨eQ⟩, -, hodd⟩ := centre_of_lift hX hLs hL
  obtain ⟨e'⟩ := e
  obtain ⟨-, ⟨e''⟩⟩ := quotCenter_equiv_alt (by omega : 4 ≤ n) e'
  have hK : CFSG.Open.IsQuasisimple ↥(barO2 L) := hL.1.component.2.2
  have hZ : Nat.card (Subgroup.center ↥(barO2 L)) = 1 :=
    (hKSMAlt ↥(barO2 L) hK n ⟨eQ.trans e''⟩ (centre_barO2_odd hL.1)).2 hn
  refine ⟨hZ, fun r hr hr2 => ?_⟩
  have h1 := hAlt ↥(barO2 L) hK n (by omega) ⟨eQ.trans e''⟩ r hr hr2
  exact ((pRank_barO2_eq hL.1 hr hr2).trans
    (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barO2 L))).trans h1

theorem pRank_eq_div_of_alt_s15 (hAlt : LieOddRankAlt) {Y : Type} [Group Y] [Finite Y] {Ls : Subgroup Y}
    (hLs : IsComponentOf Ls ⊤) {n : ℕ} (hn : 5 ≤ n) (e : Nonempty (↥Ls ≃* alternatingGroup (Fin n)))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : CFSG.Open.pRank r Ls = n / r := by
  obtain ⟨e'⟩ := e
  obtain ⟨-, ⟨e''⟩⟩ := quotCenter_equiv_alt (by omega : 4 ≤ n) e'
  have := hAlt ↥Ls hLs.2.2 n hn ⟨e''⟩ r hr hr2
  rw [← this]
  exact CFSG.SectionRank.pRank_eq_pRank_top_subgroup Ls

theorem false_of_two_components_pRank_three {T T₁ T₂ : Subgroup X} (hthree : GNThree T T₁ T₂)
    {Ls Is : Subgroup (X ⧸ gnC T)} {L I : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hIs : GNYComponent T T₁ T₂ Is) (hL : LiftOf T L Ls) (hI : LiftOf T I Is) (hne : Ls ≠ Is)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barO2 L)))
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3) (hL3 : 3 ≤ CFSG.Open.pRank 3 L) : False := by
  have hLI : L ≠ I := by
    rintro rfl
    exact hne (hL.2.symm.trans hI.2)
  have hs : CFSG.Open.pRank 3 ((Subgroup.center ↥(barO2 L)).map (barO2 L).subtype) ≤ 0 := by
    have h0 := pRank_eq_zero_of_not_dvd_s15 (A := KFactsPair.centerIn (barO2 L)) Nat.prime_three
      (by
        unfold KFactsPair.centerIn
        rw [Subgroup.card_map_of_injective (barO2 L).subtype_injective]
        exact hZ)
    unfold KFactsPair.centerIn at h0
    exact h0.le
  have hsum := pRank_add_le_pRank_sup hL.1 hI.1 hLI Nat.prime_three (by norm_num) hs
  have hLI3 : CFSG.Open.pRank 3 (L ⊔ I) ≤ 3 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans hX3
  have h3Is : 3 ∣ Nat.card ↥Is := by
    by_contra h3
    apply (hthree Is hIs).1
    have hle : pElementSubgroup 3 (gnA T T₁ Is) ≤ ⊥ := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨hxA, k, hk⟩
      rw [SetLike.mem_coe, Subgroup.mem_bot]
      by_contra hx1
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hx1 (orderOf_eq_one_iff.1 (by simpa using hk))
      have hxLs : x ∈ Is := (inf_le_right : gnA T T₁ Is ≤ Is) hxA
      have hd : orderOf x ∣ Nat.card Is := by
        rw [← Subgroup.orderOf_mk x hxLs]
        exact orderOf_dvd_natCard _
      rw [hk] at hd
      exact h3 ((dvd_pow_self 3 hk0).trans hd)
    exact hle.trans bot_le
  have h1 : 1 ≤ CFSG.Open.pRank 3 I := by
    refine one_le_pRank_of_dvd I Nat.prime_three ?_
    rw [← hI.2] at h3Is
    exact h3Is.trans (Subgroup.card_dvd_of_surjective ((toStar T).subgroupMap_surjective I))
  omega

theorem dvd_card_oddHull_of_dvd {Y : Type} [Group Y] [Finite Y] (P : Subgroup Y) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (h : q ∣ Nat.card P) : q ∣ Nat.card (oddHull P) := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := P) q h
  have hxq : orderOf (x : Y) = q := by rw [Subgroup.orderOf_coe, hx]
  have hmem : (x : Y) ∈ oddHull P :=
    Subgroup.subset_closure ⟨x.2, by rw [hxq]; exact hq.odd_of_ne_two hq2⟩
  have h1 : orderOf (⟨(x : Y), hmem⟩ : oddHull P) ∣ Nat.card (oddHull P) := orderOf_dvd_natCard _
  rwa [Subgroup.orderOf_mk (x : Y) hmem, hxq] at h1

theorem five_dvd_gnA_of_k5192 (hGen : KA10Gen) (hK5192 : K5192) {T T₁ T₂ : Subgroup X}
    (hX : GNSetting X T) (hg : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : GNYComponent T T₁ T₂ Ls)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (e : Nonempty (↥Ls ≃* alternatingGroup (Fin 10)))
    (h₁ : CFSG.Open.pRank 5 (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (hL5 : CFSG.Open.pRank 5 Ls = 2) :
    5 ∣ Nat.card (gnA T T₁ Ls) ∧ 5 ∣ Nat.card (gnA T T₂ Ls) := by
  obtain ⟨P₁, P₂, hP₁, hP₂, ⟨e₁⟩, h₂, hA1, hA2⟩ := hK5192 X T T₁ T₂ hX hg Ls hLs hinv e
  have h5 : Nat.Prime 5 := by norm_num
  have h8 : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  have h51 : 5 ∣ Nat.card (oddHull P₁) := by
    refine dvd_card_oddHull_of_dvd P₁ h5 (by norm_num) ?_
    rw [Nat.card_congr e₁.toEquiv, h8]
    norm_num
  have h52 : 5 ∣ Nat.card (oddHull P₂) := by
    refine dvd_card_oddHull_of_dvd P₂ h5 (by norm_num) ?_
    obtain ⟨-, -, ⟨e₂⟩⟩ := h₂
    have h1 : 5 ∣ Nat.card (↥P₂ ⧸ CFSG.pCore 2 ↥P₂) := by
      rw [Nat.card_congr e₂.toEquiv, h120]
      norm_num
    exact h1.trans (Subgroup.card_quotient_dvd_card _)
  have hA1' : 5 ∣ Nat.card (gnA T T₁ Ls) := h51.trans (Subgroup.card_dvd_of_le hA1)
  refine ⟨hA1', ?_⟩
  rcases hA2 with h2 | h2
  · exfalso
    have hsup : oddHull P₁ ⊔ oddHull P₂ = Ls := hGen _ Ls P₁ P₂ e hP₁ hP₂ ⟨e₁⟩ h₂
    have hLsle : Ls ≤ gnA T T₁ Ls := hsup.symm.le.trans (sup_le hA1 h2)
    have heq : gnA T T₁ Ls = Ls := le_antisymm inf_le_right hLsle
    have h3 : 1 < CFSG.Open.pRank 5 (gnA T T₁ Ls) := by rw [heq, hL5]; norm_num
    have := two_le_pRank_normalizer_of_gnA T T₁ Ls h5 (by norm_num) h3
    omega
  · exact h52.trans (Subgroup.card_dvd_of_le h2)

theorem xlevel_1516_gen (hAlt : LieOddRankAlt) (hKSMAlt : KSMAlt) (hGen : KA10Gen)
    (hK5192 : K5192) (hK518 : K518) {T T₁ T₂ : Subgroup X} (hX : GNSetting X T)
    (hg : GNGood T T₁ T₂)
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 3)
    (h5 : 3 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X))
    (h₁ : CFSG.Open.pRank 5 (Subgroup.normalizer (T₁ : Set X)) ≤ 1)
    (h₂ : CFSG.Open.pRank 5 (Subgroup.normalizer (T₂ : Set X)) ≤ 1)
    (hLifts : ∀ Is : Subgroup (X ⧸ gnC T), GNYComponent T T₁ T₂ Is → ∃ I, LiftOf T I Is)
    {Ls : Subgroup (X ⧸ gnC T)} {L : Subgroup X} (hLs : GNYComponent T T₁ T₂ Ls)
    (hL : LiftOf T L Ls) (e : Nonempty (↥Ls ≃* alternatingGroup (Fin 10))) : False := by
  have h5p : Nat.Prime 5 := by norm_num
  obtain ⟨hZ1, hrank⟩ := lift_alt_data hAlt hKSMAlt hX hLs.1 hL (n := 10) (by norm_num) e
  have hL3 : CFSG.Open.pRank 3 L = 3 := by rw [hrank 3 Nat.prime_three (by norm_num)]
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥(barO2 L)) := by
    rw [hZ1]; exact Nat.prime_three.not_dvd_one
  have hinv := gnImg_le_normalizer_of_normal
    (lift_normal_of_two_le_pRank hL Nat.prime_three (by norm_num) h3X (by omega) hZ).2
  have huniq : ∀ Is, GNYComponent T T₁ T₂ Is → Is = Ls := by
    intro Is hIs
    by_contra hne
    obtain ⟨I, hI⟩ := hLifts Is hIs
    exact false_of_two_components_pRank_three hg.three hLs hIs hL hI (Ne.symm hne) hZ
      h3X (by omega)
  have hL5 : CFSG.Open.pRank 5 Ls = 2 := by
    rw [pRank_eq_div_of_alt_s15 hAlt hLs.1 (n := 10) (by norm_num) e h5p (by norm_num)]
  obtain ⟨hd1, hd2⟩ := five_dvd_gnA_of_k5192 hGen hK5192 hX hg hLs hinv e h₁ hL5
  obtain ⟨m1, n1⟩ := mS_mN_eq_one_of_dvd h5p (by norm_num) h₁ Ls hd1
  obtain ⟨m2, n2⟩ := mS_mN_eq_one_of_dvd h5p (by norm_num) h₂ Ls hd2
  obtain ⟨hC, hY⟩ := hK518 X T T₁ T₂ hX hg 5 h5p (by norm_num) Ls L hLs hL hinv m1 m2 n1 n2
  have hle : pElementSubgroup 5 (⊤ : Subgroup X) ≤ Ls.comap (toStar T) :=
    hY fun Is hIs hne => absurd (huniq Is hIs) hne
  have h3 := pRank_le_pRank_of_le_comap_at h5p hC hle
  omega

end Row1516

theorem row1516_gen (hAlt : LieOddRankAlt) (hKSMAlt : KSMAlt) (hGen : KA10Gen) (hK5192 : K5192)
    (hK518 : K518) {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (h3X : CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) ≤ 3) (hLifts : RowLifts G M T T₁ T₂)
    (ctx : S15CtxGen G M T T₁ T₂) : Row1516 G M T T₁ T₂ := by
  intro Ls L hLs hL e h5
  exact xlevel_1516_gen hAlt hKSMAlt hGen hK5192 hK518 ctx.gn (S15CtxGen.good ctx) h3X
    (ctx.three_le 5 h5) (ctx.rank_N₁ 5 h5) (ctx.rank_N₂ 5 h5) hLifts hLs hL e

theorem row1516 (hAlt : LieOddRankAlt) (hKSMAlt : KSMAlt) (hGen : KA10Gen) (hK5192 : K5192)
    (hK518 : K518) {G : Type} [Group G] [Finite G] {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hLifts : RowLifts G M T T₁ T₂) (ctx : S15Ctx2 G M T T₁ T₂) : Row1516 G M T T₁ T₂ :=
  row1516_gen hAlt hKSMAlt hGen hK5192 hK518 (ctx.rank_odd 3 Nat.prime_three (by norm_num))
    hLifts (S15CtxGen.of_ctx2 ctx)

end CFSG.LocalAnalysis.RankThreeUC.S15
