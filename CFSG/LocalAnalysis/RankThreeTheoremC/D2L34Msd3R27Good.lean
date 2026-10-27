module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34Only
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34Three

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.RankThreeCoreUniqueness.Helpers CFSG.AGLEmbeddingD2
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G]

private theorem normalizer_map_le_of_core_one {M H E : Subgroup G}
    (hWM : GLBPrimeCore 3 H ≤ M) (hEH : E ≤ H) (hE : IsElemAbelian 3 E)
    (hEcore : GLBCore 3 1 E ≤ M) {Y : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hYE : Y ≤ (E.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)))
    (hY1 : Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set (H ⧸ primeComplementCore (G := H) 3)) ≤
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  have hO : (3 : ℕ).Coprime (Nat.card (primeComplementCore (G := H) 3)) :=
    primeComplementCore_coprime 3
  have hOM : primeComplementCore (G := H) 3 ≤ (H ⊓ M).subgroupOf H := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf hWM
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hEp' : IsPGroup 3 (E.subgroupOf H) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  set Y₁ := Y.comap π ⊓ E.subgroupOf H
  have hmap : Y₁.map π = Y := map_comap_inf_eq _ hYE
  have hEH' : (E.subgroupOf H).map H.subtype = E := Subgroup.map_subgroupOf_eq_of_le hEH
  have hY₁E : Y₁.map H.subtype ≤ E := (Subgroup.map_mono inf_le_right).trans hEH'.le
  have hY₁ne : Y₁.map H.subtype ≠ ⊥ := by
    intro hbot
    apply hY1
    rw [← hmap, (Subgroup.map_eq_bot_iff_of_injective Y₁ H.subtype_injective).mp hbot,
      Subgroup.map_bot]
  rw [← hmap]
  exact normalizer_map_mk_le_map_inf Nat.prime_three _ hO hOM (hEp'.to_le inf_le_right)
    ((CFSG.AGLEmbeddingD2.normalizer_le_glbCore 3 1 hY₁E
      (one_le_pRank_of_isElemAbelian Nat.prime_three (isElemAbelian_of_le hE hY₁E) hY₁ne)).trans
      hEcore)

private theorem ne_bot_of_one_le_pRank' {X : Type*} [Group X] [Finite X] {Q : Subgroup X}
    (h : 1 ≤ CFSG.Open.pRank 3 Q) : Q ≠ ⊥ := by
  intro hQ
  obtain ⟨F, hF, -, hFcard⟩ := pRank_attained 3 Nat.prime_three Q
  rw [hQ, le_bot_iff] at hF
  rw [hF, Subgroup.card_bot] at hFcard
  have := Nat.one_lt_pow (by omega : CFSG.Open.pRank 3 Q ≠ 0) Nat.prime_three.one_lt
  omega

theorem D2L34BetaConf3.map_eq_of_good
    {d : TauCeti.ValidLieTypeIndex} {P : Sylow 3 G} {M A H R : Subgroup G}
    {Rbar : Sylow 3 (H ⧸ primeComplementCore (G := H) 3)}
    {K : Subgroup (H ⧸ primeComplementCore (G := H) 3)}
    (hc : D2L34BetaConf3 d P M A H R Rbar K) {E : Subgroup G} (hEHM : E ≤ H ⊓ M)
    (hE : IsElemAbelian 3 E) (hE9 : Nat.card E = 9) (hEcore : GLBCore 3 1 E ≤ M) :
    (E.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) =
      (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 3)
  have hEH : E ≤ H := hEHM.trans inf_le_left
  have hEp : IsPGroup 3 E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  have hEp' : IsPGroup 3 (E.subgroupOf H) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hEH).symm
  have hEbar9 : Nat.card ((E.subgroupOf H).map π) = 9 := by
    rw [card_map_mk_of_isPGroup Nat.prime_three _ (primeComplementCore_coprime 3) hEp',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hE9]
  have hEbarel : IsElemAbelian 3 ((E.subgroupOf H).map π) :=
    elementary_abelian_map 3 (isElemAbelian_subgroupOf hE H) π
  have hEK : (E.subgroupOf H).map π ≤ K := by
    by_contra hEK
    have htop := kFactL34Outer d hc.l34 _ K hc.almostSimple.normal
      hc.almostSimple.centralizer_eq_bot hc.iso _ hEbarel (by rw [hEbar9]; norm_num) hEK
    apply hc.almostSimple.ne_top
    rw [eq_top_iff, ← htop]
    exact (fullCore_le_iff 3 1 _ _).mpr fun Q hQE hrank =>
      normalizer_map_le_of_core_one hc.esc.primeCore_le hEH hE hEcore hQE
        (ne_bot_of_one_le_pRank' hrank)
  have hX₀N : ((H ⊓ M).subgroupOf H).map π =
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) :=
    hc.almostSimple.eq_normalizer_of_l34 kFactL34Inner hc.l34 hc.iso hc.le_K
  have hEN : (E.subgroupOf H).map π ≤
      Subgroup.normalizer (((A.subgroupOf H).map π : Subgroup _) : Set _) := by
    rw [← hX₀N]
    exact Subgroup.map_mono fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hEHM (Subgroup.mem_subgroupOf.mp hx))
  have hAbar9 : Nat.card ((A.subgroupOf H).map π) = 9 := by
    rw [hc.almostSimple.card_A]
    norm_num
  have hEbarp : IsPGroup 3 ((E.subgroupOf H).map π) :=
    IsPGroup.of_card (n := 2) (by rw [hEbar9]; norm_num)
  have hAbarp : IsPGroup 3 ((A.subgroupOf H).map π) :=
    IsPGroup.of_card (n := 2) (by rw [hAbar9]; norm_num)
  have hsupp := IsPGroup.to_sup_of_normal_right' hEbarp hAbarp hEN
  have hK20 : Nat.card K = 20160 :=
    card_of_isLinThreeFour (isLinThreeFour_of_l34Index hc.l34 hc.iso)
  obtain ⟨k, hk⟩ := hsupp.exists_card_eq
  have hdvd : 3 ^ k ∣ 20160 := by
    rw [← hk, ← hK20]
    exact Subgroup.card_dvd_of_le (sup_le hEK hc.le_K)
  have hk2 : k ≤ 2 := by
    by_contra hk3
    have h27 : 3 ^ 3 ∣ 20160 := (Nat.pow_dvd_pow 3 (by omega)).trans hdvd
    norm_num at h27
  have hsup9 : Nat.card ((E.subgroupOf H).map π ⊔ (A.subgroupOf H).map π : Subgroup _) ≤ 9 := by
    rw [hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 9 := by norm_num
  have h1 : (E.subgroupOf H).map π = (E.subgroupOf H).map π ⊔ (A.subgroupOf H).map π :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hEbar9]; exact hsup9)
  have h2 : (A.subgroupOf H).map π = (E.subgroupOf H).map π ⊔ (A.subgroupOf H).map π :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hAbar9]; exact hsup9)
  rw [h1, ← h2]

end CFSG.LocalAnalysis.RankThreeTheoremC
