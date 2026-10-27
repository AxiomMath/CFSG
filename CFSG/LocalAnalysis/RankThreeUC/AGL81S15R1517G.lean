module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15R1517Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.OraclesAt
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section15.Ctx

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding CFSG.Open Subgroup
open CFSG.LocalAnalysis.AGL81TheoremCD.Section15

section GLevel

variable {G : Type} [Group G] [Finite G]

theorem pRank_normalizer_le_one_aux_ne_bot {Q : Subgroup G} (h : 1 ≤ CFSG.Open.pRank 3 Q) :
    Q ≠ ⊥ := by
  rintro rfl
  have h0 : CFSG.Open.pRank 3 (⊥ : Subgroup G) ≤ 0 :=
    CFSG.SectionRank.pRank_le (by norm_num) (fun E hE _ => by
      rw [le_bot_iff.mp hE]
      simp)
  omega

theorem pRank_normalizer_le_one_aux_order9 {X : Type} [Group X] [Finite X] {Q : Subgroup X}
    (hQ : 2 ≤ CFSG.Open.pRank 3 Q) : ∃ E ≤ Q, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Q
  have hdvd : 3 ^ 2 ∣ Nat.card E := hcard ▸ pow_dvd_pow 3 hQ
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 hdvd
  have hle : K.map E.subtype ≤ E := Subgroup.map_subtype_le K
  refine ⟨K.map E.subtype, hle.trans hEQ, CFSG.Open.IsElemAbelian.mono hE hle, ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hK]
  norm_num

theorem pRank_normalizer_le_one_aux_gamma {M E : Subgroup G}
    (hstrong3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M) (hEM : E ≤ M)
    (hE : IsElemAbelian 3 E) : rankThreeGamma 1 3 E ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine sSup_le ?_
  rintro N ⟨Q, hQE, hQ1, rfl⟩
  exact hstrong3.normalizer_le (pRank_normalizer_le_one_aux_ne_bot hQ1)
    (hE.mono hQE).isPGroup (hQE.trans hEM)

theorem pRank_normalizer_le_one_aux_maxTwoLocal {L : Subgroup G} (hL : IsTwoLocal L) :
    ∃ H : Subgroup G, rankThreeIsMaxTwoLocal H ∧ L ≤ H := by
  classical
  obtain ⟨M, ⟨hM, hLM⟩, hmax⟩ := Set.exists_max_image {K : Subgroup G | IsTwoLocal K ∧ L ≤ K}
    (fun K => Nat.card K) (Set.toFinite _) ⟨L, hL, le_rfl⟩
  refine ⟨M, ⟨hM, fun H hH hMH => ?_⟩, hLM⟩
  exact (Subgroup.eq_of_le_of_card_ge hMH (hmax H ⟨hH, hLM.trans hMH⟩)).symm

theorem pRank_normalizer_le_one_aux_char {S K : Subgroup G} (hKS : K ≤ S)
    (hchar : (K.subgroupOf S).Characteristic) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  let φ := S.normalizerMonoidHom ⟨g, hg⟩
  have hfixed := Subgroup.characteristic_iff_map_eq.mp hchar φ
  intro x
  constructor
  · intro hx
    have hxS : x ∈ S := hKS hx
    have hxK : (⟨x, hxS⟩ : S) ∈ K.subgroupOf S := hx
    have himage : φ ⟨x, hxS⟩ ∈ (K.subgroupOf S).map φ.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨⟨x, hxS⟩, hxK, rfl⟩
    rw [hfixed] at himage
    change ((φ ⟨x, hxS⟩ : S) : G) ∈ K at himage
    exact himage
  · intro hx
    have hxS : x ∈ S := (hg x).mpr (hKS hx)
    have hxK : φ ⟨x, hxS⟩ ∈ K.subgroupOf S := hx
    rw [← hfixed] at hxK
    obtain ⟨y, hy, heq⟩ := Subgroup.mem_map.mp hxK
    have hyx : y = ⟨x, hxS⟩ := φ.injective heq
    simpa only [hyx, Subgroup.mem_subgroupOf, SetLike.mem_coe] using hy

theorem pRank_normalizer_le_one_aux_setup_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂) {Ti : Subgroup ↥M} (hne : Ti ≠ ⊥) (hle : Ti ≤ T.subgroupOf M)
    (hchar : (Ti.subgroupOf (T.subgroupOf M)).Characteristic)
    (h2 : 2 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (Ti : Set ↥M))) :
    ∃ E H : Subgroup G, E ≤ M ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      rankThreeIsMaxTwoLocal H ∧ E ≤ H ∧ H ≠ M ∧
      (Subgroup.normalizer (Ti : Set ↥M)).map M.subtype ≤ H := by
  have hTM : T ≤ M := ctx.sylow.le
  obtain ⟨hCT, hCchar⟩ := map_subtype_characteristic hTM hle hchar
  have hne' : Ti.map M.subtype ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective Ti M.subtype_injective).mp h)
  have hloc : IsTwoLocal (Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G)) :=
    ⟨Ti.map M.subtype, hne', ctx.sylow.isPGroup.to_le hCT, rfl⟩
  obtain ⟨H, hH, hNH⟩ := pRank_normalizer_le_one_aux_maxTwoLocal hloc
  have hTN := pRank_normalizer_le_one_aux_char hCT hCchar
  have hmap : (Subgroup.normalizer (Ti : Set ↥M)).map M.subtype ≤
      Subgroup.normalizer ((Ti.map M.subtype : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_map (H := Ti) M.subtype
  obtain ⟨E₀, hE₀N, hE₀, hE₀9⟩ := pRank_normalizer_le_one_aux_order9 h2
  refine ⟨E₀.map M.subtype, H, Subgroup.map_subtype_le E₀, hE₀.map M.subtype, ?_, hH,
    (Subgroup.map_mono hE₀N).trans (hmap.trans hNH), fun hHM => ctx.notLe (hTN.trans (hNH.trans
      hHM.le)), hmap.trans hNH⟩
  rw [Subgroup.card_map_of_injective M.subtype_injective, hE₀9]

theorem eq_of_maxTwoLocal_of_nonTrans_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO : O1521At G M) (h11 : Row1511 G M T T₁ T₂)
    (hstrong3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M)
    (hnt : ∀ E : Subgroup ↥M, IsElemAbelian 3 E → Nat.card E = 9 → NonTrans1517 E)
    {E : Subgroup G} (hE : E ≤ M) (hEab : IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    {H : Subgroup G} (hH : rankThreeIsMaxTwoLocal H) (hEH : E ≤ H) : H = M := by
  by_contra hne
  obtain ⟨A, T', R, H', hcfg⟩ := hO h11 E hE hEab hE9
    (pRank_normalizer_le_one_aux_gamma hstrong3 hE hEab) H hH hEH hne
  have hAM : A ≤ M := hcfg.le_M
  have hA9 : Nat.card (A.subgroupOf M) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv, hcfg.card_eq]
  obtain ⟨a, ha, b, hb, ha1, hb1, hnorm⟩ :=
    hnt (A.subgroupOf M) (hcfg.elemAbelian.subgroupOf M) hA9
  obtain ⟨t, ht, hta⟩ := hcfg.transitive (a : G) ha (fun h => ha1 (Subtype.ext h)) (b : G) hb
    (fun h => hb1 (Subtype.ext h))
  obtain ⟨htT, htN⟩ := Subgroup.mem_inf.mp ht
  have htM : t ∈ M := hcfg.sylow.le htT
  refine hnorm ⟨t, htM⟩ ?_ (Subtype.ext hta)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact Subgroup.mem_normalizer_iff.mp htN (x : G)

theorem pRank_normalizer_le_one_of_O1521b_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (hO : O1521bAt G M) (ctx : S15CtxGen G M T T₁ T₂) (h11 : Row1511 G M T T₁ T₂)
    (hstrong3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 M) {p : ℕ} (hp : p ∈ sigmaM G M)
    {Ti : Subgroup ↥M} (hne : Ti ≠ ⊥) (hle : Ti ≤ T.subgroupOf M)
    (hchar : (Ti.subgroupOf (T.subgroupOf M)).Characteristic)
    (hdvd : p ∣ Nat.card (Subgroup.normalizer (Ti : Set ↥M))) :
    CFSG.Open.pRank 3 (Subgroup.normalizer (Ti : Set ↥M)) ≤ 1 := by
  by_contra hcon
  obtain ⟨E, H, hEM, hEab, hE9, hH, hEH, hHM, hNH⟩ :=
    pRank_normalizer_le_one_aux_setup_gen ctx hne hle hchar (by omega)
  apply hO h11 E hEM hEab hE9 (pRank_normalizer_le_one_aux_gamma hstrong3 hEM hEab) H hH hEH hHM
    p hp
  have hcard : Nat.card ((Subgroup.normalizer (Ti : Set ↥M)).map M.subtype) =
      Nat.card (Subgroup.normalizer (Ti : Set ↥M)) :=
    Subgroup.card_map_of_injective M.subtype_injective
  rw [← hcard] at hdvd
  exact hdvd.trans (Subgroup.card_dvd_of_le (le_inf hNH (Subgroup.map_subtype_le _)))

theorem pRank_normalizer_le_one_of_unique_gen {M T : Subgroup G} {T₁ T₂ : Subgroup ↥M}
    (ctx : S15CtxGen G M T T₁ T₂)
    (hno : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 3 E → Nat.card E = 9 →
      ∀ H : Subgroup G, rankThreeIsMaxTwoLocal H → E ≤ H → H = M)
    {Ti : Subgroup ↥M} (hne : Ti ≠ ⊥) (hle : Ti ≤ T.subgroupOf M)
    (hchar : (Ti.subgroupOf (T.subgroupOf M)).Characteristic) :
    CFSG.Open.pRank 3 (Subgroup.normalizer (Ti : Set ↥M)) ≤ 1 := by
  by_contra hcon
  obtain ⟨E, H, hEM, hEab, hE9, hH, hEH, hHM, -⟩ :=
    pRank_normalizer_le_one_aux_setup_gen ctx hne hle hchar (by omega)
  exact hHM (hno E hEM hEab hE9 H hH hEH)

end GLevel

end CFSG.LocalAnalysis.RankThreeUC.S15
