module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointStrong
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointEndgame
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma43Core
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma45Point
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointMaxPair
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma44
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointLemma42
import CFSG.LocalAnalysis.RankFourTheoremC.Equivalence
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.RelativePairGeometry

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2 CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem IsPPoint.false_three_of_case2 {P : Sylow 3 G} {M : Subgroup G} {x : G}
    (hin : PPointThreeInputs) (hS : D1Global G) (hD1 : D1For G) (hFC : FullCoreLocality G)
    (hInn : KFactInnerAction) (hWC : KFactWeakClosure) (hloc : D1Local 3 P M)
    (h : IsPPoint 3 P M x)
    (hcase2 : ∀ {n : ℕ} {f : GaloisField 3 n → G} {W : Subgroup G} (hB : BorelData3 P M x f W),
      ∀ m ∈ M, ∀ q ∈ hB.QK, m * q * m⁻¹ ∈ (P : Subgroup G) ⊔ GLBPrimeCore 3 M) : False := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  obtain ⟨n, f, W, hB⟩ := h.exists_borelData3 hin hS hD1 hFC hloc
  have hPab := h.isMulCommutative_sylow_three hin hS hD1 hFC hloc
  have hwc := h.weaklyClosed_three hin hS hD1 hFC hloc
  have hPM : (P : Subgroup G) ≤ M := sylow_le_of_core hloc
  have hPC : (P : Subgroup G) ≤ centralizer ({x} : Set G) :=
    h.le_centralizer_three hin hS hD1 hFC hloc
  have hxo : orderOf x = 3 := h.elem.2.1
  set O : Subgroup G := GLBPrimeCore 3 M with hO
  have hOM : M ≤ normalizer (O : Set G) := le_normalizer_glbPrimeCore 3 M
  have hOle : O ≤ M := glbPrimeCore_le 3 M
  have hOcop : Nat.Coprime 3 (Nat.card O) := glbPrimeCore_coprime 3 M
  have hO3 : ¬ 3 ∣ Nat.card O := (Nat.Prime.coprime_iff_not_dvd hp).mp hOcop
  have hO2 : 2 ∣ Nat.card O := by
    obtain ⟨V, hV1, hV2, hVM⟩ := hloc.maxLocal.1
    have hVO : V ≤ O := by
      refine le_glbPrimeCore (hVM ▸ Subgroup.le_normalizer) (hVM ▸ le_rfl) ?_
      obtain ⟨b, hb⟩ := hV2.exists_card_eq
      rw [hb]
      exact Nat.Coprime.pow_right _ (by norm_num)
    obtain ⟨b, hb⟩ := hV2.exists_card_eq
    have hb1 : b ≠ 0 := by
      rintro rfl
      exact hV1 (Subgroup.card_eq_one.mp (by simpa using hb))
    have : 2 ∣ Nat.card V := hb ▸ dvd_pow_self 2 hb1
    exact this.trans (Subgroup.card_dvd_of_le hVO)
  have hRM : M ≤ normalizer ((hB.QK ⊔ O : Subgroup G) : Set G) :=
    hB.le_normalizer_QK_sup hPab hwc hPM hOM (hcase2 hB)
  have hQM : hB.QK ≤ M := hB.QK_le_P.trans hPM
  have hf1P : f 1 ∈ (P : Subgroup G) := (hB.le (hB.f_mem_W 1)).1
  have hf1x : f 1 ∉ zpowers x := hB.f_not_mem_zpowers one_ne_zero
  have hf1M : centralizer ({f 1} : Set G) ≤ M :=
    h.centralizer_le_of_not_mem_zpowers hin hS hD1 hFC hloc hf1P (hB.f_pow_three 1) hf1x
  have hCM : centralizer (hB.QK : Set G) ≤ M :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (hB.f_mem_QK 1))).trans hf1M
  have hxM : x ∈ M := hPM hB.x_mem
  have hD1' : ∀ H : Subgroup G, IsTwoLocal H → 3 ≤ CFSG.Open.pRank 3 (H ⊓ M) → H ≤ M :=
    fun H hH hr => hD1 3 hloc.beta P M hloc.maxLocal hloc.core H hH hr
  set U : Subgroup G := BorelData3.plane x f 1 with hU
  have hUel : IsElemAbelian 3 U := hB.plane_isElemAbelian 1
  have hUcard : Nat.card U = 3 ^ 2 := hB.plane_card one_ne_zero
  have hUP : U ≤ (P : Subgroup G) := (hB.plane_le 1).trans (hB.le.trans inf_le_left)
  have hUM : U ≤ M := hUP.trans hPM
  have hxU : x ∈ U := BorelData3.x_mem_plane x f 1
  have hx1 : x ≠ 1 := hB.x_ne_one
  have hUp : IsPGroup 3 U := elementary_isPGroup 3 U hUel
  have hCU : centralizer (U : Set G) ≤ M := by
    refine (Subgroup.centralizer_le ?_).trans hf1M
    rw [Set.singleton_subset_iff]
    exact BorelData3.f_mem_plane x f 1
  have hC : ∀ u ∈ U, u ∉ zpowers x → centralizer ({u} : Set G) ≤ M := fun u hu hux =>
    h.centralizer_le_of_not_mem_zpowers hin hS hD1 hFC hloc (hUP hu) (hUel.2 u hu) hux
  have hL43 : ∀ Y : Subgroup G, IsPGroup 2 Y → Y ≤ M → U ≤ normalizer (Y : Set G) →
      IsSylowOf 2 (Y ⊓ O) O → normalizer (Y : Set G) ≤ M := fun Y hY2 hYM hUY hYO =>
    hB.normalizer_le_of_normal hwc hO3 hO2 hOM hOle hQM hRM hCM hxM hD1' one_ne_zero hY2 hYM hUY hYO
  obtain ⟨S₁, hS₁, hS₁M⟩ := hB.exists_rankTwoMaximal_not_le (t₀ := 1) one_ne_zero
  obtain ⟨S₁, T, hS₁, hS₁M, hT, hTM, hTloc, hint, hne, hmax⟩ := exists_maximal_escaping_pair
    hS.charTwo hp (by norm_num) hUel hUcard hUM hxU hOle hOM hOcop hC hL43 ⟨S₁, hS₁, hS₁M⟩
  have hSO := isSylowOf_two_glbPrimeCore_of_maximal hp (by norm_num) hUp hCU hS₁ hS₁M hT hTM
    hint hmax
  obtain ⟨R₀, hR₀N, hR₀T, hR₀2, hR₀S, hUR₀, hR₀notS, hR₀notO⟩ := exists_R₀_of_maximal hp
    (by norm_num) hUp hUM hOle hOM hOcop hL43 hS₁ hS₁M hTloc hint hSO
  have hS2 : IsPGroup 2 (S₁ ⊓ T : Subgroup G) := hS₁.1.to_inf_left
  have hUS : U ≤ normalizer ((S₁ ⊓ T : Subgroup G) : Set G) :=
    common_normalizer_le_normalizer_inf U S₁ T hS₁.2.1 hT.2.1
  have hesc : ¬ normalizer ((S₁ ⊓ T : Subgroup G) : Set G) ≤ M :=
    relative_pair_intersection_normalizer_escapes M S₁ T hS₁.1 hS₁M hTM hint
  have hend := endgame_exists_centralizer_ne_bot hS hD1 hFC hInn hWC hloc hPab hUel hUcard hUP
    hxU hx1 hwc hC hS2 hne hUS hesc hR₀N hR₀S hUR₀ hR₀notO
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hend
  have hcO : (c : G) ∈ O ⊓ centralizer ({x} : Set G) := ⟨hR₀N c.2.1, c.2.2⟩
  obtain ⟨k, hk⟩ := hR₀2 ⟨(c : G), c.2.1⟩
  have hck : (c : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf (c : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hck
  obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hc1
    exact Subtype.ext (orderOf_eq_one_iff.mp (by simpa using hci))
  have h2 : 2 ∣ orderOf (c : G) := hci ▸ dvd_pow_self 2 hi0
  have h3 : orderOf (c : G) ∣ Nat.card (O ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    have := orderOf_dvd_natCard (⟨(c : G), hcO⟩ : (O ⊓ centralizer ({x} : Set G) : Subgroup G))
    rwa [Subgroup.orderOf_mk] at this
  exact h.not_two_dvd_card_inf_primeCore_three hin hS hD1 hFC hloc (h2.trans h3)

end CFSG.LocalAnalysis.RankFourTheoremC
