module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SplitExc
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Model
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSz32Group
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.GLBCoreNormalizer

public section

namespace CFSG.AGLEmbedding

namespace KFactProofs.Sz32Local

open CFSG.Blueprint CFSG.RankThree.PartOne.K159.SzAbs CFSG.AGLEmbedding.KFactProofs.Sz32

theorem exists_conj_of_card_twentyfive {P : Type*} [Group P] [Finite P]
    (hP : Nat.card P = 32537600) {E E' : Subgroup P} (hE : Nat.card E = 25)
    (hE' : Nat.card E' = 25) : ∃ g : P, ∀ y, y ∈ E ↔ g * y * g⁻¹ ∈ E' := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5 : 5 ^ (Nat.card P).factorization 5 = 25 := by
    rw [hP, factorization_five]
    norm_num
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq P (Sylow.ofCard E (h5.symm ▸ hE))
    (Sylow.ofCard E' (h5.symm ▸ hE'))
  have h := congrArg (fun Q : Sylow 5 P => (Q : Subgroup P)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard] at h
  have hmap : E.map (MulAut.conj g).toMonoidHom = E' := by
    rw [← h]
    ext x
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  refine ⟨g, fun y => ?_⟩
  rw [← hmap]
  exact (Subgroup.mem_map_iff_mem (MulAut.conj g).injective).symm

noncomputable def modelEquiv {F : Type} [Field F] (σ : F ≃+* F32) :
    suzukiGroup 2 F ≃* suzukiGroup 2 F32 :=
  ((MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 2 F)).trans
    (CFSG.ShultStronglyClosedTI.glaSzFieldEquiv σ 2)).trans
    (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup 2 F32).symm)

theorem centralizer_le_of_equiv
    {K : Type} [Group K] [Finite K] (ε : K ≃* suzukiGroup 2 F32) (T : Sylow 5 K) :
    ∀ t ∈ (T : Subgroup K), t ≠ 1 → ∀ g : K, g * t = t * g → g ∈ (T : Subgroup K) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hG : Nat.card (suzukiGroup 2 F32) = 32537600 := by
    rw [CFSG.LieType.Ree.suzuki_order F32.natCard_eq]
    norm_num
  have hKcard : Nat.card K = 32537600 := (Nat.card_congr ε.toEquiv).trans hG
  have hTcard : Nat.card (T : Subgroup K) = 25 := by
    rw [Sylow.card_eq_multiplicity, hKcard, factorization_five]
    norm_num
  have hT' : Nat.card ((T : Subgroup K).map ε.toMonoidHom) = 25 := by
    rw [Subgroup.card_map_of_injective ε.injective, hTcard]
  have hT0 : Nat.card (Subgroup.zpowers g0) = 25 := by
    rw [Nat.card_zpowers, orderOf_g0]
  have : Finite (suzukiGroup 2 F32) := Nat.finite_of_card_ne_zero (by rw [hG]; norm_num)
  obtain ⟨x, hx⟩ := exists_conj_of_card_twentyfive hG hT' hT0
  have hmem : ∀ k : K, k ∈ (T : Subgroup K) ↔ x * ε k * x⁻¹ ∈ Subgroup.zpowers g0 := by
    intro k
    rw [← hx]
    exact (Subgroup.mem_map_iff_mem ε.injective).symm
  intro t ht ht1 g hg
  have h1 : x * ε t * x⁻¹ ∈ Subgroup.zpowers g0 := (hmem t).1 ht
  have h2 : x * ε t * x⁻¹ ≠ 1 := by
    intro h
    apply ht1
    apply ε.injective
    have : ε t = 1 := by
      have := congrArg (fun z => x⁻¹ * z * x) h
      simpa [mul_assoc] using this
    rw [this, map_one]
  have h3 : (x * ε g * x⁻¹) * (x * ε t * x⁻¹) = (x * ε t * x⁻¹) * (x * ε g * x⁻¹) := by
    calc (x * ε g * x⁻¹) * (x * ε t * x⁻¹) = x * ε (g * t) * x⁻¹ := by
          rw [map_mul]; group
      _ = x * ε (t * g) * x⁻¹ := by rw [hg]
      _ = (x * ε t * x⁻¹) * (x * ε g * x⁻¹) := by rw [map_mul]; group
  exact (hmem g).2 (sz32_centralizer_le h1 h2 h3)

end KFactProofs.Sz32Local

open CFSG.Open CFSG.Blueprint KFactProofs.Sz32Local KFactProofs.Sz32

theorem kFactCaseTwoLocalSz32 :
    KFactCaseTwoLocalSz32 := by
  rintro p K _ _ ⟨rfl, d, hd, he⟩
  obtain ⟨x, hv⟩ := d
  simp only at hd
  subst hd
  have hiso : CFSG.RankThree.PartOne.Census3.IsoLie K (.suzuki 2) := ⟨hv, he⟩
  have hSz := CFSG.RankThree.PartOne.K159.SzAbs.szSylow_of_isoLie hiso
  have hmodel := CFSG.RankThree.PartOne.CTP.suzukiModel_of_isoLie 2 hiso
  have hOut : (CFSG.ComponentClassification.OuterAutomorphisms.inner K).index ∣ 5 :=
    CFSG.RankThree.PartOne.K159F.card_outer_dvd_five hiso
  obtain ⟨-, a, ha, F, _, _, hfa, hF, ⟨eF⟩⟩ := hmodel
  have hF' : Nat.card F = 2 ^ (2 * a + 1) := by rw [← hfa]; exact hF
  have hsimple : IsSimpleGroup K := by
    have := (CFSG.LieType.Ree.suzuki_simple ha hF').2.2
    exact eF.isSimpleGroup
  obtain rfl : a = 2 := by omega
  let σ : F ≃+* F32 := F32.ringEquiv F hF'
  let ε : K ≃* suzukiGroup 2 F32 := eF.trans (modelEquiv σ)
  have hcard : ∀ T : Sylow 5 K, Nat.card (T : Subgroup K) = 25 := by
    intro T
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [Sylow.card_eq_multiplicity, hSz.card,
      CFSG.RankThree.PartOne.K159.SzAbs.factorization_five]
    norm_num
  have hdata : ∀ T : Sylow 5 K, Sz32Data K (T : Subgroup K) := fun T =>
    ⟨hSz.card, hcard T, hSz.cyclic T, centralizer_le_of_equiv ε T⟩
  have hΓ : ∀ T : Sylow 5 K,
      GLBCore 5 1 (T : Subgroup K) = Subgroup.normalizer ((T : Subgroup K) : Set K) := fun T =>
    KFactProofs.GLBCoreNormalizer.glbCore_eq_normalizer Nat.prime_five
      (by rw [hcard T]; norm_num) (hdata T).commute (hdata T).centralizer_le
  refine ⟨?_, fun t ht => Sz32Data.isPGroup_stabilizer hdata hOut ht, fun T => ?_⟩
  · intro T _
    rw [hΓ T]
    exact ⟨fun Y hY => (hdata T).maximal hY,
      fun N hNle hNn hcop => (hdata T).eq_bot_of_normal hNle hNn hcop,
      fun f hf => (hdata T).eq_one_of_fixes_normalizer hSz hsimple hOut hf⟩
  · refine ⟨(hdata T).exists_fixed_point_free, fun f hf => (hdata T).aut hSz hsimple hOut hf, ?_⟩
    rw [hΓ T]
    exact (hdata T).isSolvable_normalizer

end CFSG.AGLEmbedding
