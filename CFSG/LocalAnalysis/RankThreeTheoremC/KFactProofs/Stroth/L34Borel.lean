module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34KFacts
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3L34Proved
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.L34BorelSpec
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.L34ModelS
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallDefs
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.ComponentClassification.PSL3Four
open CFSG.RankThreeCoreUniqueness.Helpers

namespace KFactProofs.Stroth.L34Borel

variable {K : Type} [Group K] [Finite K]

theorem isLinThreeFour_of_isRankThreeL34 (hK : IsRankThreeL34 K) :
    CFSG.AGLEmbedding.IsLinThreeFour K := by
  obtain ⟨q, hq2, hqe, hv, he⟩ := hK
  exact ⟨⟨.A 2 q, hv⟩, ⟨q, hq2, hqe, rfl⟩, he⟩

theorem exists_conj_of_orderOf_eq_three (hK : IsRankThreeL34 K) {a b : K} (ha : orderOf a = 3)
    (hb : orderOf b = 3) : ∃ c : K, c * a * c⁻¹ = b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpa : IsPGroup 3 (zpowers a) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; rfl)
  have hpb : IsPGroup 3 (zpowers b) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb]; rfl)
  obtain ⟨Pa, hPa⟩ := hpa.exists_le_sylow
  obtain ⟨Pb, hPb⟩ := hpb.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K Pa Pb
  have hga : g * a * g⁻¹ ∈ (Pb : Subgroup K) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    have := Subgroup.smul_mem_pointwise_smul a (MulAut.conj g) (Pa : Subgroup K)
      (hPa (mem_zpowers a))
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have ha1 : g * a * g⁻¹ ≠ 1 := by
    intro h
    have : a = 1 := by
      calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
        _ = 1 := by rw [h]; group
    rw [this, orderOf_one] at ha
    omega
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    omega
  obtain ⟨n, -, hn⟩ := kFactL34SylowTransitive K hK Pb _ _ hga (hPb (mem_zpowers b)) ha1 hb1
  exact ⟨n * g, by rw [← hn]; group⟩

theorem card_eq (hK : IsRankThreeL34 K) : Nat.card K = 20160 := by
  obtain ⟨ε⟩ := CFSG.AGLEmbedding.KFactProofs.L34ModelS.nonempty_mulEquiv_S_of_isLinThreeFour
    (isLinThreeFour_of_isRankThreeL34 hK)
  rw [Nat.card_congr ε.toEquiv]
  exact card_S

end KFactProofs.Stroth.L34Borel

open KFactProofs.Stroth.L34Borel in
theorem kFactL34Borel :
    KFactL34Borel := by
  intro K _ _ hK u hu V hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ε⟩ := CFSG.AGLEmbedding.KFactProofs.L34ModelS.nonempty_mulEquiv_S_of_isLinThreeFour
    (isLinThreeFour_of_isRankThreeL34 hK)
  obtain ⟨u₀, T, hu₀S, hu₀1, hu₀3, hT, hcover, hnorm⟩ :=
    KFactProofs.Stroth.L34Borel.l34Borel_spec
  let ι : K →* Equiv.Perm (Fin 42) := S.subtype.comp ε.toMonoidHom
  have hι_inj : Function.Injective ι := Subtype.val_injective.comp ε.injective
  have hιS : ∀ k, ι k ∈ S := fun k => (ε k).2
  have hι_surj : ∀ x ∈ S, ∃ k, ι k = x := fun x hx => ⟨ε.symm ⟨x, hx⟩, by simp [ι]⟩
  obtain ⟨u', hu'⟩ := hι_surj u₀ hu₀S
  have hu'3 : orderOf u' = 3 := by
    have h1 : orderOf (ι u') = orderOf u' := orderOf_injective ι hι_inj u'
    rw [← h1, hu']
    exact orderOf_eq_prime hu₀3 hu₀1
  obtain ⟨c, hc⟩ := exists_conj_of_orderOf_eq_three hK hu hu'3
  let V' : Subgroup K := V.map (MulAut.conj c).toMonoidHom
  have hzp : (zpowers u).map (MulAut.conj c).toMonoidHom = zpowers u' := by
    rw [MonoidHom.map_zpowers]
    simp [hc]
  have hV' : rankTwoMaximalInvariantTwoSubgroup (zpowers u') V' := by
    have := rankTwoMaximalInvariantTwoSubgroup_map (zpowers u) V (MulAut.conj c) hV
    rwa [hzp] at this
  let TK : ℕ → Subgroup K := fun j => (T j).comap ι
  have hTKmap : ∀ j < 6, (TK j).map ι = T j := by
    intro j hj
    apply le_antisymm (Subgroup.map_comap_le _ _)
    intro x hx
    obtain ⟨k, rfl⟩ := hι_surj x ((hT j hj).1 hx)
    exact ⟨k, hx, rfl⟩
  have hTKcard : ∀ j < 6, Nat.card (TK j) = 64 := by
    intro j hj
    rw [← (hT j hj).2.1, ← hTKmap j hj, Subgroup.card_map_of_injective hι_inj]
  have hTKp : ∀ j < 6, IsPGroup 2 (TK j) := fun j hj =>
    IsPGroup.of_card (n := 6) (by rw [hTKcard j hj]; norm_num)
  have hTKu : ∀ j < 6, zpowers u' ≤ normalizer ((TK j : Subgroup K) : Set K) := by
    intro j hj
    rw [Subgroup.zpowers_le]
    rw [Subgroup.mem_normalizer_iff]
    intro k
    have hinv := (hT j hj).2.2
    constructor
    · intro hk
      show ι (u' * k * u'⁻¹) ∈ T j
      rw [map_mul, map_mul, map_inv, hu']
      exact hinv _ hk
    · intro hk
      have h1 : ι (u' * k * u'⁻¹) ∈ T j := hk
      rw [map_mul, map_mul, map_inv, hu'] at h1
      have h3 : u₀ ^ 3 = 1 := hu₀3
      show ι k ∈ T j
      have h2 := hinv _ (hinv _ h1)
      have hsq : u₀ * u₀ * u₀ = 1 := by rw [← pow_three']; exact h3
      have : ι k = u₀ * (u₀ * (u₀ * ι k * u₀⁻¹) * u₀⁻¹) * u₀⁻¹ := by
        have e : u₀ * u₀ * u₀ * ι k * (u₀ * u₀ * u₀)⁻¹ = ι k := by rw [hsq]; group
        calc ι k = u₀ * u₀ * u₀ * ι k * (u₀ * u₀ * u₀)⁻¹ := e.symm
          _ = u₀ * (u₀ * (u₀ * ι k * u₀⁻¹) * u₀⁻¹) * u₀⁻¹ := by group
      rw [this]
      exact h2
  have hV'eq : ∃ j < 6, V' = TK j := by
    by_cases hbot : V' = ⊥
    · refine ⟨0, by norm_num, ?_⟩
      have := hV'.2.2 (TK 0) (hTKp 0 (by norm_num)) (hTKu 0 (by norm_num)) (by rw [hbot]; exact bot_le)
      exact this.symm
    · have hW2 : IsPGroup 2 (V'.map ι) := hV'.1.map ι
      have hWne : V'.map ι ≠ ⊥ := by
        rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hι_inj]
      have hWS : V'.map ι ≤ S := by
        rintro _ ⟨k, -, rfl⟩
        exact hιS k
      have hWu : ∀ w ∈ V'.map ι, u₀ * w * u₀⁻¹ ∈ V'.map ι := by
        rintro _ ⟨k, hk, rfl⟩
        refine ⟨u' * k * u'⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hu']⟩
        have hn := hV'.2.1 (mem_zpowers u')
        exact (Subgroup.mem_normalizer_iff.1 hn k).1 hk
      obtain ⟨j, hj, hle⟩ := hcover _ hWS hW2 hWne hWu
      refine ⟨j, hj, ?_⟩
      have hle' : V' ≤ TK j := by
        intro k hk
        exact hle ⟨k, hk, rfl⟩
      exact (hV'.2.2 (TK j) (hTKp j hj) (hTKu j hj) hle').symm
  obtain ⟨j, hj, hVj⟩ := hV'eq
  have hVcard : Nat.card V = 64 := by
    have h1 : Nat.card V' = Nat.card V :=
      Subgroup.card_map_of_injective (MulAut.conj c).injective
    rw [← h1, hVj, hTKcard j hj]
  refine ⟨?_, ?_, ?_⟩
  ·
    refine isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top, card_eq hK, hVcard, Nat.factorization_def _ Nat.prime_two,
      show (20160 : ℕ) = 2 ^ 6 * 315 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
      padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
    norm_num
  ·
    obtain ⟨P, hP⟩ := (IsPGroup.of_card (n := 1) (p := 3) (G := zpowers u)
      (by rw [Nat.card_zpowers, hu]; rfl)).exists_le_sylow
    have hu1 : u ≠ 1 := by
      rintro rfl
      rw [orderOf_one] at hu
      omega
    have hC := kFactL34SylowCentralizer K hK P u (hP (mem_zpowers u)) hu1
    rw [hC]
    apply Subgroup.inf_eq_bot_of_coprime
    have hP9 : Nat.card (P : Subgroup K) = 9 := by
      rw [Sylow.card_eq_multiplicity, card_eq hK, Nat.factorization_def _ Nat.prime_three,
        show (20160 : ℕ) = 3 ^ 2 * 2240 by norm_num, padicValNat.mul (by norm_num) (by norm_num),
        padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd (by norm_num)]
      norm_num
    rw [hP9, hVcard]
    norm_num
  ·
    apply le_antisymm
    · exact sup_le hV.2.1 (Subgroup.le_normalizer)
    · intro n hn
      have hcn : c * n * c⁻¹ ∈ normalizer ((V' : Subgroup K) : Set K) := by
        rw [Subgroup.mem_normalizer_iff]
        intro k
        constructor
        · rintro ⟨v, hv, rfl⟩
          refine ⟨n * v * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn v).1 hv, ?_⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        · intro hk
          obtain ⟨v, hv, hvk⟩ := hk
          refine ⟨c⁻¹ * k * c, ?_, by simp [MulAut.conj_apply]; group⟩
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hvk
          have hv_eq : v = c⁻¹ * (c * n * c⁻¹ * k * (c * n * c⁻¹)⁻¹) * c := by
            rw [← hvk]
            group
          have : n * (c⁻¹ * k * c) * n⁻¹ = v := by
            rw [hv_eq]
            group
          have hv' : v ∈ V := hv
          rw [← this] at hv'
          exact (Subgroup.mem_normalizer_iff.1 hn _).2 hv'
      have hιN : ∀ t ∈ T j, ι (c * n * c⁻¹) * t * (ι (c * n * c⁻¹))⁻¹ ∈ T j := by
        intro t ht
        obtain ⟨k, rfl⟩ := hι_surj t ((hT j hj).1 ht)
        have hkV : k ∈ V' := by rw [hVj]; exact ht
        have := (Subgroup.mem_normalizer_iff.1 hcn k).1 hkV
        rw [hVj] at this
        have h2 : ι (c * n * c⁻¹ * k * (c * n * c⁻¹)⁻¹) ∈ T j := this
        rwa [map_mul, map_mul, map_inv] at h2
      have hmem := hnorm j hj _ (hιS _) hιN
      have hu'inv : ι u'⁻¹ = u₀⁻¹ := by rw [map_inv, hu']
      have key : c * n * c⁻¹ ∈ TK j ∨ u'⁻¹ * (c * n * c⁻¹) ∈ TK j ∨
          u'⁻¹ * (u'⁻¹ * (c * n * c⁻¹)) ∈ TK j := by
        rcases hmem with h | h | h
        · exact Or.inl h
        · right; left
          show ι (u'⁻¹ * (c * n * c⁻¹)) ∈ T j
          rwa [map_mul, hu'inv]
        · right; right
          show ι (u'⁻¹ * (u'⁻¹ * (c * n * c⁻¹))) ∈ T j
          rwa [map_mul, map_mul, hu'inv]
      rw [← hVj] at key
      have hback : ∀ x ∈ V', c⁻¹ * x * c ∈ V := by
        rintro _ ⟨v, hv, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rwa [show c⁻¹ * (c * v * c⁻¹) * c = v by group]
      have hcu : c⁻¹ * u' * c = u := by rw [← hc]; group
      have hcui : c⁻¹ * u'⁻¹ * c = u⁻¹ := by rw [← hc]; group
      rcases key with h | h | h
      · have := hback _ h
        rw [show c⁻¹ * (c * n * c⁻¹) * c = n by group] at this
        exact Subgroup.mem_sup_right this
      · have hv := hback _ h
        have e : c⁻¹ * (u'⁻¹ * (c * n * c⁻¹)) * c = u⁻¹ * n := by
          rw [← hcui]
          group
        rw [e] at hv
        have hn' : n = u * (u⁻¹ * n) := by group
        rw [hn']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (mem_zpowers u)) (Subgroup.mem_sup_right hv)
      · have := hback _ h
        have e : c⁻¹ * (u'⁻¹ * (u'⁻¹ * (c * n * c⁻¹))) * c = u⁻¹ * (u⁻¹ * n) := by
          rw [← hcui]
          group
        rw [e] at this
        have hn' : n = (u * u) * (u⁻¹ * (u⁻¹ * n)) := by group
        rw [hn']
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mul_mem _ (mem_zpowers u)
          (mem_zpowers u))) (Subgroup.mem_sup_right this)

end CFSG.LocalAnalysis.RankThreeTheoremC
