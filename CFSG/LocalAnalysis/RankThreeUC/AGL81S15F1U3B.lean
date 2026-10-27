module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15F1U3Glue
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3Dickson
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddGood
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddPSLCard

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace F1Proof

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.BenderSuzuki.MatrixGroups CFSG.ABGLocalTools
  CFSG.AGLEmbeddingD2.McLaughlin.OddIndex CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

section Good

theorem relIndex_centralizer_odd (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq3 : (p ^ f) % 3 = 1) (hq4 : (p ^ f) % 4 = 3)
    (hD : ∀ A H : Subgroup (PSL2MatrixGroup (fixedSubfield F p f)), Nat.card A = 3 →
      Nat.card (fixedSubfield F p f) - 1 ∣
        Nat.card (Subgroup.normalizer (A : Set (PSL2MatrixGroup (fixedSubfield F p f)))) →
      Subgroup.normalizer (A : Set _) ≤ H → H = Subgroup.normalizer (A : Set _) ∨ ¬ 2 ∣ H.index)
    {ω : Fˣ} (hω : orderOf ω = 3) {W : Subgroup (SU (unitaryInvolution F p f) 3)}
    (hNW : normA0 hF ω ≤ W)
    (hgood : ∃ x ∈ W, x * zSU hF = zSU hF * x ∧ x ∉ normA0 hF ω) :
    ¬ 2 ∣ (W ⊓ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))).relIndex
      (Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))) := by
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  have hTN := range_tSU_le_normA0 hF hω hq3
  have hTW : (tSU hF).range ≤ W := hTN.trans hNW
  obtain ⟨x, hxW, hxz, hxN⟩ := hgood
  obtain ⟨l, hl, t, ht, rfl⟩ := (mem_centralizer_zSU_iff hF hp2 x).1 hxz
  have hlW : l ∈ W := by
    have : l = (l * t) * t⁻¹ := by group
    rw [this]
    exact W.mul_mem hxW (W.inv_mem (hTW ht))
  have hlN : l ∉ normA0 hF ω := fun h => hxN ((normA0 hF ω).mul_mem h (hTN ht))
  rw [← range_levi hζ0 hζ] at hl
  obtain ⟨w, rfl⟩ := hl
  have hA := card_zpowers_pslMk_diagSL hζ0 hζ hF hω hq3
  have hAH := (normalizer_psl_le_map_comap hζ0 hζ hF hω hq3).trans
    (Subgroup.map_mono (Subgroup.comap_mono hNW))
  have hF0 : Nat.card (fixedSubfield F p f) = p ^ f := card_fixedSubfield hF
  have hN : Nat.card (fixedSubfield F p f) - 1 ∣ Nat.card (Subgroup.normalizer
      ((Subgroup.zpowers (pslMk (fixedSubfield F p f)
        (diagSL (pow_eq_self_of_orderOf_three hω hq3))) : Subgroup
          (PSL2MatrixGroup (fixedSubfield F p f))) : Set (PSL2MatrixGroup (fixedSubfield F p f)))) := by
    rw [card_normalizer_psl hζ0 hζ hF hω hq3 hp2, hF0]
  rcases hD _ _ hA hN hAH with hEq | hodd
  · exfalso
    apply hlN
    have hmem : pslMk (fixedSubfield F p f) w ∈
        (W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) :=
      ⟨w, Subgroup.mem_comap.2 hlW, rfl⟩
    rw [hEq] at hmem
    exact levi_mem_normA0_of_psl_normalizer hζ0 hζ hF hω hq3 hmem
  ·
    set C := Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) with hC
    set H := (W.comap (levi hζ0 hζ)).map (pslMk (fixedSubfield F p f)) with hH
    have hq : 2 ≤ p ^ f := two_le_prime_pow_of_card' hF
    have hqodd : Odd (p ^ f) := Nat.odd_iff.2 (by omega)
    have hcW := card_inf_centralizer_zSU_eq hζ0 hζ hF hp2 W hTW
    have hcT := card_inf_centralizer_zSU_eq hζ0 hζ hF hp2 ⊤ le_top
    have hPSL := CFSG.Glauberman.Dickson.MaxUp.card_psl2_odd hF0 hp2
    have htopH : ((⊤ : Subgroup (SU (unitaryInvolution F p f) 3)).comap (levi hζ0 hζ)).map
        (pslMk (fixedSubfield F p f)) = ⊤ := by
      rw [Subgroup.comap_top, Subgroup.map_top_of_surjective _ (pslMk_surjective _)]
    rw [htopH, Subgroup.card_top, top_inf_eq, hPSL] at hcT
    have hdiv : 2 * (p ^ f * ((p ^ f) ^ 2 - 1) / 2) = p ^ f * ((p ^ f) ^ 2 - 1) := by
      apply Nat.mul_div_cancel'
      obtain ⟨a, ha⟩ := hqodd
      have h : (p ^ f) ^ 2 = 2 * (2 * a * (a + 1)) + 1 := by rw [ha]; ring
      exact Dvd.dvd.mul_left ⟨2 * a * (a + 1), Nat.sub_eq_of_eq_add h⟩ _
    rw [hdiv] at hcT
    have hm := Subgroup.relIndex_mul_card W C
    rw [Subgroup.inf_relIndex_right]
    have hCard : Nat.card ↥H * H.index = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
      rw [← hPSL]; exact Subgroup.card_mul_index H
    have hs0 : (p ^ f) ^ 2 - 1 ≠ 0 := by
      have : 4 ≤ (p ^ f) ^ 2 := by nlinarith
      omega
    have hh0 : 0 < Nat.card ↥H := Nat.card_pos
    have e1 : W.relIndex C * (2 * Nat.card ↥H * ((p ^ f) ^ 2 - 1)) =
        p ^ f * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 2 - 1) := by
      calc W.relIndex C * (2 * Nat.card ↥H * ((p ^ f) ^ 2 - 1))
          = W.relIndex C * (Nat.card ↥(W ⊓ C) * (p ^ f - 1)) := by rw [hcW]
        _ = (W.relIndex C * Nat.card ↥(W ⊓ C)) * (p ^ f - 1) := by ring
        _ = Nat.card ↥C * (p ^ f - 1) := by rw [hm]
        _ = p ^ f * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 2 - 1) := hcT
    have e2 : W.relIndex C * (2 * Nat.card ↥H) = p ^ f * ((p ^ f) ^ 2 - 1) := by
      refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hs0) ?_
      calc W.relIndex C * (2 * Nat.card ↥H) * ((p ^ f) ^ 2 - 1)
          = W.relIndex C * (2 * Nat.card ↥H * ((p ^ f) ^ 2 - 1)) := by ring
        _ = p ^ f * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 2 - 1) := e1
    have e3 : 2 * (Nat.card ↥H * H.index) = p ^ f * ((p ^ f) ^ 2 - 1) := by
      rw [hCard, hdiv]
    have e4 : W.relIndex C = H.index := by
      refine Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * Nat.card ↥H) ?_
      calc 2 * Nat.card ↥H * W.relIndex C = W.relIndex C * (2 * Nat.card ↥H) := by ring
        _ = p ^ f * ((p ^ f) ^ 2 - 1) := e2
        _ = 2 * (Nat.card ↥H * H.index) := e3.symm
        _ = 2 * Nat.card ↥H * H.index := by ring
    rw [e4]
    exact hodd

end Good

section Core


theorem f1Core_SU3_of_mod4_three (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq3 : (p ^ f) % 3 = 1) (hq4 : (p ^ f) % 4 = 3) :
    F1Core (SU (unitaryInvolution F p f) 3) := by
  have hq2 := two_le_prime_pow_of_card' hF
  have hF3 : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have h2 : (p ^ f) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
    have h3 : 1 ≤ (p ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 hF3
  have hD : ∀ A H : Subgroup (PSL2MatrixGroup (fixedSubfield F p f)), Nat.card A = 3 →
      Nat.card (fixedSubfield F p f) - 1 ∣
        Nat.card (Subgroup.normalizer (A : Set (PSL2MatrixGroup (fixedSubfield F p f)))) →
      Subgroup.normalizer (A : Set _) ≤ H → H = Subgroup.normalizer (A : Set _) ∨ ¬ 2 ∣ H.index :=
    fun A H hA _ hAH => psl2_normalizer_three_dichotomy (K := fixedSubfield F p f) (p := p) (f := f)
      (card_fixedSubfield hF) (by rw [card_fixedSubfield hF]; exact hq3)
      (by rw [card_fixedSubfield hF]; exact hq4) hA hAH
  obtain ⟨c, hc⟩ := exists_norm_eq_neg_one hF
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_char_ne_two hp2
  refine f1Core_of_A0 (A₀ := Subgroup.zpowers (tSU hF ω)) ?_ ?_
  · rw [Nat.card_zpowers, orderOf_injective (tSU hF) (tSU_injective hF) ω, hω]
  · intro W Y hNW hYW hAY hY hWtop S hS hSW
    have hNW' : normA0 hF ω ≤ W := hNW
    by_cases hbad : ∀ x ∈ W, x * zSU hF = zSU hF * x → x ∈ normA0 hF ω
    · exfalso
      obtain ⟨ν, -, hν2, hνq⟩ := exists_unit_orderOf_card_add_one hF hp2
      exact (badCase_model hF hp2 hω hq3 hq4 hν2 hνq hNW' hbad).false_of_isLThreeTwo hYW
        (hAY (Subgroup.mem_zpowers _)) hY
    · push Not at hbad
      have hodd := relIndex_centralizer_odd hF hp2 hq3 hq4 hD hω hNW' hbad
      obtain ⟨S₀, hS₀⟩ := exists_isSylowOf 2
        (W ⊓ Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)))
      have hS₀le := hS₀.le
      have hS₀L : IsSylowOf 2 S₀
          (Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3))) := by
        rw [isSylowOf_iff] at hS₀ ⊢
        obtain ⟨hle, hp, hidx⟩ := hS₀
        refine ⟨hle.trans inf_le_right, hp, ?_⟩
        rw [← Subgroup.relIndex_mul_relIndex S₀ _ _ hle inf_le_right]
        intro hd
        rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hd with h | h
        · exact hidx h
        · exact hodd h
      have hXtop := isSylowOf_stdSylG hF h2 hc hq4
      have hXL := hXtop.of_le (stdSylG_le_centralizer hF h2 hc) le_top
      have hS₀top : IsSylowOf 2 S₀ ⊤ := by
        refine isSylowOf_of_card le_top ?_
        rw [hS₀L.card_eq, ← hXL.card_eq, hXtop.card_eq, Subgroup.card_top]
      have hS₀W : IsSylowOf 2 S₀ W := hS₀top.of_le (hS₀le.trans inf_le_left) le_top
      have hSW' : IsSylowOf 2 S W := hS.of_le hSW le_top
      obtain ⟨w, hwW, hw⟩ := exists_conj_of_isSylowOf_two hS₀W hSW'
      intro n hn
      have hn' := mem_normalizer_of_conj hw hn
      obtain ⟨s, hsS₀, l, hl, hnl⟩ := star_G hF h2 hc hq4 hS₀L hn'
      have hsW : s ∈ W := (hS₀le hsS₀).1
      have htW : tSU hF l ∈ W := hNW' (range_tSU_le_normA0 hF hω hq3 ⟨l, rfl⟩)
      have hmem : w⁻¹ * n * w ∈ W := hnl ▸ W.mul_mem hsW htW
      have hnW : n = w * (w⁻¹ * n * w) * w⁻¹ := by group
      rw [hnW]
      exact W.mul_mem (W.mul_mem hwW hmem) (W.inv_mem hwW)

end Core

end F1Proof

end CFSG.LocalAnalysis.RankThreeUC.S15
