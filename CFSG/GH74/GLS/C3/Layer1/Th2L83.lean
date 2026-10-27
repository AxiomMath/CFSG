module

public import CFSG.GH74.GLS.C3.Layer1.Th2L83A5
public import CFSG.GH74.GLS.C3.Layer1.Th2L83A7
public import CFSG.GH74.GLS.C3.Layer1.Th2L84

public section

namespace CFSG.GH74.GLS.Th2.L83

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.Th2
  CFSG.GH74.GLS.C3.Layer1

variable {G : Type} [Group G]

theorem inner_conj_mem {K : Type} [Group K] (φ ψ : MulAut K)
    (h : ψ ∈ (MulAut.conj : K →* MulAut K).range) :
    φ * ψ * φ⁻¹ ∈ (MulAut.conj : K →* MulAut K).range := by
  obtain ⟨a, rfl⟩ := h
  refine ⟨φ a, ?_⟩
  ext z
  simp [MulAut.conj_apply]

theorem actHom_not_inner {K X : Subgroup G} (hKX : ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hKXle : K ≤ X)
    {y : G} (hyX : y ∈ X) (hy : y ∉ K ⊔ centralizerSection K (pPrimeCoreOf 2 K)) :
    Back.actHom hKX ⟨y, hyX⟩ ∉ (MulAut.conj : kBar K →* MulAut (kBar K)).range := by
  rintro ⟨z, hz⟩
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 := Back.actHom_of_mem hKX k.2 (hKXle k.2)
  have hkyX : (k : G)⁻¹ * y ∈ X := X.mul_mem (X.inv_mem (hKXle k.2)) hyX
  have h2 : Back.actHom hKX ⟨(k : G)⁻¹ * y, hkyX⟩ = 1 := by
    have e : (⟨(k : G)⁻¹ * y, hkyX⟩ : ↥X) = (⟨(k : G), hKXle k.2⟩ : ↥X)⁻¹ * ⟨y, hyX⟩ := rfl
    rw [e, map_mul, map_inv, h1, ← hz]
    simp
  have h3 : (⟨(k : G)⁻¹ * y, hkyX⟩ : ↥X) ∈ (Back.actHom hKX).ker := h2
  rw [Back.actHom_ker, Subgroup.mem_subgroupOf] at h3
  have h4 : (k : G)⁻¹ * y ∈ centralizerSection K (pPrimeCoreOf 2 K) := h3.2
  apply hy
  have : y = (k : G) * ((k : G)⁻¹ * y) := by group
  rw [this]
  exact Subgroup.mul_mem_sup k.2 h4

variable [Finite G]

theorem exists_outer_elemAbelian {x y : G} {K T S : Subgroup G} (h : Th2Std x y K T S)
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hyc : y ∈ centralizer ({x} : Set G))
    (hy : y ∉ K ⊔ centralizerSection K (pPrimeCoreOf 2 K)) (hy2 : orderOf y = 2)
    {F : Subgroup G} (hFel : CFSG.IsElementaryAbelian 2 ↥F)
    (hFC : F ≤ centralizer ({x, y} : Set G)) :
    ∃ (A : Subgroup G) (hAT : A ≤ T), CFSG.IsElementaryAbelian 2 ↥A ∧ pRank 2 ↥F ≤ pRank 2 ↥A ∧
      ∃ (a : G) (ha : a ∈ A), Back.actHom hKN ⟨a, h.T_le_C (hAT ha)⟩ ∉
        (MulAut.conj : kBar K →* MulAut (kBar K)).range := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFy : ∀ f ∈ F, f * y = y * f := by
    intro f hf
    have := Subgroup.mem_centralizer_iff.1 (hFC hf) y (by simp)
    exact this.symm
  have hzel : CFSG.IsElementaryAbelian 2 ↥(zpowers y) := isElementaryAbelian_zpowers_of_orderOf_two hy2
  have hA₀el : CFSG.IsElementaryAbelian 2 ↥(F ⊔ zpowers y) := by
    refine isElementaryAbelian_sup hFel hzel fun f hf z hz => ?_
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hz
    exact (Commute.zpow_right (hFy f hf) m).eq
  have hA₀X : F ⊔ zpowers y ≤ centralizer ({x} : Set G) := by
    exact sup_le (hFC.trans (Subgroup.centralizer_le (by simp : ({x} : Set G) ⊆ {x, y})))
      (zpowers_le.2 hyc)
  obtain ⟨g, hgX, hgA⟩ := exists_cj_le_of_isSylowOf h.setup.sylowT hA₀X
    (CFSG.IsElementaryAbelian.isPGroup 2 ↥(F ⊔ zpowers y))
  refine ⟨cj g (F ⊔ zpowers y), hgA, isElementaryAbelian_cj g hA₀el, ?_, ?_⟩
  · rw [pRank_cj]
    exact Back.pRank_mono' le_sup_left
  · have hyA : g * y * g⁻¹ ∈ cj g (F ⊔ zpowers y) :=
      ⟨y, Subgroup.mem_sup_right (mem_zpowers y), by simp [MulAut.conj_apply]⟩
    refine ⟨g * y * g⁻¹, hyA, ?_⟩
    have hmem : g * y * g⁻¹ ∈ centralizer ({x} : Set G) := h.T_le_C (hgA hyA)
    have hout := actHom_not_inner hKN h.K_le_C hyc hy
    intro hin
    have e : (⟨g * y * g⁻¹, hmem⟩ : ↥(centralizer ({x} : Set G))) =
        ⟨g, hgX⟩ * ⟨y, hyc⟩ * ⟨g, hgX⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at hin
    apply hout
    have := inner_conj_mem (Back.actHom hKN ⟨g, hgX⟩)⁻¹ _ hin
    simpa [mul_assoc] using this


section Rows

variable {x y : G} {K T S M : Subgroup G}

theorem l83_rows_L2 (hG : C3Hyp G) (h : Th2Std x y K T S) {Pr : ℕ → Prop}
    (hPr : ∀ q, Pr q → Odd q) (hq5 : ∀ q, Pr q → q ≠ 5) (hL2 : HasL2Model (kBar K) Pr)
    (h6 : Bk.B_ivk_6) {B : Subgroup G} (hB : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B)
    (hM : gammaK 2 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B''}, B') 3 ≤ M) :
    K ≤ M := by
  have hcen := centerlessBar_of_hasL2Model hPr hL2
  have hP := rankTwoShape_sylow_L2 h.sylow_P (TwoThin.isQuasisimple_hat h.comp) hPr hL2
  have hKN := h.K_normal_L2 hG hPr hL2
  have hPQ := h.commDisj hcen
  obtain ⟨U, hU, E, hE, hrk, -⟩ := (isS_sup_iff hPQ hP B).1 hB
  refine l83_L2_core h hcen hP hKN ?_ h6 hE.1 hE.2.1 hrk ?_
  · obtain ⟨p, f, hp, hf, hq, hmodel⟩ := hL2
    exact ⟨p, f, hp, hf, hPr _ hq, hq5 _ hq, hmodel⟩
  · intro U' hU' F hF hFr
    have hmem : U' ⊔ E ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B''} :=
      (isS_sup_iff hPQ hP _).2 ⟨U', hU', E, hE, hrk, rfl⟩
    have hle : F ≤ ⨆ B' ∈ {B'' : Subgroup G | IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B''}, B' :=
      hF.trans (le_iSup₂_of_le (U' ⊔ E) hmem le_rfl)
    refine le_trans ?_ hM
    unfold gammaK
    exact le_iSup₂_of_le F hle (le_iSup_of_le hFr le_rfl)

theorem l83_rows_A7 (hG : C3Hyp G) (h : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {B D : Subgroup G} (hBE : IsE 4 T B)
    (hD : IsDSub K (T ⊓ K) D) (hDB : D ≤ B) (hM : gammaK 2 B 3 ≤ M) : K ≤ M := by
  refine l83_A7_core (X := centralizer ({x} : Set G)) (P := T ⊓ K) (r := 3)
    (h.K_normal_A7 hG h7) h.sylow_P ?_ hBE.2.1 (by simpa using hBE.2.2) hD hDB ?_
  · exact hBE.1.trans h.T_le_C
  · intro F hFB hFr
    refine le_trans ?_ hM
    unfold gammaK
    exact le_iSup₂_of_le F hFB (le_iSup_of_le hFr le_rfl)

theorem row3a_l83_general {x y : G} {K T S M B : Subgroup G}
    (h2 : Th2M2 x y K T S M .r3a B)
    (hM : gammaK 2 B 4 ≤ M) : K ≤ M := by
  have hstd := h2.std
  obtain ⟨hSn5, D, hD, hDB⟩ := h2.mem
  have hE := h2.isE
  simp only [Th2Row.level, Th2Level.minRank] at hE
  obtain ⟨hBT, hBel, hBr⟩ := hE
  have hBC : B ≤ centralizer ({x} : Set G) := hBT.trans hstd.T_le_C
  have hBN : B ≤ normalizer (K : Set G) := by
    have hBR : B ≤ (T ⊓ K) ⊔ (T ⊓ CxK x K) := hSn5.1.1
    refine hBR.trans (sup_le ?_ ?_)
    · exact inf_le_right.trans Subgroup.le_normalizer
    · exact inf_le_right.trans ((CxK_le_NxK x K).trans inf_le_right)
  let X := NxK x K
  have hBX : B ≤ X := le_inf hBC hBN
  have hKX : ∀ a ∈ X, ∀ k ∈ K, a * k * a⁻¹ ∈ K := by
    intro a ha k hk
    exact (Subgroup.mem_normalizer_iff.1 ha.2 _).1 hk
  have hP : IsSylowOf 2 (T ⊓ K) K := hstd.sylow_P
  refine l83_A7_core (X := X) (P := T ⊓ K) (r := 4) hKX hP hBX hBel hBr hD hDB ?_
  intro F hFB hFr
  refine le_trans ?_ hM
  unfold gammaK
  exact le_iSup₂_of_le F hFB (le_iSup_of_le hFr le_rfl)

theorem row3a_l83 {x y : G} {K T S M B : Subgroup G}
    (h2 : Th2M2 x y K T S M .r3a B) : K ≤ M :=
  row3a_l83_general h2 (row3a_gamma b_ig_21_10 h2).1

theorem l83_row_4c (hG : C3Hyp G) (h : Th2Std x y K T S)
    (hL2 : HasL2Model (kBar K) (fun q => q = 5)) {B : Subgroup G} (hB : IsSn 4 T B)
    (hM : gammaK 2 B 2 ≤ M) : K ≤ M := by
  have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
  have hKN := h.K_normal_L2 hG hPr hL2
  obtain ⟨e5⟩ := C3.Layer1.Back.nonempty_alt5_of_hasL2Model5 hL2
  refine l83_A5_two hKN e5 (hB.1.1.trans h.T_le_C) hB.1.2.1 hB.2 ?_
  intro F hFB hFr
  refine le_trans ?_ hM
  unfold gammaK
  exact le_iSup₂_of_le F hFB (le_iSup_of_le hFr le_rfl)

theorem l83_row_4b (hG : C3Hyp G) (h : Th2Std x y K T S)
    (hL2 : HasL2Model (kBar K) (fun q => q = 5)) (hunb : IsUnbalancingTriple x y K)
    (hr : pRank 2 ↥(centralizer ({x, y} : Set G)) = 4) (h6 : Bk.B_ivk_6) (h10a : B_ivk_10_2a)
    (hM : ∀ A : Subgroup G, IsE 4 (⨆ B' ∈ {B'' : Subgroup G | IsSn 4 T B''}, B') A →
      gammaK 2 A 3 ≤ M) : K ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
  have hKN := h.K_normal_L2 hG hPr hL2
  obtain ⟨e5⟩ := C3.Layer1.Back.nonempty_alt5_of_hasL2Model5 hL2
  have hL2odd : HasL2Model (kBar K) Odd := C3.Layer1.Back.hasL2Model_mono hPr hL2
  have hL2fm : HasL2Model (kBar K) IsFM9 := by
    refine C3.Layer1.Back.hasL2Model_mono ?_ hL2
    rintro q rfl
    exact Th2Tstar.isFM9_five
  have hy := h10a G hG x y K h.v2ss.isV2Triple hL2fm
  obtain ⟨F, hFC, hFel, hFrk⟩ := exists_elemAbelian_pRank (centralizer ({x, y} : Set G))
  obtain ⟨A, hAT, hAel, hAF, a, ha, hnot⟩ :=
    exists_outer_elemAbelian h hKN hunb.2.2.1 hy hunb.2.1 hFel hFC
  have hAX : A ≤ centralizer ({x} : Set G) := hAT.trans h.T_le_C
  have hrkA : 4 ≤ pRank 2 ↥A := by omega
  obtain ⟨B₀, hAB₀, hB₀⟩ := exists_maximal_elemAbelian hAT hAel
  have hB₀mem : B₀ ∈ {B'' : Subgroup G | IsSn 4 T B''} :=
    ⟨hB₀, hrkA.trans (Back.pRank_mono' hAB₀)⟩
  have hAle : A ≤ ⨆ B' ∈ {B'' : Subgroup G | IsSn 4 T B''}, B' :=
    hAB₀.trans (le_iSup₂_of_le B₀ hB₀mem le_rfl)
  have hc := hM A ⟨hAle, hAel, hrkA⟩
  refine l83_A5_three hKN e5 hL2odd h6 hAX hAel hrkA ⟨a, ha, hnot⟩ ?_
  intro F' hF'A hF'r
  refine le_trans ?_ hc
  unfold gammaK
  exact le_iSup₂_of_le F' hF'A (le_iSup_of_le hF'r le_rfl)

end Rows

end CFSG.GH74.GLS.Th2.L83

namespace CFSG.GH74.GLS

open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.Th2 CFSG.GH74.GLS.Th2.L83

theorem b_thm2_l83_of (hL34 : B_gen4_noL34_elem) (h82 : B_thm2_l82) (h6 : C3.Layer1.Bk.B_ivk_6)
    (h10a : B_ivk_10_2a) : B_thm2_l83 := by
  intro G _ _ hG x y K T S M ρ B h2
  have hstd := h2.std
  have hrow := h2.row
  have hmem := h2.mem
  have hE := h2.isE
  have h82' := h82 G hG x y K T S M ρ B h2
  cases ρ with
  | r1a =>
    obtain ⟨hL2, -, h3⟩ := hrow
    have hPr : ∀ q : ℕ, (Odd q ∧ ¬ IsFM9 q) → Odd q := fun q hq => hq.1
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_hasL2Model hPr hL2)
      (rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL2) h3).elim
  | r1b =>
    obtain ⟨hL2, -⟩ := hrow
    have hPr : ∀ q : ℕ, (Odd q ∧ ¬ IsFM9 q) → Odd q := fun q hq => hq.1
    have hmem' : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B := hmem
    exact l83_rows_L2 hG hstd hPr (fun q hq h5 => hq.2 (h5 ▸ Th2Tstar.isFM9_five)) hL2 h6 hmem'
      (h82'.1 (by decide) (by decide))
  | r2 =>
    have hPr : ∀ q : ℕ, (Odd q ∧ IsFM9 q ∧ q ≠ 5) → Odd q := fun q hq => hq.1
    have hmem' : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B := hmem
    exact l83_rows_L2 hG hstd hPr (fun q hq => hq.2.2) hrow h6 hmem'
      (h82'.1 (by decide) (by decide))
  | r3a =>
    exact row3a_l83 h2
  | r3b =>
    obtain ⟨h7, -, -⟩ := hrow
    obtain ⟨D, hD, hBeq⟩ := hmem
    have hDB : D ≤ B := by
      rw [hBeq]
      intro d hd
      exact Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem S.one_mem ⟨d, hd, by simp⟩)
    exact l83_rows_A7 hG hstd h7 hE hD hDB h82'.2.2.2
  | r3c =>
    obtain ⟨h7, -⟩ := hrow
    have hmem' : IsSn 4 ((T ⊓ K) ⊔ (T ⊓ CxK x K)) B ∧ ∃ D, IsDSub K (T ⊓ K) D ∧ D ≤ B := hmem
    obtain ⟨-, D, hD, hDB⟩ := hmem'
    exact l83_rows_A7 hG hstd h7 hE hD hDB h82'.2.2.2
  | r4a =>
    obtain ⟨hL2, h3⟩ := hrow
    have hPr : ∀ q : ℕ, q = 5 → Odd q := by rintro q rfl; decide
    exact (false_of_three_le_rank_Q hG hstd (centerlessBar_of_hasL2Model hPr hL2)
      (rankTwoShape_sylow_L2 hstd.sylow_P (TwoThin.isQuasisimple_hat hstd.comp) hPr hL2) h3).elim
  | r4b =>
    obtain ⟨hL2, -, hr, hunb⟩ := hrow
    exact l83_row_4b hG hstd hL2 hunb hr h6 h10a h82'.2.2.1
  | r4c =>
    obtain ⟨hL2, -, -⟩ := hrow
    have hmem' : IsSn 4 T B := hmem
    exact l83_row_4c hG hstd hL2 hmem' h82'.2.2.2
  | r5 =>
    obtain ⟨hL34', hel, hcard⟩ := hrow
    exact (hL34 G hG.gen4 x K hstd.orderOf_x hstd.comp ⟨hL34', hel, hcard⟩).elim

end CFSG.GH74.GLS
