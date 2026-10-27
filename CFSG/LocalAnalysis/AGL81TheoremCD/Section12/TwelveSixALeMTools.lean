module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixTInvariant
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixToNineStmt

import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.RankThreeUC.AGL81I.Section9.Base
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Sylow
import CFSG.CGT.Timmesfeld75.Sec4TwoBender
import CFSG.GH74.QTGen4.U42.VertexGen4B
import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicSylowGL

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeUC.AGL81C Subgroup
open scoped MatrixGroups Pointwise
open CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Syl
open CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Off

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ}

theorem exists_conj_le_of_le_sup_of_not_three_dvd {O V U : Subgroup G}
    (hO3 : ¬ 3 ∣ Nat.card O) (hV : IsPGroup 3 V) (hVO : V ≤ normalizer (O : Set G))
    (hU : IsPGroup 3 U) (hUVO : U ≤ V ⊔ O) :
    ∃ o ∈ O, U.map (MulAut.conj o).toMonoidHom ≤ V := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hVsyl : IsSylowOf 3 V (V ⊔ O) := isSylowOf_sup hV hO3 hVO
  obtain ⟨P, hP, hUP⟩ := exists_isSylowOf_of_le (p := 3) hU hUVO
  obtain ⟨k, hkVO, hk⟩ := hVsyl.exists_mem_conj hP
  have hkVO' : k ∈ ((V ⊔ O : Subgroup G) : Set G) := hkVO
  have hcoe : ((V ⊔ O : Subgroup G) : Set G) = (O : Set G) * (V : Set G) := by
    rw [sup_comm]
    exact Subgroup.coe_mul_of_right_le_normalizer_left O V hVO
  rw [hcoe] at hkVO'
  obtain ⟨o, hoO, v, hvV, rfl⟩ := hkVO'
  refine ⟨o⁻¹, O.inv_mem hoO, ?_⟩
  intro x hx
  obtain ⟨u, hu, rfl⟩ := hx
  have h1 : (o * v)⁻¹ * u * (o * v) ∈ V := (hk u).mp (hUP hu)
  have hkey : (MulAut.conj o⁻¹).toMonoidHom u =
      v * ((o * v)⁻¹ * u * (o * v)) * v⁻¹ := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  rw [hkey]
  exact V.mul_mem (V.mul_mem hvV h1) (V.inv_mem hvV)

theorem exists_mul_mem_normalizer_of_not_three_dvd {O W : Subgroup G} {s : G}
    (hO3 : ¬ 3 ∣ Nat.card O) (hW : IsPGroup 3 W) (hWO : W ≤ normalizer (O : Set G))
    (hsW : ∀ w ∈ W, s * w * s⁻¹ ∈ W ⊔ O) : ∃ o ∈ O, o * s ∈ normalizer (W : Set G) := by
  have hW' : IsPGroup 3 (W.map (MulAut.conj s).toMonoidHom) := hW.map _
  have hle' : W.map (MulAut.conj s).toMonoidHom ≤ W ⊔ O := by
    rintro x ⟨w, hw, rfl⟩
    simpa [MulAut.conj_apply] using hsW w hw
  obtain ⟨o, ho, hconj⟩ :=
    exists_conj_le_of_le_sup_of_not_three_dvd hO3 hW hWO hW' hle'
  refine ⟨o, ho, ?_⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change W.map (MulAut.conj (o * s)).toMonoidHom = W
  have hmap : W.map (MulAut.conj (o * s)).toMonoidHom =
      (W.map (MulAut.conj s).toMonoidHom).map (MulAut.conj o).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨s * w * s⁻¹, ⟨w, hw, rfl⟩, by group⟩
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨w, hw, by group⟩
  rw [hmap]
  have hcard : Nat.card ((W.map (MulAut.conj s).toMonoidHom).map
      (MulAut.conj o).toMonoidHom) = Nat.card W := by
    rw [Subgroup.card_map_of_injective (MulAut.conj o).injective,
      Subgroup.card_map_of_injective (MulAut.conj s).injective]
  exact Subgroup.eq_of_le_of_card_ge hconj (by rw [hcard])

private lemma eq_one_or_eq_or_eq_inv_of_mem_of_card_three {W : Subgroup G}
    (hW : Nat.card W = 3) {w : G} (hwW : w ∈ W) (hw1 : w ≠ 1) {x : G} (hxW : x ∈ W) :
    x = 1 ∨ x = w ∨ x = w⁻¹ := by
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  have hordw : orderOf w = 3 := by
    have hdvd := Subgroup.orderOf_dvd_natCard W hwW
    rw [hW] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hw1
    · exact h
  have hwinv : w⁻¹ ≠ w := by
    intro h
    have h2 : w ^ 2 = 1 := by
      rw [pow_two]
      calc w * w = w⁻¹ * w := by rw [h]
        _ = 1 := inv_mul_cancel w
    have hdvd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    rw [hordw] at hdvd
    norm_num at hdvd
  have hset : ({1, w, w⁻¹} : Set G) = (W : Set G) := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite (W : Set G))
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · exact W.one_mem
      · exact hwW
      · exact W.inv_mem hwW
    · have h1 : (W : Set G).ncard = 3 := by
        rw [← Nat.card_coe_set_eq]
        exact hW
      have h2 : ({1, w, w⁻¹} : Set G).ncard = 3 := by
        rw [Set.ncard_eq_three]
        refine ⟨1, w, w⁻¹, hw1.symm, ?_, hwinv.symm, rfl⟩
        intro h
        exact hw1 (by simpa using (congrArg Inv.inv h).symm)
      omega
  have hx : x ∈ ({1, w, w⁻¹} : Set G) := by
    rw [hset]
    exact hxW
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx

private lemma mem_centralizer_of_maps_gen {W : Subgroup G} (hW : Nat.card W = 3)
    {w : G} (hwW : w ∈ W) (hw1 : w ≠ 1) {s : G} (hs : s * w * s⁻¹ = w) :
    s ∈ centralizer (W : Set G) := by
  have hsw : Commute s w := by
    rw [commute_iff_eq]
    calc s * w = (s * w * s⁻¹) * s := by group
      _ = w * s := by rw [hs]
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hsx : Commute s x := by
    rcases eq_one_or_eq_or_eq_inv_of_mem_of_card_three hW hwW hw1 hx with rfl | rfl | rfl
    · exact Commute.one_right s
    · exact hsw
    · exact hsw.inv_right
  exact ((commute_iff_eq s x).mp hsx).symm

theorem normalizer_le_of_inverted {M W : Subgroup G} {t : G} (hW : Nat.card W = 3)
    (hCW : centralizer (W : Set G) ≤ M) (htM : t ∈ M)
    (ht : ∀ w ∈ W, t * w * t⁻¹ = w⁻¹) : normalizer (W : Set G) ≤ M := by
  intro g hg
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  haveI : Nontrivial W := by
    rw [← Finite.one_lt_card_iff_nontrivial, hW]
    norm_num
  obtain ⟨w, hwW, hw1⟩ := Subgroup.exists_ne_one_of_nontrivial W
  have hgW : g * w * g⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hg w).mp hwW
  have hgW1 : g * w * g⁻¹ ≠ 1 := by
    intro h
    apply hw1
    have := congrArg (fun x => g⁻¹ * x * g) h
    simpa [mul_assoc] using this
  have htinv : t⁻¹ * w * t = w⁻¹ := by
    have h2 : t⁻¹ * w⁻¹ * t = w := by
      calc t⁻¹ * w⁻¹ * t = t⁻¹ * (t * w * t⁻¹) * t := by
            rw [ht w hwW]
        _ = w := by group
    calc t⁻¹ * w * t = (t⁻¹ * w⁻¹ * t)⁻¹ := by group
      _ = w⁻¹ := by rw [h2]
  rcases eq_one_or_eq_or_eq_inv_of_mem_of_card_three hW hwW hw1 hgW with h1 | h1 | h1
  · exact absurd h1 hgW1
  · exact hCW (mem_centralizer_of_maps_gen hW hwW hw1 h1)
  · have hgtw : (g * t⁻¹) * w * (g * t⁻¹)⁻¹ = w := by
      calc (g * t⁻¹) * w * (g * t⁻¹)⁻¹ = g * (t⁻¹ * w * t) * g⁻¹ := by
            group
        _ = g * w⁻¹ * g⁻¹ := by rw [htinv]
        _ = w := by
            rw [show g * w⁻¹ * g⁻¹ = (g * w * g⁻¹)⁻¹ by group, h1, inv_inv]
    rw [show g = (g * t⁻¹) * t by group]
    exact M.mul_mem (hCW (mem_centralizer_of_maps_gen hW hwW hw1 hgtw)) htM

private lemma three_dvd_card_psl_two_pow {n : ℕ} (hn : 2 ≤ n) :
    3 ∣ Nat.card (PSL(2, GaloisField 2 n)) := by
  rw [CFSG.GH74.QTGen4.U42.VertexGen4B.card_psl_galois (by omega : 1 ≤ n)]
  refine dvd_mul_of_dvd_right ?_ _
  have h4 : 4 ^ n ≡ 1 ^ n [MOD 3] := Nat.ModEq.pow n (by decide)
  rw [one_pow] at h4
  have hpow : (2 ^ n) ^ 2 - 1 = 4 ^ n - 1 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hpow]
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow n 4 (by norm_num))).1 h4.symm

theorem le_pCoreOf_two_of_isPSLType {I N : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hI : IsPSLType 2 (GaloisField 2 n) (modTwoCore I)) (hNI : N ≤ I)
    (hIN : I ≤ normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N) : N ≤ pCoreOf 2 I := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Subgroup ↥I := CFSG.pCore 2 ↥I
  let π : ↥I →* modTwoCore I := QuotientGroup.mk' P
  let B : Subgroup ↥I := N.subgroupOf I
  have hBn : B.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNI).mpr hIN
  let K : Subgroup (modTwoCore I) := B.map π
  haveI : K.Normal := hBn.map π (QuotientGroup.mk'_surjective P)
  obtain ⟨e⟩ := hI
  haveI : IsSimpleGroup (modTwoCore I) :=
    CFSG.CGT.Timmesfeld75.isSimpleGroup_of_psl2 hn e
  rcases (Subgroup.Normal.eq_bot_or_eq_top K) with hbot | htop
  · have hBle : B ≤ P := by
      intro x hx
      have hxbot : π x ∈ K := Subgroup.mem_map_of_mem π hx
      rw [hbot] at hxbot
      exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hxbot)
    calc N = B.map I.subtype := (Subgroup.map_subgroupOf_eq_of_le hNI).symm
      _ ≤ P.map I.subtype := Subgroup.map_mono hBle
      _ = pCoreOf 2 I := rfl
  · exfalso
    have h3psl : 3 ∣ Nat.card (PSL(2, GaloisField 2 n)) := three_dvd_card_psl_two_pow hn
    have h3K : 3 ∣ Nat.card K := by
      rw [htop, Subgroup.card_top, Nat.card_congr e.toEquiv]
      exact h3psl
    have hdvd : Nat.card K ∣ Nat.card B := Subgroup.card_map_dvd (H := B) π
    have h3B : 3 ∣ Nat.card B := h3K.trans hdvd
    have hcardB : Nat.card B = Nat.card N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNI).toEquiv
    exact hN3 (hcardB ▸ h3B)

theorem le_sup_relPPrimeCore_of_starImg_le (hp : p.Prime) {H A B : Subgroup G} (hAH : A ≤ H)
    (hAB : starImg p H A ≤ starImg p H B) : A ≤ B ⊔ relPPrimeCore p H := by
  haveI : Fact p.Prime := ⟨hp⟩
  let O : Subgroup ↥H := CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore (G := ↥H) p
  let π : ↥H →* StarGroup p H := QuotientGroup.mk' O
  have h2 : (A.subgroupOf H).map π ≤ (B.subgroupOf H).map π := hAB
  have h3 : A.subgroupOf H ≤ B.subgroupOf H ⊔ π.ker := by
    have := Subgroup.map_le_iff_le_comap.mp h2
    rwa [Subgroup.comap_map_eq] at this
  calc A = (A.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le hAH).symm
    _ ≤ ((B.subgroupOf H ⊔ π.ker).map H.subtype) := Subgroup.map_mono h3
    _ = (B.subgroupOf H).map H.subtype ⊔ (π.ker).map H.subtype := by rw [Subgroup.map_sup]
    _ ≤ B ⊔ relPPrimeCore p H := by
        refine sup_le ?_ ?_
        · rw [Subgroup.subgroupOf_map_subtype]
          exact inf_le_left.trans le_sup_left
        · have hker : π.ker = O := QuotientGroup.ker_mk' O
          rw [hker, ← nineTenGen_relPPrimeCore_eq_map hp H]
          exact le_sup_right

theorem lt_finrank_of_dvd_card_linearEquiv {K : Type*} [Field K] [Finite K] {S : Type*}
    [AddCommGroup S] [Module K S] [FiniteDimensional K S] {r m : ℕ} (hr : r.Prime)
    (hrK : ¬ r ∣ Nat.card K) (hj : ∀ j, 1 ≤ j → j ≤ m → ¬ r ∣ Nat.card K ^ j - 1)
    (hdvd : r ∣ Nat.card (S ≃ₗ[K] S)) : m < Module.finrank K S := by
  classical
  haveI : Fact r.Prime := ⟨hr⟩
  have : Fintype K := Fintype.ofFinite K
  by_contra hlt
  push Not at hlt
  have h0 : ¬ r ∣ Fintype.card K := by
    rwa [Nat.card_eq_fintype_card] at hrK
  have hj' : ∀ j, 1 ≤ j → j ≤ Module.finrank K S → ¬ r ∣ Fintype.card K ^ j - 1 :=
    fun j hj1 hjn => by simpa [Nat.card_eq_fintype_card] using hj j hj1 (hjn.trans hlt)
  have hnot := CFSG.AGLEmbeddingD2.CyclicSylowGL.not_dvd_card_GL
    (k := K) (r := r) (m := Module.finrank K S) h0 hj'
  have hcard : Nat.card (S ≃ₗ[K] S) =
      Nat.card (GL (Fin (Module.finrank K S)) K) := by
    let basis := Module.finBasis K S
    let equivalence := (Matrix.GeneralLinearGroup.toLin' basis).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K S)
    exact (Nat.card_congr equivalence.toEquiv).symm
  rw [hcard] at hdvd
  exact hnot hdvd

private lemma conj_inv_eq_of_conj_eq {t w : G} (h : t * w * t⁻¹ = w) :
    t * w⁻¹ * t⁻¹ = w⁻¹ := by
  calc t * w⁻¹ * t⁻¹ = (t * w * t⁻¹)⁻¹ := by group
    _ = w⁻¹ := by rw [h]

private lemma IsE27InvConfig.tau_inv₁ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hcfg : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    ∀ w ∈ W₁, (t₁ * t₂ * t₃) * w * (t₁ * t₂ * t₃)⁻¹ = w⁻¹ := by
  intro w hw
  have h₂ : t₂ * w * t₂⁻¹ = w := by
    rw [hcfg.comm₂ w (Subgroup.mem_sup_left hw)]
    group
  have h₃ : t₃ * w * t₃⁻¹ = w := by
    rw [hcfg.comm₃ w (Subgroup.mem_sup_left hw)]
    group
  calc (t₁ * t₂ * t₃) * w * (t₁ * t₂ * t₃)⁻¹ =
      t₁ * (t₂ * (t₃ * w * t₃⁻¹) * t₂⁻¹) * t₁⁻¹ := by group
    _ = t₁ * (t₂ * w * t₂⁻¹) * t₁⁻¹ := by rw [h₃]
    _ = t₁ * w * t₁⁻¹ := by rw [h₂]
    _ = w⁻¹ := hcfg.inv₁ w hw

private lemma IsE27InvConfig.tau_inv₂ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hcfg : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    ∀ w ∈ W₂, (t₁ * t₂ * t₃) * w * (t₁ * t₂ * t₃)⁻¹ = w⁻¹ := by
  intro w hw
  have h₁ : t₁ * w * t₁⁻¹ = w := by
    rw [hcfg.comm₁ w (Subgroup.mem_sup_left hw)]
    group
  have h₃ : t₃ * w * t₃⁻¹ = w := by
    rw [hcfg.comm₃ w (Subgroup.mem_sup_right hw)]
    group
  have h₁' : t₁ * w⁻¹ * t₁⁻¹ = w⁻¹ := conj_inv_eq_of_conj_eq h₁
  calc (t₁ * t₂ * t₃) * w * (t₁ * t₂ * t₃)⁻¹ =
      t₁ * (t₂ * (t₃ * w * t₃⁻¹) * t₂⁻¹) * t₁⁻¹ := by group
    _ = t₁ * (t₂ * w * t₂⁻¹) * t₁⁻¹ := by rw [h₃]
    _ = t₁ * w⁻¹ * t₁⁻¹ := by rw [hcfg.inv₂ w hw]
    _ = w⁻¹ := h₁'

private lemma IsE27InvConfig.tau_inv₃ {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hcfg : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) :
    ∀ w ∈ W₃, (t₁ * t₂ * t₃) * w * (t₁ * t₂ * t₃)⁻¹ = w⁻¹ := by
  intro w hw
  have h₁ : t₁ * w * t₁⁻¹ = w := by
    rw [hcfg.comm₁ w (Subgroup.mem_sup_right hw)]
    group
  have h₂ : t₂ * w * t₂⁻¹ = w := by
    rw [hcfg.comm₂ w (Subgroup.mem_sup_right hw)]
    group
  have h₁' : t₁ * w⁻¹ * t₁⁻¹ = w⁻¹ := conj_inv_eq_of_conj_eq h₁
  have h₂' : t₂ * w⁻¹ * t₂⁻¹ = w⁻¹ := conj_inv_eq_of_conj_eq h₂
  calc (t₁ * t₂ * t₃) * w * (t₁ * t₂ * t₃)⁻¹ =
      t₁ * (t₂ * (t₃ * w * t₃⁻¹) * t₂⁻¹) * t₁⁻¹ := by group
    _ = t₁ * (t₂ * w⁻¹ * t₂⁻¹) * t₁⁻¹ := by rw [hcfg.inv₃ w hw]
    _ = t₁ * w⁻¹ * t₁⁻¹ := by rw [h₂']
    _ = w⁻¹ := h₁'

private lemma inverts_of_inverts_factors {V W₁ W₂ W₃ : Subgroup G} {τ : G}
    (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hjoin : V = W₁ ⊔ W₂ ⊔ W₃)
    (hinv₁ : ∀ w ∈ W₁, τ * w * τ⁻¹ = w⁻¹)
    (hinv₂ : ∀ w ∈ W₂, τ * w * τ⁻¹ = w⁻¹)
    (hinv₃ : ∀ w ∈ W₃, τ * w * τ⁻¹ = w⁻¹) :
    ∀ v ∈ V, τ * v * τ⁻¹ = v⁻¹ := by
  have hW₁V : W₁ ≤ V := by rw [hjoin]; exact le_sup_left.trans le_sup_left
  have hW₂V : W₂ ≤ V := by rw [hjoin]; exact le_sup_right.trans le_sup_left
  have hW₃V : W₃ ≤ V := by rw [hjoin]; exact le_sup_right
  let D : Subgroup G :=
    { carrier := {x | x ∈ V ∧ τ * x * τ⁻¹ = x⁻¹}
      one_mem' := by
        refine ⟨V.one_mem, ?_⟩
        rw [mul_one, inv_one, mul_inv_cancel]
      mul_mem' := by
        rintro a b ⟨haV, ha⟩ ⟨hbV, hb⟩
        refine ⟨V.mul_mem haV hbV, ?_⟩
        calc τ * (a * b) * τ⁻¹ = (τ * a * τ⁻¹) * (τ * b * τ⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha, hb]
          _ = (a * b)⁻¹ := by
            rw [mul_inv_rev]
            exact hcomm (a⁻¹) (V.inv_mem haV) (b⁻¹) (V.inv_mem hbV)
      inv_mem' := by
        rintro a ⟨haV, ha⟩
        refine ⟨V.inv_mem haV, ?_⟩
        calc τ * a⁻¹ * τ⁻¹ = (τ * a * τ⁻¹)⁻¹ := by group
          _ = (a⁻¹)⁻¹ := by rw [ha] }
  have hW₁D : W₁ ≤ D := fun w hw => ⟨hW₁V hw, hinv₁ w hw⟩
  have hW₂D : W₂ ≤ D := fun w hw => ⟨hW₂V hw, hinv₂ w hw⟩
  have hW₃D : W₃ ≤ D := fun w hw => ⟨hW₃V hw, hinv₃ w hw⟩
  have hVD : V ≤ D := by
    rw [hjoin]
    exact sup_le (sup_le hW₁D hW₂D) hW₃D
  exact fun v hv => (hVD hv).2

theorem IsE27InvConfig.conj_mul_mul_eq_inv {V W₁ W₂ W₃ : Subgroup G} {t₁ t₂ t₃ : G}
    (hcfg : IsE27InvConfig V W₁ W₂ W₃ t₁ t₂ t₃) {v : G} (hv : v ∈ V) :
    (t₁ * t₂ * t₃) * v * (t₁ * t₂ * t₃)⁻¹ = v⁻¹ :=
  inverts_of_inverts_factors
    (fun a ha b hb => CFSG.Open.IsElemAbelian.comm hcfg.elem ha hb) hcfg.join
    hcfg.tau_inv₁ hcfg.tau_inv₂ hcfg.tau_inv₃ v hv

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
