module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMTools
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixInvertedRank
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixALeMStepZero
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixCStarLModel
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKFacts

import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTwelveQuot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyNine
import CFSG.CGT.PushingUpLit.CGT6.SixFourLTwo
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBInnerPClosure

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G} {d : ℕ}
  {L₁ L₂ L₃ : Subgroup G} {n₁ n₂ n₃ : ℕ}

theorem TwelveSixKCtx.p_eq_three_of_starImg_le_cStarL
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃)
    (hY : starImg p H D.I₁ ≤ cStarL p H ∧ starImg p H D.I₂ ≤ cStarL p H ∧
      starImg p H D.I₃ ≤ cStarL p H) : p = 3 := by
  classical
  by_contra hp3
  haveI : Fact p.Prime := ⟨hc.ctx.p_prime⟩
  have hI₁H : D.I₁ ≤ H := D.le_inf₁.trans inf_le_left
  have hI₂H : D.I₂ ≤ H := D.le_inf₂.trans inf_le_left
  have hI₃H : D.I₃ ≤ H := D.le_inf₃.trans inf_le_left
  have hVH : D.V ≤ H :=
    D.V_le.trans (sup_le (sup_le hI₁H hI₂H) hI₃H)
  have hstar_sup_le : starImg p H (D.I₁ ⊔ D.I₂ ⊔ D.I₃) ≤ cStarL p H := by
    rw [starImg]
    refine Subgroup.map_le_iff_le_comap.mpr ?_
    rw [Subgroup.subgroupOf_sup (sup_le hI₁H hI₂H) hI₃H,
      Subgroup.subgroupOf_sup hI₁H hI₂H]
    exact sup_le (sup_le (Subgroup.map_le_iff_le_comap.mp hY.1)
      (Subgroup.map_le_iff_le_comap.mp hY.2.1))
      (Subgroup.map_le_iff_le_comap.mp hY.2.2)
  have hVstar : starImg p H D.V ≤ cStarL p H :=
    (Subgroup.map_mono (Subgroup.comap_mono D.V_le)).trans hstar_sup_le
  have hdisjV : D.V ⊓ relPPrimeCore p H = ⊥ := hc.V_inf_relPPrimeCore_eq_bot D
  have hcard1 : Nat.card (starImg p H D.V) ∣ Nat.card D.V := by
    have h := Subgroup.card_map_dvd (D.V.subgroupOf H)
      (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
    have hc := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVH).toEquiv
    rw [starImg, ← hc]
    exact h
  have hcard2 : Nat.card D.V ∣ Nat.card (starImg p H D.V) := by
    have h := card_range_dvd_card_map_mul_card_starImg hc.ctx.p_prime hVH
      (MonoidHom.id ↥(D.V))
    have hmap : ((relPPrimeCore p H).subgroupOf D.V).map (MonoidHom.id ↥(D.V)) = ⊥ := by
      have hbot : (relPPrimeCore p H).subgroupOf D.V = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot]
        exact disjoint_iff.mpr (by rwa [inf_comm] at hdisjV)
      rw [hbot, Subgroup.map_bot]
    have hrange : (MonoidHom.id ↥(D.V)).range = ⊤ :=
      MonoidHom.range_eq_top.mpr Function.surjective_id
    rw [hrange, hmap] at h
    simpa using h
  have hcardV : Nat.card (starImg p H D.V) = 27 := by
    rw [Nat.dvd_antisymm hcard1 hcard2, D.cfg.card]
  have hcardVbar : Nat.card ((starImg p H D.V).subgroupOf (cStarL p H)) = 3 ^ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVstar).toEquiv, hcardV]
    norm_num
  have hElem : IsElemAbelian 3 ((starImg p H D.V).subgroupOf (cStarL p H)) :=
    (show IsElemAbelian 3 (starImg p H D.V) from
      (D.cfg.elem.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))).subgroupOf (cStarL p H)
  obtain ⟨W, hWac, hWmod, hWfin, φ, hker, hdim⟩ := hc.ctx.exists_cStarL_model
  have hinj : ((starImg p H D.V).subgroupOf (cStarL p H)) ⊓ φ.ker = ⊥ := by
    have hV3 : IsPGroup 3 ((starImg p H D.V).subgroupOf (cStarL p H)) := hElem.isPGroup
    have hPp : IsPGroup p (CFSG.pCore p ↥(cStarL p H)) :=
      CFSG.pCore_isPGroup (p := p) (G := ↥(cStarL p H))
    have hdisj : ((starImg p H D.V).subgroupOf (cStarL p H)) ⊓
        CFSG.pCore p ↥(cStarL p H) = ⊥ :=
      disjoint_iff.mp (IsPGroup.disjoint_of_ne 3 p (Ne.symm hp3) _ _ hV3 hPp)
    exact le_bot_iff.mp ((inf_le_inf_left _ hker).trans hdisj.le)
  have hτH : D.t₁ * D.t₂ * D.t₃ ∈ H :=
    H.mul_mem (H.mul_mem (D.t₁_mem hc.data).1 (D.t₂_mem hc.data).1)
      (D.t₃_mem hc.data).1
  have hτsup : D.t₁ * D.t₂ * D.t₃ ∈ D.I₁ ⊔ D.I₂ ⊔ D.I₃ :=
    (D.I₁ ⊔ D.I₂ ⊔ D.I₃).mul_mem
      ((D.I₁ ⊔ D.I₂ ⊔ D.I₃).mul_mem D.mem₁ D.mem₂) D.mem₃
  have hτY : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ⟨D.t₁ * D.t₂ * D.t₃, hτH⟩ ∈
      cStarL p H :=
    hstar_sup_le (Subgroup.mem_map.mpr
      ⟨⟨D.t₁ * D.t₂ * D.t₃, hτH⟩, Subgroup.mem_subgroupOf.mpr hτsup, rfl⟩)
  let τbar : ↥(cStarL p H) :=
    ⟨(QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) ⟨D.t₁ * D.t₂ * D.t₃, hτH⟩, hτY⟩
  have hτ : ∀ v ∈ ((starImg p H D.V).subgroupOf (cStarL p H)),
      τbar * v * τbar⁻¹ = v⁻¹ := by
    intro v hv
    have hv' : (v : StarGroup p H) ∈ starImg p H D.V := hv
    rw [starImg] at hv'
    obtain ⟨d, hdmem, hdval⟩ := Subgroup.mem_map.mp hv'
    have hdH : (d : G) ∈ H := d.2
    have hdV : (d : G) ∈ D.V := Subgroup.mem_subgroupOf.mp hdmem
    have hconj : (D.t₁ * D.t₂ * D.t₃) * (d : G) * (D.t₁ * D.t₂ * D.t₃)⁻¹ = (d : G)⁻¹ :=
      D.cfg.conj_mul_mul_eq_inv hdV
    have hsub : (⟨D.t₁ * D.t₂ * D.t₃, hτH⟩ : ↥H) * d * (⟨D.t₁ * D.t₂ * D.t₃, hτH⟩ : ↥H)⁻¹ =
        ⟨(d : G)⁻¹, H.inv_mem hdH⟩ := Subtype.ext hconj
    have hmap : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
          ⟨D.t₁ * D.t₂ * D.t₃, hτH⟩ * (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) d *
          ((QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
            ⟨D.t₁ * D.t₂ * D.t₃, hτH⟩)⁻¹ =
        ((QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) d)⁻¹ := by
      have h1 : (QuotientGroup.mk' (primeComplementCore (G := ↥H) p))
            (⟨D.t₁ * D.t₂ * D.t₃, hτH⟩ * d * (⟨D.t₁ * D.t₂ * D.t₃, hτH⟩⁻¹)) =
          (QuotientGroup.mk' (primeComplementCore (G := ↥H) p)) (d⁻¹) :=
        congrArg _ hsub
      simpa only [map_mul, map_inv] using h1
    apply Subtype.ext
    show (τbar : StarGroup p H) * (v : StarGroup p H) * (τbar : StarGroup p H)⁻¹ =
      ((v : StarGroup p H))⁻¹
    simpa [τbar, ← hdval] using hmap
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro h0
    have h0' : ((3 : ℕ) : ZMod p) = 0 := by simpa using h0
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h0'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hc.ctx.p_prime Nat.prime_three).mp hdvd)
  have h6 := two_mul_le_finrank_of_inverted (K := ZMod p) (W := W) h3 φ hElem hcardVbar
    hinj hτ
  omega

private theorem not_dvd_three_pow_sub_one {r j : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r)
    (hr13 : r ≠ 13) (hj1 : 1 ≤ j) (hj4 : j ≤ 4) : ¬ r ∣ 3 ^ j - 1 := by
  intro hdvd
  have hj0 : j ≠ 0 := by omega
  have hpos : 0 < 3 ^ j - 1 := by
    have h1 : 1 < 3 ^ j := Nat.one_lt_pow hj0 (by norm_num)
    omega
  have hmem : r ∈ (3 ^ j - 1).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hr, hdvd, hpos.ne'⟩
  have hsub : (3 ^ j - 1).primeFactors ⊆ ({2, 5, 13} : Finset ℕ) := by
    interval_cases j <;> norm_num [Nat.primeFactors]
  have hr' : r ∈ ({2, 5, 13} : Finset ℕ) := hsub hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hr'
  rcases hr' with rfl | rfl | rfl
  · omega
  · omega
  · exact absurd rfl hr13

theorem TwelveCtx.false_of_starImg_le_cStarL_of_three_le (h : TwelveCtx G M p Q H)
    (hp : p = 3) {I : Subgroup G} {n : ℕ} (hIH : I ≤ H) (hn : Odd n) (hn3 : 3 ≤ n)
    (hIt : IsPSLType 2 (GaloisField 2 n) (modTwoCore I))
    (hIY : starImg p H I ≤ cStarL p H) : False := by
  subst hp
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn2 : 2 ≤ n := by omega
  have hOle : relPPrimeCore 3 H ≤ H := relPPrimeCore_le H
  have hOnorm : ((relPPrimeCore 3 H).subgroupOf H).Normal :=
    relPPrimeCore_normal Nat.prime_three H
  have hHnorm : H ≤ Subgroup.normalizer (relPPrimeCore 3 H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hOle).mp hOnorm
  have hIN : I ≤ Subgroup.normalizer ((I ⊓ relPPrimeCore 3 H : Subgroup G) : Set G) :=
    (le_inf Subgroup.le_normalizer (hIH.trans hHnorm)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hN3 : ¬ 3 ∣ Nat.card ↥(I ⊓ relPPrimeCore 3 H) := by
    intro hdvd
    have hdvdO : 3 ∣ Nat.card (relPPrimeCore 3 H) :=
      hdvd.trans (Subgroup.card_dvd_of_le inf_le_right)
    exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
      (coprime_card_relPPrimeCore Nat.prime_three H)) hdvdO
  have hNcore : I ⊓ relPPrimeCore 3 H ≤ pCoreOf 2 I :=
    le_pCoreOf_two_of_isPSLType hn2 hIt inf_le_left hIN hN3
  let φ : ↥I →* modTwoCore I := QuotientGroup.mk' (pCore 2 ↥I)
  have hφker : ((relPPrimeCore 3 H).subgroupOf I) ≤ φ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxG : (x : G) ∈ I ⊓ relPPrimeCore 3 H :=
      ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    have hxcore : (x : G) ∈ pCoreOf 2 I := hNcore hxG
    rw [pCoreOf] at hxcore
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxcore
    have hye : y = x := Subtype.ext hyx
    have hxmem : x ∈ pCore 2 ↥I := by rw [hye] at hy; exact hy
    exact (QuotientGroup.eq_one_iff x).mpr hxmem
  have hdivStar : Nat.card (modTwoCore I) ∣ Nat.card (starImg 3 H I) := by
    have h := card_range_dvd_card_map_mul_card_starImg Nat.prime_three hIH φ
    have hmap : ((relPPrimeCore 3 H).subgroupOf I).map φ = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr hφker
    rw [QuotientGroup.range_mk', hmap] at h
    simpa using h
  obtain ⟨r, hr, hr7, hrdvd2n⟩ := exists_prime_seven_le_dvd_two_pow_sub_one hn hn3
  have hr13 : r ≠ 13 := fun h13 =>
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19.not_thirteen_dvd_two_pow_sub_one_of_odd
      hn (h13 ▸ hrdvd2n)
  have hr3 : r ≠ 3 := by omega
  have hdvdMod : r ∣ Nat.card (modTwoCore I) := by
    unfold IsPSLType at hIt
    obtain ⟨e⟩ := hIt
    have hn0 : n ≠ 0 := by omega
    have hn1 : 1 ≤ n := by omega
    have hF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn0
    have hcardPSL : Nat.card
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) =
        2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      rw [Nat.card_congr
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
          (GaloisField 2 n)).toEquiv]
      exact CFSG.CGT.PushingUpLit.CGT6.card_psl2_two_pow hn1 hF
    have hcardMod : Nat.card (modTwoCore I) = 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      (Nat.card_congr e.toEquiv).trans hcardPSL
    rw [hcardMod]
    exact dvd_mul_of_dvd_right
      (hrdvd2n.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)) (2 ^ n)
  have hdvdStar : r ∣ Nat.card (starImg 3 H I) := hdvdMod.trans hdivStar
  have hdvdY : r ∣ Nat.card ↥(cStarL 3 H) :=
    hdvdStar.trans (Subgroup.card_dvd_of_le hIY)
  obtain ⟨W, hWac, hWmod, hWfin, φY, hkerY, hdim⟩ := h.exists_cStarL_model
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' r hdvdY
  have hyker : y ∉ φY.ker := by
    intro hyk
    have hmem : y ∈ CFSG.pCore 3 ↥(cStarL 3 H) := hkerY hyk
    have hordvd : orderOf y ∣ Nat.card (CFSG.pCore 3 ↥(cStarL 3 H)) :=
      Subgroup.orderOf_dvd_natCard _ hmem
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 3) (G := ↥(cStarL 3 H))).exists_card_eq
    rw [hk, hyord] at hordvd
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
      (Nat.Prime.dvd_of_dvd_pow hr hordvd))
  have hordφ : orderOf (φY y) = r := by
    have hdvd := orderOf_map_dvd φY y
    rw [hyord] at hdvd
    have hne : orderOf (φY y) ≠ 1 := by
      intro h1
      exact hyker (MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h1))
    rcases (Nat.dvd_prime hr).mp hdvd with h1 | h1
    · exact absurd h1 hne
    · exact h1
  have hdvdUnits : r ∣ Nat.card ((Module.End (ZMod 3) W)ˣ) := by
    have h := Subgroup.orderOf_dvd_natCard (⊤ : Subgroup ((Module.End (ZMod 3) W)ˣ))
      (Subgroup.mem_top (φY y))
    simpa [hordφ] using h
  have hdvdGL : r ∣ Nat.card (W ≃ₗ[ZMod 3] W) := by
    have hcard := Nat.card_congr
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 3) W).toEquiv
    rwa [hcard] at hdvdUnits
  have hlt : 4 < Module.finrank (ZMod 3) W :=
    lt_finrank_of_dvd_card_linearEquiv (K := ZMod 3) (S := W) (r := r) (m := 4) hr
      (by
        rw [Nat.card_zmod]
        intro hdvd
        have := Nat.le_of_dvd (by norm_num) hdvd
        omega)
      (fun j hj1 hj4 => by
        simpa [Nat.card_zmod] using not_dvd_three_pow_sub_one hr hr7 hr13 hj1 hj4) hdvdGL
  omega

theorem TwelveSixKCtx.n_eq_one_of_starImg_le_cStarL
    (hc : TwelveSixKCtx G M p Q H d L₁ L₂ L₃ n₁ n₂ n₃)
    (D : TwelveSixIData H L₁ L₂ L₃ n₁ n₂ n₃) (hp : p = 3)
    (hY : starImg p H D.I₁ ≤ cStarL p H ∧ starImg p H D.I₂ ≤ cStarL p H ∧
      starImg p H D.I₃ ≤ cStarL p H) : n₁ = 1 ∧ n₂ = 1 ∧ n₃ = 1 := by
  subst hp
  have key : ∀ {I : Subgroup G} {n : ℕ}, I ≤ H → Odd n → IsPSLType 2 (GaloisField 2 n)
      (modTwoCore I) → starImg 3 H I ≤ cStarL 3 H → n = 1 := by
    intro I n hIH hn hIt hIY
    by_contra hn1
    obtain ⟨k, hk⟩ := hn
    have hnodd : Odd n := ⟨k, hk⟩
    have hn3 : 3 ≤ n := by omega
    exact hc.ctx.false_of_starImg_le_cStarL_of_three_le rfl hIH hnodd hn3 hIt hIY
  exact ⟨key (D.le_inf₁.trans inf_le_left) hc.data.odd₁ D.type₁ hY.1,
    key (D.le_inf₂.trans inf_le_left) hc.data.odd₂ D.type₂ hY.2.1,
    key (D.le_inf₃.trans inf_le_left) hc.data.odd₃ D.type₃ hY.2.2⟩

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12

end
