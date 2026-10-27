module

import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNFGroup
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataAt

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.PreuniquenessRankFour.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataAt.exists_lift_central (hd : D1CaseTwoDataAt p P M H R Rbar)
    {N : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hNR : N ≤ (Rbar : Subgroup _))
    (hNn : (Rbar : Subgroup _) ≤
      Subgroup.normalizer (N : Set (H ⧸ primeComplementCore (G := H) p)))
    (hN1 : N ≠ ⊥) :
    ∃ t : H, (t : G) ∈ R ∧ orderOf (t : G) = p ∧ (∀ g ∈ R, g * (t : G) = (t : G) * g) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) t ∈ N := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set Rb := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) with hRb
  set N' : Subgroup Rb := N.subgroupOf Rb with hN'
  have : N'.Normal := by
    refine ⟨fun a ha g => ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hNn g.2) a).mp ha
  have hN'1 : N' ≠ ⊥ := by
    intro h
    apply hN1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNR hx⟩ : Rb) ∈ N' := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)
  have : Group.IsNilpotent Rb := Rbar.isPGroup'.isNilpotent
  have hZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'1
  have hpg : IsPGroup p (N' ⊓ Subgroup.center Rb : Subgroup Rb) :=
    Rbar.isPGroup'.to_subgroup _
  obtain ⟨c, hcmem, hcp, -⟩ := exists_mem_centralizer_orderOf_eq hpg hZ
  have hcR : (c : H ⧸ primeComplementCore (G := H) p) ∈ (Rbar : Subgroup _) := c.2
  rw [hd.cfg.rbar] at hcR
  obtain ⟨r, hrR, hrc⟩ := hcR
  have hO := primeComplementCore_coprime (G := H) p
  have hRO : ∀ s : H, (s : G) ∈ R → s ∈ primeComplementCore (G := H) p → s = 1 := by
    intro s hs hsO
    obtain ⟨k, hk⟩ := hd.cfg.ext.isPGroup ⟨s, hs⟩
    have h1 : orderOf s ∣ p ^ k := by
      apply orderOf_dvd_of_pow_eq_one
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : orderOf s ∣ Nat.card (primeComplementCore (G := H) p) :=
      Subgroup.orderOf_dvd_natCard _ hsO
    have h3 : orderOf s = 1 :=
      Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.coprime_dvd_right h2 hO).symm.pow_right k) h1
    exact orderOf_eq_one_iff.mp h3
  have hrR' : ((r : H) : G) ∈ R := hrR
  have hc1 : (c : H ⧸ primeComplementCore (G := H) p) ≠ 1 := by
    intro h
    have : orderOf (c : H ⧸ primeComplementCore (G := H) p) = p := by
      rw [Subgroup.orderOf_coe, hcp]
    rw [h, orderOf_one] at this
    exact hp.one_lt.ne this
  have hro : orderOf ((r : H) : G) = p := by
    rw [Subgroup.orderOf_coe]
    apply orderOf_eq_prime
    · apply hRO
      · rw [Subgroup.coe_pow]
        exact R.pow_mem hrR' p
      · rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow,
          show QuotientGroup.mk' (primeComplementCore (G := H) p) (r : H) = c from hrc]
        have : orderOf (c : H ⧸ primeComplementCore (G := H) p) = p := by
          rw [Subgroup.orderOf_coe, hcp]
        exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq this)
    · intro h
      apply hc1
      rw [← hrc]
      show QuotientGroup.mk' _ (r : H) = 1
      rw [h, map_one]
  have hRr : ∀ s ∈ R, s * ((r : H) : G) = ((r : H) : G) * s := by
    intro s hs
    have hsH : s ∈ H := hd.cfg.ext.le_H hs
    have hsc : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨s, hsH⟩ * c =
        c * QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨s, hsH⟩ := by
      have hsR : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨s, hsH⟩ ∈
          (Rbar : Subgroup _) := by
        rw [hd.cfg.rbar]
        exact ⟨⟨s, hsH⟩, hs, rfl⟩
      have := Subgroup.mem_center_iff.mp hcmem.2 ⟨_, hsR⟩
      exact congrArg Subtype.val this
    rw [← hrc] at hsc
    have hcomm : (⟨s, hsH⟩ : H) * r * (⟨s, hsH⟩ : H)⁻¹ * (r : H)⁻¹ = 1 := by
      apply hRO
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact R.mul_mem (R.mul_mem (R.mul_mem hs hrR') (R.inv_mem hs)) (R.inv_mem hrR')
      · rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply]
        simp only [map_mul, map_inv]
        rw [hsc]
        group
    have := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at this
    calc s * (r : G) = s * r * s⁻¹ * (r : G)⁻¹ * (r * s) := by group
      _ = r * s := by rw [this, one_mul]
  refine ⟨r, hrR', hro, hRr, ?_⟩
  rw [hrc]
  exact hcmem.1

theorem D1CaseTwoDataAt.mem_component_twoA (hd : D1CaseTwoDataAt p P M H R Rbar)
    {L L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hL₂ : IsComponentOf L₂ ⊤) (hLL₂ : L ≠ L₂) {z : H} (hzR : (z : G) ∈ R)
    (hzo : orderOf (z : G) = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)))
    {w : G} (hwo : orderOf w = p) (hRw : ∀ g ∈ R, g * w = w * g)
    (hΩ : ∀ g ∈ R, (∀ y ∈ R, y * g = g * y) → g ^ p = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G)) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈ L₂ := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  have hRbN : ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      (Rbar : Subgroup _) ≤ Subgroup.normalizer
        ((((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
          Subgroup (H ⧸ primeComplementCore (G := H) p))) :
            Set (H ⧸ primeComplementCore (G := H) p)) := by
    intro K hK r hr
    have hrN := hd.cfg.red.sylow_le_normalizer_component hK hr
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxR, hxL⟩
      exact ⟨(Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)).mul_mem
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)).mul_mem hr hxR)
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)).inv_mem hr),
        (Subgroup.mem_normalizer_iff.mp hrN x).mp hxL⟩
    · rintro ⟨hxR, hxL⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp hrN x).mpr hxL⟩
      have := (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)).mul_mem
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)).mul_mem
        ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)).inv_mem hr) hxR) hr
      have e : r⁻¹ * (r * x * r⁻¹) * r = x := by group
      rw [e] at this
      exact this
  have hne : ∀ K : Subgroup (H ⧸ primeComplementCore (G := H) p), IsComponentOf K ⊤ →
      ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K :
        Subgroup (H ⧸ primeComplementCore (G := H) p)) ≠ ⊥ := by
    intro K hK hbot
    obtain ⟨t, htRL, htp, -⟩ := exists_mem_sylow_inf_component hp hd.cfg.red.ne_two
      hd.cfg.red.core_eq_bot Rbar hK
    rw [hbot, Subgroup.mem_bot] at htRL
    rw [htRL, orderOf_one] at htp
    exact hp.one_lt.ne htp
  obtain ⟨t₁, ht₁R, ht₁o, ht₁c, ht₁L⟩ := D1CaseTwoDataAt.exists_lift_central hd inf_le_left
    (hRbN L hL) (hne L hL)
  obtain ⟨t₂, ht₂R, ht₂o, ht₂c, ht₂L⟩ := D1CaseTwoDataAt.exists_lift_central hd inf_le_left
    (hRbN L₂ hL₂) (hne L₂ hL₂)
  by_contra hz2
  have hzt₂ : (z : G) ∉ Subgroup.zpowers (t₂ : G) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    apply hz2
    have : z = t₂ ^ k := Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
    rw [this, map_zpow]
    exact Subgroup.zpow_mem _ ht₂L.2 k
  set D : Subgroup G := ((Subgroup.centralizer (L : Set _)).comap π).map H.subtype with hD
  have hZL := hd.cfg.red.center_eq_bot_of_isCyclic hL (hd.cyclic L hL)
  have ht₂D : (t₂ : G) ∈ D := ⟨t₂, le_centralizer_of_component_ne hL₂ hL (Ne.symm hLL₂) ht₂L.2,
    rfl⟩
  have hzD : (z : G) ∈ D := ⟨z, hzL, rfl⟩
  have ht₁D : (t₁ : G) ∉ D := by
    rintro ⟨t, htC, htt⟩
    have htt' : t = t₁ := Subtype.ext htt
    rw [htt'] at htC
    have hcen : (⟨π t₁, ht₁L.2⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp htC g g.2)
    rw [hZL, Subgroup.mem_bot] at hcen
    have h1 : π t₁ = 1 := congrArg Subtype.val hcen
    have h2 := (mk'_primeComplementCore_eq_one_iff p t₁).mp h1
    have h3 : orderOf (t₁ : G) ∣ Nat.card (GLBPrimeCore p H) := by
      have := Subgroup.orderOf_dvd_natCard (GLBPrimeCore p H) h2
      exact this
    rw [ht₁o] at h3
    exact (Nat.Prime.coprime_iff_not_dvd hp).mp (glbPrimeCore_coprime p H) h3
  have hcomm : ∀ a b : G, a * b = b * a →
      Subgroup.zpowers a ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    intro a b hab
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (show Commute b a from hab.symm) n)).eq
  have hc1 := card_sup_zpowers hp le_rfl hzo hzt₂ (hcomm _ _ (ht₂c _ hzR).symm)
  rw [Nat.card_zpowers, ht₂o] at hc1
  have hA2D : Subgroup.zpowers (t₂ : G) ⊔ Subgroup.zpowers (z : G) ≤ D :=
    sup_le ((Subgroup.zpowers_le).mpr ht₂D) ((Subgroup.zpowers_le).mpr hzD)
  have hA2c : Subgroup.zpowers (t₂ : G) ⊔ Subgroup.zpowers (z : G) ≤
      Subgroup.centralizer (Subgroup.zpowers (t₁ : G) : Set G) :=
    sup_le (hcomm _ _ (ht₁c _ ht₂R)) (hcomm _ _ (ht₁c _ hzR))
  have hc2 := card_sup_zpowers hp hA2D ht₁o ht₁D hA2c
  rw [hc1] at hc2
  have hle : Subgroup.zpowers (t₂ : G) ⊔ Subgroup.zpowers (z : G) ⊔
      Subgroup.zpowers (t₁ : G) ≤ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G) := by
    have hp₁ : (t₁ : G) ^ p = 1 := by rw [← ht₁o]; exact pow_orderOf_eq_one _
    have hp₂ : (t₂ : G) ^ p = 1 := by rw [← ht₂o]; exact pow_orderOf_eq_one _
    refine sup_le (sup_le ((Subgroup.zpowers_le).mpr (hΩ _ ht₂R ht₂c hp₂))
      le_sup_right) ((Subgroup.zpowers_le).mpr (hΩ _ ht₁R ht₁c hp₁))
  have hc3 := card_sup_zpowers_le hwo hzo (hRw _ hzR).symm
  have h4 := Subgroup.card_le_of_le hle
  rw [hc2] at h4
  have h5 : p * p * p ≤ p * p := h4.trans hc3
  have h6 : 0 < p * p := Nat.mul_pos hp.pos hp.pos
  nlinarith [hp.two_le]

theorem D1CaseTwoData.mem_component_twoA (hd : D1CaseTwoData p P M H R Rbar)
    {L L₂ : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hL₂ : IsComponentOf L₂ ⊤) (hLL₂ : L ≠ L₂) {z : H} (hzR : (z : G) ∈ R)
    (hzo : orderOf (z : G) = p)
    (hzL : QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈
      Subgroup.centralizer (L : Set (H ⧸ primeComplementCore (G := H) p)))
    {w : G} (hwo : orderOf w = p) (hRw : ∀ g ∈ R, g * w = w * g)
    (hΩ : ∀ g ∈ R, (∀ y ∈ R, y * g = g * y) → g ^ p = 1 →
      g ∈ Subgroup.zpowers w ⊔ Subgroup.zpowers (z : G)) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) z ∈ L₂ :=
  D1CaseTwoDataAt.mem_component_twoA (hd := hd.toAt) (hL := hL) (hL₂ := hL₂) (hLL₂ := hLL₂)
    (hzR := hzR) (hzo := hzo) (hzL := hzL) (hwo := hwo) (hRw := hRw) (hΩ := hΩ)

end CFSG.AGLEmbedding
