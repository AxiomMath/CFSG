module

public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Stage1Cls
public import CFSG.GH74.GLS.Stage2.Local.P27.Psp4Main
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.GH74.GLS.Stage2.Local.P27.L4Actual
public import CFSG.GH74.GLS.Stage2.Local.P27.L4WFacts
public import CFSG.GH74.GLS.Stage2.Local.P27.LayerAAux
public import CFSG.GH74.GLS.Stage2.Local.P27.P3L4
public import CFSG.GH74.GLS.Stage2.Local.P27.S45L4Cls

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27 CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

theorem not_mem_LC_of_swaps {z : G} {S : Subgroup G} {q : ℕ} {L₁ L₂ : Subgroup (CentralizerBar z)}
    (hP : Stage1Pair G z S q L₁ L₂) {t : G} (hsw : Swaps z t L₁ L₂) : t ∉ LC z := by
  intro htL
  obtain ⟨htC, hc1, hc2⟩ := hsw
  have hn1 : LBar z ≤ normalizer (L₁ : Set (CentralizerBar z)) := by
    rw [← hP.prod.1]
    exact sup_le Subgroup.le_normalizer
      (Psp4Stage1.le_normalizer_of_commute (fun b hb a ha => (hP.prod.2.1 a ha b hb).symm))
  have hmem : toBar z ⟨t, htC⟩ ∈ LBar z := ⟨⟨t, htC⟩, htL, rfl⟩
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hn1 ((LBar z).inv_mem hmem))
  have h2 : conjugate L₁ (toBar z ⟨t, htC⟩) = L₁ := h1
  exact hP.ne (h2.symm.trans hc1)


omit [Finite G] in
theorem swaps_mul_z {z : G} {L₁ L₂ : Subgroup (CentralizerBar z)} {t : G} (hsw : Swaps z t L₁ L₂) :
    Swaps z (z * t) L₁ L₂ := by
  obtain ⟨htC, hc1, hc2⟩ := hsw
  have hzC : z ∈ Cen z := mem_Cen_self z
  have hzt : z * t ∈ Cen z := mul_mem hzC htC
  have hcen : ∀ y : CentralizerBar z, toBar z ⟨z, hzC⟩ * y = y * toBar z ⟨z, hzC⟩ := by
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    show toBar z ⟨z, hzC⟩ * toBar z w = toBar z w * toBar z ⟨z, hzC⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 w.2).symm
  have hmul : toBar z ⟨z * t, hzt⟩ = toBar z ⟨z, hzC⟩ * toBar z ⟨t, htC⟩ := by
    rw [← map_mul]; rfl
  have hconj_eq : (MulAut.conj (toBar z ⟨z * t, hzt⟩)⁻¹).toMonoidHom =
      (MulAut.conj (toBar z ⟨t, htC⟩)⁻¹).toMonoidHom := by
    ext x
    show (toBar z ⟨z * t, hzt⟩)⁻¹ * x * ((toBar z ⟨z * t, hzt⟩)⁻¹)⁻¹ =
      (toBar z ⟨t, htC⟩)⁻¹ * x * ((toBar z ⟨t, htC⟩)⁻¹)⁻¹
    rw [inv_inv, inv_inv, hmul]
    have h1 : (toBar z ⟨z, hzC⟩)⁻¹ * x * toBar z ⟨z, hzC⟩ = x := by
      have := hcen x
      calc (toBar z ⟨z, hzC⟩)⁻¹ * x * toBar z ⟨z, hzC⟩
          = (toBar z ⟨z, hzC⟩)⁻¹ * (x * toBar z ⟨z, hzC⟩) := by group
        _ = (toBar z ⟨z, hzC⟩)⁻¹ * (toBar z ⟨z, hzC⟩ * x) := by rw [this]
        _ = x := by group
    calc (toBar z ⟨z, hzC⟩ * toBar z ⟨t, htC⟩)⁻¹ * x * (toBar z ⟨z, hzC⟩ * toBar z ⟨t, htC⟩)
        = (toBar z ⟨t, htC⟩)⁻¹ * ((toBar z ⟨z, hzC⟩)⁻¹ * x * toBar z ⟨z, hzC⟩) * toBar z ⟨t, htC⟩ := by
          group
      _ = (toBar z ⟨t, htC⟩)⁻¹ * x * toBar z ⟨t, htC⟩ := by rw [h1]
  have key : ∀ L : Subgroup (CentralizerBar z),
      conjugate L (toBar z ⟨z * t, hzt⟩) = conjugate L (toBar z ⟨t, htC⟩) := by
    intro L
    unfold conjugate
    rw [hconj_eq]
  exact ⟨hzt, (key L₁).trans hc1, (key L₂).trans hc2⟩


section Psp4

theorem pattern_psp4 {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x₀ : G} (hz : IsCentralInvolution z)
    (hS : IsSylowOf 2 S (Cen z)) (h4 : Stage1PSp4 G z S q L₁ L₂)
    (hx : TwoClassData G z S L₁ L₂ q x₀) {t' : G} (ht'S : t' ∈ S) (ht'2 : t' * t' = 1)
    (hsw : Swaps z t' L₁ L₂) :
    (IsConj z t' ∧ ¬ IsConj z (z * t')) ∨ (IsConj z (z * t') ∧ ¬ IsConj z t') := by
  obtain ⟨t₀, ht₀S, ht₀c, ht₀sw⟩ := hx.swap_exists
  obtain ⟨P₁, P₂, a, hD, hP12, -⟩ := Psp4Stage1.psp4_data_of_stage1_t hz hS h4 ht₀S ht₀c ht₀sw
  have hcls := Psp4Stage1.isConj_iff_mem_traces hz hD hP12 hx ht₀c ht₀sw
  have hA := Psp4.ps4_actual hD
  have hzS : z ∈ S := hD.z_mem
  have hxz : ¬ IsConj z x₀ := fun h => hx.x_nonCentral (isCentralInvolution_of_isConj_P27 hz h)
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have ht'R : t' ∉ P₁ ⊔ P₂ := by
    rw [hP12]
    exact fun h => not_mem_LC_of_swaps h4.pair hsw h.2
  have hzR : z ∈ P₁ ⊔ P₂ := Subgroup.mem_sup_left hD.z_mem₁
  have ht'1 : t' ≠ 1 := fun h => ht'R (h ▸ one_mem _)
  have ht'z : t' ≠ z := fun h => ht'R (h ▸ hzR)
  have hzt' : z * t' = t' * z := hD.z_cent' ht'S
  have hzt'S : z * t' ∈ S := S.mul_mem hzS ht'S
  have hzt'2 : (z * t') * (z * t') = 1 := by
    calc (z * t') * (z * t') = z * (t' * z) * t' := by group
      _ = z * (z * t') * t' := by rw [hzt']
      _ = (z * z) * (t' * t') := by group
      _ = 1 := by rw [hzz, ht'2, one_mul]
  have hzt'1 : z * t' ≠ 1 := by
    intro h
    apply ht'z
    have := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hzz
  have hRS := hD.R_le_S
  have hzt₀ : z * t₀ = t₀ * z := hD.z_cent' ht₀S
  have hc1 := hcls t' ht'S ht'2 ht'1
  have hc2 := hcls (z * t') hzt'S hzt'2 hzt'1
  rcases (hA.partition t' ht'S ht'2 ht'1).1 with hZ | hX
  ·
    rcases hZ with hzeq | ⟨r, hr, hreq⟩
    · exact absurd (Set.mem_singleton_iff.1 hzeq) ht'z
    · left
      have hzr : z * r = r * z := hD.z_cent' (hRS hr)
      have hmem : z * t' ∈ Psp4.Xc (P₁ ⊔ P₂) z t₀ := by
        refine Or.inr ⟨r, hr, ?_⟩
        rw [hreq]
        calc z * (r * t₀ * r⁻¹) = (z * r) * t₀ * r⁻¹ := by group
          _ = r * (z * t₀) * r⁻¹ := by rw [hzr]; group
          _ = r * (t₀ * z) * r⁻¹ := by rw [hzt₀]
      refine ⟨hc1.1.2 (Or.inr ⟨r, hr, hreq⟩), fun hcz => hxz ?_⟩
      exact hcz.trans (hc2.2.2 hmem).symm
  ·
    rcases hX with ⟨hR, -⟩ | ⟨r, hr, hreq⟩
    · exact absurd hR ht'R
    · right
      have hzr : z * r = r * z := hD.z_cent' (hRS hr)
      have hmem : z * t' ∈ Psp4.Zc (P₁ ⊔ P₂) z t₀ := by
        refine Or.inr ⟨r, hr, ?_⟩
        rw [hreq]
        calc z * (r * (t₀ * z) * r⁻¹) = (z * r) * (t₀ * z) * r⁻¹ := by group
          _ = r * (z * (t₀ * z)) * r⁻¹ := by rw [hzr]; group
          _ = r * ((z * t₀) * z) * r⁻¹ := by group
          _ = r * ((t₀ * z) * z) * r⁻¹ := by rw [hzt₀]
          _ = r * t₀ * r⁻¹ := by rw [mul_assoc t₀ z z, hzz, mul_one]
      refine ⟨hc2.1.2 hmem, fun hcz => hxz ?_⟩
      exact hcz.trans (hc1.2.2 (Or.inr ⟨r, hr, hreq⟩)).symm

end Psp4


section L4

theorem pattern_l4 {z : G} {S : Subgroup G} {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} {x₀ : G} (hz : IsCentralInvolution z)
    (hS : IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂)
    (hidx : (RC S z).relIndex S ≤ 4) (hx : TwoClassData G z S L₁ L₂ q x₀)
    (hfield : ∃ t ∈ S, IsConj z t ∧ Swaps z t L₁ L₂ ∧
      ∃ w ∈ S, orderOf w = 2 ∧ t * w = w * t ∧ w ∉ RC S z ⊔ zpowers t ∧
        GoodInvolution z S L₁ L₂ q w ∧ IsConj z w ∧ IsConj z (t * w) ∧ IsConj x₀ (t * w * z) ∧
        ∀ y ∈ S, y * y = 1 → y ≠ 1 → (∃ r ∈ RC S z, y = r * w) → IsConj z y)
    {t' : G} (ht'S : t' ∈ S) (ht'2 : t' * t' = 1) (hsw : Swaps z t' L₁ L₂) :
    (IsConj z t' ∧ ¬ IsConj z (z * t')) ∨ (IsConj z (z * t') ∧ ¬ IsConj z t') := by
  obtain ⟨t, htS, htc, hswt, w, hwS, hwo, htw, hwRt, hgood, hwz, htwz, htwx, hcos⟩ := hfield
  obtain ⟨P₁, P₂, a, hPD, hP12, -, -, hcard, hP₁eq, -⟩ :=
    Psp4Stage1.pair_data_of_stage1_t hz hS hP htS htc hswt
  have hSC : S ≤ Cen z := Psp4Stage1.S_le_Cen hS
  have hw2 : w * w = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo, pow_two] at this
  have hwR : w ∉ RC S z := fun h => hwRt (Subgroup.mem_sup_left h)
  have htR : t ∉ RC S z := by
    rw [← hP12]
    exact hPD.t_not
  have hnorm := RC_conj_mem hSC
  obtain ⟨hidx4, hRinf, hSeq⟩ := P27.S45.l4_S_structure (inf_le_left : RC S z ≤ S) hnorm htS hwS
    hPD.t_inv hw2 htw htR hwRt hidx
  have hidx4' : (RC S z).relIndex S = 4 := hidx4
  obtain ⟨hwnorm, hwdih⟩ := P27.l4_w_facts hz hS hP hP₁eq hcard hgood hwR
  have d : P27.L4.DataL4 S P₁ P₂ z t w a :=
    ⟨hPD.z_mem, hPD.z_ord, hPD.z_cent, hPD.P₁_le, hPD.P₂_le, hPD.P₁_quat, hPD.P₂_quat, hPD.inter,
      hPD.comm, hPD.t_mem, hPD.t_inv, hPD.swap, hwS, hw2, htw, by rw [hP12]; exact hidx4,
      by rw [hP12]; exact hRinf, by rw [hP12]; exact hSeq, hwnorm, hwdih⟩
  have hA := P27.L4.l4_actual d
  have hcls := P27.S45.isConj_iff_mem_traces_l4 hz d hP12 hx htc hswt hwz htwz htwx hcos hA.partition
  have hzS : z ∈ S := hPD.z_mem
  have hxz : ¬ IsConj z x₀ := fun h => hx.x_nonCentral (isCentralInvolution_of_isConj_P27 hz h)
  have hzz : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz.1, pow_two] at this
  have ht'R : t' ∉ P₁ ⊔ P₂ := by
    rw [hP12]
    exact fun h => not_mem_LC_of_swaps hP hsw h.2
  have hzP₁ : z ∈ P₁ := by
    have : z ∈ P₁ ⊓ P₂ := hPD.inter ▸ Subgroup.mem_zpowers z
    exact this.1
  have hzR : z ∈ P₁ ⊔ P₂ := Subgroup.mem_sup_left hzP₁
  have ht'1 : t' ≠ 1 := fun h => ht'R (h ▸ one_mem _)
  have ht'z : t' ≠ z := fun h => ht'R (h ▸ hzR)
  have hzt' : z * t' = t' * z := (hPD.z_cent _ ht'S).symm
  have hzt'S : z * t' ∈ S := S.mul_mem hzS ht'S
  have hzt'2 : (z * t') * (z * t') = 1 := by
    calc (z * t') * (z * t') = z * (t' * z) * t' := by group
      _ = z * (z * t') * t' := by rw [hzt']
      _ = (z * z) * (t' * t') := by group
      _ = 1 := by rw [hzz, ht'2, one_mul]
  have hzt'1 : z * t' ≠ 1 := by
    intro h
    apply ht'z
    have := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact inv_eq_of_mul_eq_one_right hzz
  have hRS : P₁ ⊔ P₂ ≤ S := sup_le hPD.P₁_le hPD.P₂_le
  have hzt₀ : z * t = t * z := (hPD.z_cent _ htS).symm
  have hzw : z * w = w * z := (hPD.z_cent _ hwS).symm
  have hc1 := hcls t' ht'S ht'2 ht'1
  have hc2 := hcls (z * t') hzt'S hzt'2 hzt'1
  rcases (hA.partition t' ht'S ht'2 ht'1).1 with hZ | hX
  · rcases hZ with (hZ | hC) | hD
    · rcases hZ with hzeq | ⟨r, hr, hreq⟩
      · exact absurd (Set.mem_singleton_iff.1 hzeq) ht'z
      · left
        have hzr : z * r = r * z := (hPD.z_cent _ (hRS hr)).symm
        have hmem : z * t' ∈ P27.L4.XcL (P₁ ⊔ P₂) z t w := by
          refine Or.inl (Or.inr ⟨r, hr, ?_⟩)
          rw [hreq]
          calc z * (r * t * r⁻¹) = (z * r) * t * r⁻¹ := by group
            _ = r * (z * t) * r⁻¹ := by rw [hzr]; group
            _ = r * (t * z) * r⁻¹ := by rw [hzt₀]
        exact ⟨hc1.1.2 (Or.inl (Or.inl (Or.inr ⟨r, hr, hreq⟩))),
          fun hcz => hxz (hcz.trans (hc2.2.2 hmem).symm)⟩
    ·
      exfalso
      obtain ⟨⟨r, hr, hreq⟩, -⟩ := hC
      have hzr : z * r ∈ P₁ ⊔ P₂ := (P₁ ⊔ P₂).mul_mem hzR hr
      have hzt'C : z * t' ∈ P27.L4.ZcL (P₁ ⊔ P₂) z t w := by
        refine Or.inl (Or.inr ⟨⟨z * r, hzr, ?_⟩, hzt'2⟩)
        rw [hreq]; group
      have hc1' : IsConj z t' := hc1.1.2 (Or.inl (Or.inr ⟨⟨r, hr, hreq⟩, ht'2⟩))
      have hx1 := (hx.swap_conseq t' ht'S hc1' hsw).1
      have hzx : IsConj z (z * t') := hc2.1.2 hzt'C
      rw [← hzt'] at hx1
      exact hxz (hzx.trans hx1.symm)
    ·
      obtain ⟨r, hr, hreq⟩ := hD
      left
      have hzr : z * r = r * z := (hPD.z_cent _ (hRS hr)).symm
      have hztw : z * (t * w) = t * w * z := by
        calc z * (t * w) = (z * t) * w := by group
          _ = (t * z) * w := by rw [hzt₀]
          _ = t * (z * w) := by group
          _ = t * (w * z) := by rw [hzw]
          _ = t * w * z := by group
      have hmem : z * t' ∈ P27.L4.XcL (P₁ ⊔ P₂) z t w := by
        refine Or.inr ⟨r, hr, ?_⟩
        rw [hreq]
        calc z * (r * (t * w) * r⁻¹) = (z * r) * (t * w) * r⁻¹ := by group
          _ = r * (z * (t * w)) * r⁻¹ := by rw [hzr]; group
          _ = r * (t * w * z) * r⁻¹ := by rw [hztw]
      exact ⟨hc1.1.2 (Or.inr ⟨r, hr, hreq⟩), fun hcz => hxz (hcz.trans (hc2.2.2 hmem).symm)⟩
  · rcases hX with (hE | hF) | hG
    · obtain ⟨hR, -⟩ := hE
      exact absurd hR ht'R
    · obtain ⟨r, hr, hreq⟩ := hF
      right
      have hzr : z * r = r * z := (hPD.z_cent _ (hRS hr)).symm
      have hmem : z * t' ∈ P27.L4.ZcL (P₁ ⊔ P₂) z t w := by
        refine Or.inl (Or.inl (Or.inr ⟨r, hr, ?_⟩))
        rw [hreq]
        calc z * (r * (t * z) * r⁻¹) = (z * r) * (t * z) * r⁻¹ := by group
          _ = r * (z * (t * z)) * r⁻¹ := by rw [hzr]; group
          _ = r * ((z * t) * z) * r⁻¹ := by group
          _ = r * ((t * z) * z) * r⁻¹ := by rw [hzt₀]
          _ = r * t * r⁻¹ := by rw [mul_assoc t z z, hzz, mul_one]
      exact ⟨hc2.1.2 hmem, fun hcz => hxz (hcz.trans (hc1.2.2 (Or.inl (Or.inr ⟨r, hr, hreq⟩))).symm)⟩
    · obtain ⟨r, hr, hreq⟩ := hG
      right
      have hzr : z * r = r * z := (hPD.z_cent _ (hRS hr)).symm
      have hmem : z * t' ∈ P27.L4.ZcL (P₁ ⊔ P₂) z t w := by
        refine Or.inr ⟨r, hr, ?_⟩
        rw [hreq]
        calc z * (r * (t * w * z) * r⁻¹) = (z * r) * (t * w * z) * r⁻¹ := by group
          _ = r * (z * (t * w * z)) * r⁻¹ := by rw [hzr]; group
          _ = r * (z * (t * w) * z) * r⁻¹ := by group
          _ = r * ((t * w * z) * z) * r⁻¹ := by
            rw [show z * (t * w) = t * w * z by
              calc z * (t * w) = (z * t) * w := by group
                _ = (t * z) * w := by rw [hzt₀]
                _ = t * (z * w) := by group
                _ = t * (w * z) := by rw [hzw]
                _ = t * w * z := by group]
          _ = r * (t * w) * r⁻¹ := by rw [mul_assoc (t * w) z z, hzz, mul_one]
      exact ⟨hc2.1.2 hmem, fun hcz => hxz (hcz.trans (hc1.2.2 (Or.inr ⟨r, hr, hreq⟩)).symm)⟩

end L4

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
