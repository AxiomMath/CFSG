module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoModelB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4RealStd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSylowPosition
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBFix
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoModelBBase

public section

namespace CFSG.ComponentClassification.GrSLit.GrS5S

open CFSG Subgroup CFSG.ComponentClassification CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit.L34Facts.Real
  CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso CFSG.LieType.Multipliers.L34
  CFSG.CosetTable

variable {G : Type} [Group G] [Finite G]

theorem length_le_card {H : Subgroup G} {l : List G} (hl : l.Nodup) (hH : ∀ x ∈ l, x ∈ H) :
    l.length ≤ Nat.card H := by
  classical
  rw [← List.toFinset_card_of_nodup hl, ← Set.ncard_coe_finset,
    show Nat.card H = (H : Set G).ncard from Nat.card_coe_set_eq _]
  exact Set.ncard_le_ncard (fun x hx => hH x (by simpa using hx)) (Set.toFinite _)

theorem mem_of_card_four {H : Subgroup G} (h4 : Nat.card H = 4) {a b c d w : G} (ha : a ∈ H)
    (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) (hw : w ∈ H) : w = a ∨ w = b ∨ w = c ∨ w = d := by
  by_contra hne
  push Not at hne
  obtain ⟨hwa, hwb, hwc, hwd⟩ := hne
  have := length_le_card (H := H) (l := [a, b, c, d, w])
    (by simp [hab, hac, had, hbc, hbd, hcd, hwa.symm, hwb.symm, hwc.symm, hwd.symm])
    (by simp [ha, hb, hc, hd, hw])
  simp at this
  omega

variable {J S : Subgroup G} {hSN : S ≤ normalizer (J : Set G)}

variable (J S hSN) in
structure WStd where
  q : Jhat J →* Equiv.Perm (Fin 42)
  l : Cover →* Jhat J
  hQ : IsQSetting q l
  hT0 : ∀ e, q e ∈ T0 ↔ ∃ p ∈ S ⊓ J, ∃ hp : p ∈ J, jq J ⟨p, hp⟩ = e
  ψ : ↥S →* Equiv.Perm (Fin 42)
  hψR : ∀ h, ψ h ∈ PSL3Four.R
  hψ : ∀ (h : ↥S) e, q (betaHat J (hSN h.2) e) = (ψ h)⁻¹ * q e * ψ h
  kb : List Bool
  hkbL : kb ∈ kbList
  hkb : ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true


theorem exists_wStd (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hT : IsSylowTwoIn (S ⊓ J) J)
    (hSN : S ≤ normalizer (J : Set G)) : Nonempty (WStd J S hSN) := by
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT0⟩ := exists_sylow_standard hJ hL hT
  obtain ⟨ψ, hψR, hψ⟩ := GrS4.exists_realization_hom hSN hqS hqsurj hqker
  obtain ⟨kb, hkbL, hkb⟩ := exists_kb l
  exact ⟨⟨q, l, ⟨hqS, hqsurj, hqker, h3, hl, hls⟩, hT0, ψ, hψR, hψ, kb, hkbL, hkb⟩⟩

namespace WStd

omit [Finite G]
  in
theorem mem_normalizer_P (hN : S ≤ normalizer (J : Set G)) {s : G} (hs : s ∈ S) :
    s ∈ normalizer ((S ⊓ J : Subgroup G) : Set G) :=
  GrS4.inf_mem_normalizer (le_normalizer hs) (hN hs)

omit [Finite G] in
theorem ψ_eq_q (D : WStd J S hSN) {p : G} (hpS : p ∈ S) (hpJ : p ∈ J) :
    D.ψ ⟨p, hpS⟩ = D.q (jq J ⟨p, hpJ⟩) :=
  GrS4.realization_eq_of_mem hSN D.hQ.qS D.hQ.qsurj D.hψR D.hψ ⟨p, hpS⟩ hpJ

omit [Finite G] in
theorem ψ_mem_S (D : WStd J S hSN) {w : G} (hw : w ∈ S) (hwK : w ∈ withKernel J) :
    D.ψ ⟨w, hw⟩ ∈ PSL3Four.S := by
  have h := GrS4.realization_mem_S_of_mem_withKernel (hSN hw) hwK D.hQ.qS D.hQ.qsurj
    (PSL3Four.R.inv_mem (D.hψR ⟨w, hw⟩)) fun e => by rw [D.hψ ⟨w, hw⟩ e, inv_inv]
  exact (inv_mem_iff).mp h

omit [Finite G] in
theorem ψ_mem_T0 (D : WStd J S hSN) (hS2 : IsPGroup 2 S) {w : G} (hw : w ∈ S)
    (hwK : w ∈ withKernel J) : D.ψ ⟨w, hw⟩ ∈ T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set g := D.ψ ⟨w, hw⟩ with hg
  have hgS : g ∈ PSL3Four.S := D.ψ_mem_S hw hwK
  have hgN : zpowers g ≤ normalizer (T0 : Set (Equiv.Perm (Fin 42))) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro u
    constructor
    · exact GrS4.mul_inv_mem_T0_of_realization hSN D.hQ.qsurj D.hT0 D.hψ ⟨w, hw⟩
        (mem_normalizer_P hSN hw) u
    · intro hu
      have h1 := GrS4.inv_mul_mem_T0_of_realization hSN D.hQ.qsurj D.hT0 D.hψ ⟨w, hw⟩
        (mem_normalizer_P hSN hw) _ hu
      have e1 : (D.ψ ⟨w, hw⟩)⁻¹ * (g * u * g⁻¹) * D.ψ ⟨w, hw⟩ = u := by rw [hg]; group
      rwa [e1] at h1
  have hrange : IsPGroup 2 D.ψ.range :=
    hS2.of_surjective D.ψ.rangeRestrict D.ψ.rangeRestrict_surjective
  have hZ2 : IsPGroup 2 (zpowers g) := hrange.to_le (zpowers_le.mpr ⟨⟨w, hw⟩, rfl⟩)
  have hT2 : IsPGroup 2 T0 := IsPGroup.of_card (n := 6) (by rw [card_T0]; norm_num)
  have hH2 := hT2.to_sup_of_normal_left' hZ2 hgN
  have hHS : T0 ⊔ zpowers g ≤ PSL3Four.S := sup_le T0_le_S (zpowers_le.mpr hgS)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hH2
  have hdvd : 2 ^ n ∣ 20160 := by
    rw [← hn, ← PSL3Four.card_S]
    exact Subgroup.card_dvd_of_le hHS
  have hn6 : n ≤ 6 := by
    by_contra hlt
    push Not at hlt
    have h7 : 2 ^ 7 ∣ 20160 := (Nat.pow_dvd_pow 2 hlt).trans hdvd
    norm_num at h7
  have hle : Nat.card ↥(T0 ⊔ zpowers g) ≤ Nat.card T0 := by
    rw [hn, card_T0]
    calc 2 ^ n ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hn6
      _ = 64 := by norm_num
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : T0 ≤ T0 ⊔ zpowers g) hle
  rw [heq]
  exact mem_sup_right (mem_zpowers g)

omit [Finite G] in
theorem ψ_eq_one_iff (D : WStd J S hSN) (hJ : ⁅J, J⁆ = J) {w : G} (hw : w ∈ S) :
    D.ψ ⟨w, hw⟩ = 1 ↔ w ∈ coreActionKernel J := by
  constructor
  · intro h1
    refine GrS4.mem_coreActionKernel_of_realization_eq_one hJ (hSN hw) D.hQ.ker fun e => ?_
    rw [D.hψ ⟨w, hw⟩ e, h1, inv_one, one_mul, mul_one]
  · intro hwC
    have h := GrS4.realization_eq_one_of_mem hwC D.hQ.qsurj
      (PSL3Four.R.inv_mem (D.hψR ⟨w, hw⟩)) fun e => by
        rw [show betaHat J (mem_coreActionKernel.mp hwC).1 e = betaHat J (hSN hw) e from rfl,
          D.hψ ⟨w, hw⟩ e, inv_inv]
    rwa [inv_eq_one] at h

omit [Finite G]
  in
theorem betaHat_eq (D : WStd J S hSN) (hJ : ⁅J, J⁆ = J) {w : G} (hw : w ∈ S) {ĵ : Jhat J}
    (hj : D.q ĵ = D.ψ ⟨w, hw⟩) (e : Jhat J) : betaHat J (hSN hw) e = ĵ⁻¹ * e * ĵ := by
  have hext : (betaHat J (hSN hw)).toMonoidHom = (MulAut.conj ĵ⁻¹).toMonoidHom := by
    apply hom_ext_of_central (commutator_jhat hJ) D.q (D.hQ.ker ▸ le_refl _)
    refine MonoidHom.ext fun e => ?_
    show D.q (betaHat J (hSN hw) e) = D.q (MulAut.conj ĵ⁻¹ e)
    rw [MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv, D.hψ ⟨w, hw⟩ e, hj]
  have h := DFunLike.congr_fun hext e
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at h
  exact h

omit [Finite G] in
theorem model
    (D : WStd J S hSN) {s : G} (hs : s ∈ S) :
    ∃ t < 64, ∃ i < 36, (D.ψ ⟨s, hs⟩)⁻¹ = yPerm t i ∧ liftsKB D.kb i = true ∧
      ∀ x : MElt, x.1 < 64 → betaHat J (hSN hs) (nfM D.l x) = nfM D.l (betaYM t i x) := by
  have hyR : (D.ψ ⟨s, hs⟩)⁻¹ ∈ PSL3Four.R := PSL3Four.R.inv_mem (D.hψR _)
  have hyN : ∀ u ∈ T0, (D.ψ ⟨s, hs⟩)⁻¹ * u * ((D.ψ ⟨s, hs⟩)⁻¹)⁻¹ ∈ T0 := fun u hu => by
    rw [inv_inv]
    exact GrS4.inv_mul_mem_T0_of_realization hSN D.hQ.qsurj D.hT0 D.hψ ⟨s, hs⟩
      (mem_normalizer_P hSN hs) u hu
  have hβ : ∀ e, D.q (betaHat J (hSN hs) e) =
      (D.ψ ⟨s, hs⟩)⁻¹ * D.q e * ((D.ψ ⟨s, hs⟩)⁻¹)⁻¹ := fun e => by
    rw [inv_inv]
    exact D.hψ ⟨s, hs⟩ e
  obtain ⟨i, hi, t, ht, hy, hβr⟩ := exists_betaRep D.hQ hyR hyN hβ
  obtain ⟨β', hβ'⟩ := lift_of_betaRep hβr
  exact ⟨t, ht, i, hi, hy, liftsKB_of D.hQ D.hkb hi hβ',
    fun x hx => betaY_nfM D.hQ ht hi hβr hx⟩

omit [Finite G] in
theorem outer_spec (D : WStd J S hSN) (hJ : ⁅J, J⁆ = J)
    {s : G} (hs : s ∈ S) (hs2 : s * s = 1) (hsK : s ∉ withKernel J) {t i : ℕ}
    (hi : i < 36) (hy : (D.ψ ⟨s, hs⟩)⁻¹ = yPerm t i) :
    repInS.contains i = false ∧ yPerm t i * yPerm t i = 1 := by
  refine ⟨?_, ?_⟩
  · cases hc : repInS.contains i
    · rfl
    · exfalso
      apply hsK
      refine GrS4.mem_withKernel_of_realization_mem_S hJ hSN D.hQ.qsurj D.hQ.ker D.hψ ⟨s, hs⟩ ?_
      have hyS : yPerm t i ∈ PSL3Four.S :=
        PSL3Four.S.mul_mem (wordPerm_mem _) (repPerm_mem_S hi hc)
      rw [← hy] at hyS
      exact (inv_mem_iff).mp hyS
  · rw [← hy, ← mul_inv_rev, ← map_mul]
    have : (⟨s, hs⟩ : ↥S) * ⟨s, hs⟩ = 1 := Subtype.ext hs2
    rw [this, map_one, inv_one]

omit [Finite G] in
theorem mem_outerInvs (D : WStd J S hSN) (hJ : ⁅J, J⁆ = J)
    {s : G} (hs : s ∈ S) (hs2 : s * s = 1) (hsK : s ∉ withKernel J) {t i : ℕ} (ht : t < 64)
    (hi : i < 36) (hy : (D.ψ ⟨s, hs⟩)⁻¹ = yPerm t i) : (t, i) ∈ outerInvs := by
  obtain ⟨hc, h2⟩ := D.outer_spec hJ hs hs2 hsK hi hy
  exact mem_outerInvs_of ht hi hc (sq_yTab_of hi h2)

theorem exists_of_model
    (D : WStd J S hSN) (hJ : ⁅J, J⁆ = J) (hS2 : IsPGroup 2 S) {E₁ : Subgroup G}
    (hE₁ : E₁ ≤ S) {k : ℕ} (hk : k < 64)
    (hψE₁ : ∀ w (hw : w ∈ E₁), D.ψ ⟨w, hE₁ hw⟩ = 1 ∨ D.ψ ⟨w, hE₁ hw⟩ = wordPerm (tg k))
    {f : G} (hf : f ∈ S) {t i : ℕ} (ht : t < 64) (hi : i < 36)
    (hβ : ∀ x : MElt, x.1 < 64 → betaHat J (hSN hf) (nfM D.l x) = nfM D.l (betaYM t i x))
    {x : MElt} (hx : x ∈ fixInvs D.kb t i)
    (hxk : eqKB D.kb (mulM x (k, 0, 0)) (mulM (k, 0, 0) x) = true) :
    ∃ p, ∃ hpS : p ∈ S, ∃ hpJ : p ∈ J, p * p = 1 ∧ p ≠ 1 ∧
      (∀ g ∈ E₁ ⊔ zpowers f, p * g = g * p) ∧ D.ψ ⟨p, hpS⟩ = wordPerm (tg x.1) ∧
      jq J ⟨p, hpJ⟩ = nfM D.l x := by
  obtain ⟨hxM, hfix, hinv⟩ := mem_fixInvs.mp hx
  have hx64 : x.1 < 64 := lt_of_mem_allM hxM
  have hP2 : IsPGroup 2 (S ⊓ J : Subgroup G) := hS2.to_le inf_le_left
  have hPJ : S ⊓ J ≤ J := inf_le_right
  obtain ⟨p, hpP, hpJ, hpe⟩ :=
    (D.hT0 (nfM D.l x)).1 (by rw [q_nfM D.hQ hx64]; exact tg_mem_T0 _ hx64)
  have hpS : p ∈ S := (mem_inf.mp hpP).1
  obtain ⟨hx2, hx1⟩ := (isInvKB_iff D.hQ D.hkb hx64).1 hinv
  have hp2 : p * p = 1 := by
    refine eq_one_of_jq_eq_one hPJ hP2 (mul_mem hpP hpP) ?_
    rw [show (⟨p * p, hPJ (mul_mem hpP hpP)⟩ : ↥J) = ⟨p, hpJ⟩ * ⟨p, hpJ⟩ from rfl, map_mul, hpe,
      hx2]
  have hp1 : p ≠ 1 := by
    rintro rfl
    apply hx1
    rw [← hpe]
    exact map_one (jq J)
  have hfp : f⁻¹ * p * f = p := by
    rw [GrS4.conj_eq_iff_betaHat hPJ hP2 (hSN hf) (mem_normalizer_P hSN hf) hpP, hpe, hβ x hx64]
    exact (eqKB_iff D.hQ D.hkb (betaYM_lt ht hi hx64) hx64).1 hfix
  have hwp : ∀ w (hw : w ∈ E₁), w⁻¹ * p * w = p := by
    intro w hw
    rcases hψE₁ w hw with h1 | h1
    · have hwC := (D.ψ_eq_one_iff hJ (hE₁ hw)).1 h1
      have hc := GrS4.mul_comm_of_mem_coreActionKernel hS2 (hE₁ hw) hwC hpS hpJ
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    · have hk0 : (k, (0 : ZMod 4), (0 : ZMod 4)).1 < 64 := hk
      have hj : D.q (nfM D.l (k, 0, 0)) = D.ψ ⟨w, hE₁ hw⟩ := by rw [q_nfM D.hQ hk0, h1]
      rw [GrS4.conj_eq_iff_betaHat hPJ hP2 (hSN (hE₁ hw)) (mem_normalizer_P hSN (hE₁ hw)) hpP, hpe,
        D.betaHat_eq hJ (hE₁ hw) hj]
      have hc := (commKB_iff D.hQ D.hkb hx64 hk0).1 hxk
      rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcent : E₁ ⊔ zpowers f ≤ centralizer ({p} : Set G) := by
    refine sup_le (fun w hw => mem_centralizer_singleton_iff.mpr ?_) (zpowers_le.mpr ?_)
    · have := hwp w hw
      calc w * p = w * (w⁻¹ * p * w) := by rw [this]
        _ = p * w := by group
    · rw [mem_centralizer_singleton_iff]
      calc f * p = f * (f⁻¹ * p * f) := by rw [hfp]
        _ = p * f := by group
  refine ⟨p, hpS, hpJ, hp2, hp1, fun g hg => (mem_centralizer_singleton_iff.mp (hcent hg)).symm, ?_,
    hpe⟩
  rw [D.ψ_eq_q hpS hpJ, hpe, q_nfM D.hQ hx64]

end WStd

end CFSG.ComponentClassification.GrSLit.GrS5S
