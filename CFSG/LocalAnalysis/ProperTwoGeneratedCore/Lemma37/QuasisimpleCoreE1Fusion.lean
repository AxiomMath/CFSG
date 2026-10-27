module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1FusionBasic
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Classes
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsCosets

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem e1PQ_of_e1U_true : ∀ v : Fin 64, e1U true v → c3Mul v v = 0 → v ≠ 0 →
    e1Gen true true v = false → e1PQ v := by decide

theorem e1PQ_or_e1E_of_even : ∀ v : Fin 64, v.val % 2 = 0 → c3Mul v v = 0 → v ≠ 0 →
    ¬ c3GenW v → e1PQ v ∨ (e1E v ∧ v ≠ 40) := by decide

theorem e1_typeD_labels : e1Gen true true 2 = false ∧ e1Gen true true (c3Mul 2 40) = false ∧
    e1Gen true true 1 = true ∧ e1Gen true true 3 = true ∧ c3Mul 2 2 = 0 := by decide

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem map_le_centralizer_forty : (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) ≤
    Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} := by
  intro s hs
  obtain ⟨v, rfl⟩ := d.caseC3BCD.exists_caseC3Word hs
  rw [Subgroup.mem_centralizer_singleton_iff, d.caseC3BCD.caseC3Word_mul,
    d.caseC3BCD.caseC3Word_mul, c3Mul_forty_comm]

theorem not_genuine_self : ¬ CaseC3.Genuine (Subgroup.center J) (u : J ⧸ Subgroup.center J) := by
  rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x)]
  exact d.not_genuine_of_e1PQ (by decide)

theorem not_isConj_forty_self :
    ¬ IsConj (caseC3Word (Subgroup.center J) u m y x 40) (u : J ⧸ Subgroup.center J) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have h' := CaseC3.genuine_conj _ d.caseC3BCD.genuine_forty c⁻¹
  rw [inv_inv, hc] at h'
  exact d.not_genuine_self h'

variable (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
  s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
    CaseC3.Genuine (Subgroup.center J) s)
include htype

theorem isConj_two : IsConj (u : J ⧸ Subgroup.center J) (y : J ⧸ Subgroup.center J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := d.caseC3BCD
  have hperf := d.setting.perfect
  have hperf' : commutator (J ⧸ Subgroup.center J) = ⊤ := Group.isPerfect_def.mp inferInstance
  set S'' := S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))
  have hS'' : (S'' : Subgroup (J ⧸ Subgroup.center J)) =
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) := Sylow.coe_mapSurjective _ _
  have hy : (y : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 2 :=
    CaseC3BCD.caseC3Word_two.symm
  have hyy : (y : J ⧸ Subgroup.center J) * (y : J ⧸ Subgroup.center J) = 1 := by
    rw [hy, hb.caseC3Word_mul, e1_typeD_labels.2.2.2.2, CaseC3BCD.caseC3Word_zero]
  obtain ⟨g, hg⟩ := Lemma37.exists_conj_mem_of_relIndex_eq_two hperf' S''
    (hS'' ▸ hb.e1UBar_le true) (by rw [hS'']; exact hb.relIndex_e1UBar true)
    (show orderOf (y : J ⧸ Subgroup.center J) = 2 by
      rw [hy]; exact hb.orderOf_caseC3Word e1_typeD_labels.2.2.2.2 (by decide))
  obtain ⟨v, hv, hvg⟩ := hb.mem_e1UBar_iff.mp hg
  have hvv : c3Mul v v = 0 := by
    rw [← hb.caseC3Word_mul_self_eq_one_iff, hvg,
      show g⁻¹ * (y : J ⧸ Subgroup.center J) * g * (g⁻¹ * (y : J ⧸ Subgroup.center J) * g) =
        g⁻¹ * ((y : J ⧸ Subgroup.center J) * (y : J ⧸ Subgroup.center J)) * g by group, hyy]
    group
  have hv0 : v ≠ 0 := fun h0 => by
    rw [h0, CaseC3BCD.caseC3Word_zero] at hvg
    have h1 : (y : J ⧸ Subgroup.center J) = 1 := by
      rw [show (y : J ⧸ Subgroup.center J) = g * (g⁻¹ * (y : J ⧸ Subgroup.center J) * g) * g⁻¹ by
        group, ← hvg]
      group
    rw [hy, hb.caseC3Word_eq_one_iff] at h1
    exact absurd h1 (by decide)
  have hgen : e1Gen true true v = false := by
    rw [← Bool.not_eq_true, ← hb.genuine_iff_of_typeD htype, hvg]
    intro h'
    have h'' := CaseC3.genuine_conj _ h' g⁻¹
    rw [inv_inv, show g * (g⁻¹ * (y : J ⧸ Subgroup.center J) * g) * g⁻¹ = y by group, hy,
      hb.genuine_iff_of_typeD htype, e1_typeD_labels.1] at h''
    exact Bool.false_ne_true h''
  obtain ⟨h, -, hh⟩ := d.exists_conj_self_of_e1PQ (H := ⊤) le_top le_top
    (e1PQ_of_e1U_true v hv hvv hv0 hgen)
  refine isConj_iff.mpr ⟨g * h, ?_⟩
  rw [show g * h * (u : J ⧸ Subgroup.center J) * (g * h)⁻¹ =
    g * (h * (u : J ⧸ Subgroup.center J) * h⁻¹) * g⁻¹ by group, hh, hvg]
  group

theorem exists_centralizer_conj_two :
    ∃ h ∈ Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40},
      h * (u : J ⧸ Subgroup.center J) * h⁻¹ = (y : J ⧸ Subgroup.center J) := by
  have hb := d.caseC3BCD
  have hy : (y : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 2 :=
    CaseC3BCD.caseC3Word_two.symm
  refine d.exists_mem_centralizer_conj_eq (d.isConj_two htype) ?_ ?_
  · rw [hy]
    change _ * _ = _ * _
    rw [hb.caseC3Word_mul, hb.caseC3Word_mul, c3Mul_forty_comm]
  · rw [hy, hb.caseC3Word_mul, hb.genuine_iff_of_typeD htype, e1_typeD_labels.2.1]
    exact Bool.false_ne_true

theorem exists_conj_self_of_e1E {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHz : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ≤ H) {v : Fin 64}
    (hv : e1E v) (hv0 : v ≠ 0) (hv40 : v ≠ 40) : ∃ h ∈ H, h * (u : J ⧸ Subgroup.center J) * h⁻¹ =
      caseC3Word (Subgroup.center J) u m y x v := by
  have hb := d.caseC3BCD
  have hSH := d.map_le_centralizer_forty.trans hHz
  rcases hb.exists_conj_of_mem_e1EBar (hb.caseC3Word_mem_e1EBar_iff.mpr hv)
      (by rw [Ne, hb.caseC3Word_eq_one_iff]; exact hv0)
      (by rw [Ne, hb.caseC3Word_inj]; exact hv40) with ⟨s, hs, hsv⟩ | ⟨s, hs, hsv⟩
  · exact ⟨s, hSH hs, hsv⟩
  · obtain ⟨h₀, hh₀, hh₀u⟩ := d.exists_centralizer_conj_two htype
    refine ⟨s * h₀, H.mul_mem (hSH hs) (hHz hh₀), ?_⟩
    rw [show s * h₀ * (u : J ⧸ Subgroup.center J) * (s * h₀)⁻¹ =
      s * (h₀ * (u : J ⧸ Subgroup.center J) * h₀⁻¹) * s⁻¹ by group, hh₀u, hsv]

theorem exists_conj_forty_of_outer {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHz : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ≤ H)
    (hHu : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≤ H) {v : Fin 64}
    (hv : v.val % 2 = 1) (hvv : c3Mul v v = 0) :
    ∃ h ∈ H, h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹ =
      caseC3Word (Subgroup.center J) u m y x v := by
  have hb := d.caseC3BCD
  have hSH := d.map_le_centralizer_forty.trans hHz
  obtain ⟨h₀, hh₀, hh₀u⟩ := d.exists_centralizer_conj_two htype
  have hy : (y : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 2 :=
    CaseC3BCD.caseC3Word_two.symm
  have hrep : ∀ r : Fin 64, (r = 1 ∨ r = 3) → ∃ h ∈ H,
      h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹ =
        caseC3Word (Subgroup.center J) u m y x r := by
    intro r hr
    have hr2 : c3Mul r 2 = c3Mul 2 r := by
      rcases hr with rfl | rfl
      exacts [e1_fusion_words.1, e1_fusion_words.2.1]
    have hrr : c3Mul r r = 0 := by rcases hr with rfl | rfl <;> decide
    have hr0 : r ≠ 0 := by rcases hr with rfl | rfl <;> decide
    have hgen : CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x r) := by
      rw [hb.genuine_iff_of_typeD htype]
      rcases hr with rfl | rfl
      exacts [e1_typeD_labels.2.2.1, e1_typeD_labels.2.2.2.1]
    set w := caseC3Word (Subgroup.center J) u m y x r with hw
    have hcomm : w * (y : J ⧸ Subgroup.center J) = (y : J ⧸ Subgroup.center J) * w := by
      rw [hy, hw, hb.caseC3Word_mul, hb.caseC3Word_mul, hr2]
    have hww : w * w = 1 := by
      rw [hw, hb.caseC3Word_mul, hrr, CaseC3BCD.caseC3Word_zero]
    have hw1 : w ≠ 1 := by rw [hw, Ne, hb.caseC3Word_eq_one_iff]; exact hr0
    obtain ⟨h, hh, hhw⟩ := d.exists_conj_forty_of_mem_centralizer hHu hSH
      (w := h₀⁻¹ * w * h₀) (Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc h₀⁻¹ * w * h₀ * (u : J ⧸ Subgroup.center J) =
              h₀⁻¹ * (w * (h₀ * (u : J ⧸ Subgroup.center J) * h₀⁻¹)) * h₀ := by group
          _ = h₀⁻¹ * ((h₀ * (u : J ⧸ Subgroup.center J) * h₀⁻¹) * w) * h₀ := by rw [hh₀u, hcomm]
          _ = (u : J ⧸ Subgroup.center J) * (h₀⁻¹ * w * h₀) := by group))
      (by rw [show h₀⁻¹ * w * h₀ * (h₀⁻¹ * w * h₀) = h₀⁻¹ * (w * w) * h₀ by group, hww]; group)
      (fun h1 => hw1 (by rw [show w = h₀ * (h₀⁻¹ * w * h₀) * h₀⁻¹ by group, h1]; group))
      (CaseC3.genuine_conj _ hgen h₀)
    refine ⟨h₀ * h, H.mul_mem (hHz hh₀) hh, ?_⟩
    rw [show h₀ * h * caseC3Word (Subgroup.center J) u m y x 40 * (h₀ * h)⁻¹ =
      h₀ * (h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹) * h₀⁻¹ by group, hhw]
    group
  obtain ⟨w, -, hw⟩ := c3_outer_conj v hv hvv
  obtain ⟨h, hh, hhr⟩ := hrep (e1OuterRep v) (by unfold e1OuterRep; split_ifs <;> simp)
  refine ⟨caseC3Word (Subgroup.center J) u m y x w * h,
    H.mul_mem (hSH (hb.caseC3Word_mem w)) hh, ?_⟩
  rw [show caseC3Word (Subgroup.center J) u m y x w * h *
      caseC3Word (Subgroup.center J) u m y x 40 * (caseC3Word (Subgroup.center J) u m y x w * h)⁻¹ =
        caseC3Word (Subgroup.center J) u m y x w *
          (h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹) *
            (caseC3Word (Subgroup.center J) u m y x w)⁻¹ by group, hhr, hb.caseC3Word_conj, hw]

theorem exists_conj_of_typeD {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHz : Subgroup.centralizer {caseC3Word (Subgroup.center J) u m y x 40} ≤ H)
    (hHu : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≤ H) {v : Fin 64}
    (hvv : c3Mul v v = 0) (hv0 : v ≠ 0) :
    (CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x v) →
      ∃ h ∈ H, h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹ =
        caseC3Word (Subgroup.center J) u m y x v) ∧
    (¬ CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x v) →
      ∃ h ∈ H, h * (u : J ⧸ Subgroup.center J) * h⁻¹ =
        caseC3Word (Subgroup.center J) u m y x v) := by
  have hb := d.caseC3BCD
  have hSH := d.map_le_centralizer_forty.trans hHz
  rcases Nat.mod_two_eq_zero_or_one v.val with hv2 | hv2
  · rw [hb.genuine_even_iff hv2]
    refine ⟨fun hg => d.exists_conj_forty_of_c3GenW hHu hSH (hg.resolve_left hv0), fun hg => ?_⟩
    push Not at hg
    rcases e1PQ_or_e1E_of_even v hv2 hvv hv0 hg.2 with h | ⟨h, h40⟩
    · exact d.exists_conj_self_of_e1PQ hHu hSH h
    · exact d.exists_conj_self_of_e1E htype hHz h hv0 h40
  · refine ⟨fun _ => d.exists_conj_forty_of_outer htype hHz hHu hv2 hvv, fun hg => absurd ?_ hg⟩
    exact htype _ (hb.caseC3Word_mem v) (hb.caseC3Word_not_mem_bot hv2)
      (hb.caseC3Word_mul_self_eq_one_iff.mpr hvv)

omit htype in
theorem exists_conj_caseC3Word {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHS : (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) ≤ H)
    {t : J ⧸ Subgroup.center J} (htH : t ∈ H) (htt : t * t = 1) (ht1 : t ≠ 1) :
    ∃ k ∈ H, ∃ v : Fin 64, c3Mul v v = 0 ∧ v ≠ 0 ∧
      k * t * k⁻¹ = caseC3Word (Subgroup.center J) u m y x v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := d.caseC3BCD
  set S'' := S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))
  have hS'' : (S'' : Subgroup (J ⧸ Subgroup.center J)) =
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) := Sylow.coe_mapSurjective _ _
  have hp : IsPGroup 2 (Subgroup.zpowers t) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (show t ^ 2 ^ 1 = 1 by rw [pow_one, pow_two, htt]))
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨k, hk, hkt⟩ := exists_conj_mem_sylow_of_le S'' (hS''.symm ▸ hHS)
    (Subgroup.zpowers_le.mpr htH) hp
  have hmem := hkt t (Subgroup.mem_zpowers t)
  rw [hS''] at hmem
  obtain ⟨v, hv⟩ := hb.exists_caseC3Word hmem
  refine ⟨k, hk, v, ?_, fun h0 => ht1 ?_, hv.symm⟩
  · rw [← hb.caseC3Word_mul_self_eq_one_iff, hv,
      show k * t * k⁻¹ * (k * t * k⁻¹) = k * (t * t) * k⁻¹ by group, htt]
    group
  · rw [h0, CaseC3BCD.caseC3Word_zero] at hv
    rw [show t = k⁻¹ * (k * t * k⁻¹) * k by group, ← hv]
    group

theorem isConj_forty_of_genuine {t : J ⧸ Subgroup.center J} (htt : t * t = 1) (ht1 : t ≠ 1)
    (hgen : CaseC3.Genuine (Subgroup.center J) t) :
    IsConj (caseC3Word (Subgroup.center J) u m y x 40) t := by
  obtain ⟨k, -, v, hvv, hv0, hkt⟩ := d.exists_conj_caseC3Word le_top (Subgroup.mem_top t) htt ht1
  obtain ⟨h, -, hh⟩ := (d.exists_conj_of_typeD htype (H := ⊤) le_top le_top hvv hv0).1 (by
    rw [← hkt]
    have h' := CaseC3.genuine_conj _ hgen k⁻¹
    rwa [inv_inv] at h')
  refine isConj_iff.mpr ⟨k⁻¹ * h, ?_⟩
  rw [show k⁻¹ * h * caseC3Word (Subgroup.center J) u m y x 40 * (k⁻¹ * h)⁻¹ =
    k⁻¹ * (h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹) * k by group, hh, ← hkt]
  group

theorem isConj_self_of_not_genuine {t : J ⧸ Subgroup.center J} (htt : t * t = 1) (ht1 : t ≠ 1)
    (hgen : ¬ CaseC3.Genuine (Subgroup.center J) t) :
    IsConj (u : J ⧸ Subgroup.center J) t := by
  obtain ⟨k, -, v, hvv, hv0, hkt⟩ := d.exists_conj_caseC3Word le_top (Subgroup.mem_top t) htt ht1
  obtain ⟨h, -, hh⟩ := (d.exists_conj_of_typeD htype (H := ⊤) le_top le_top hvv hv0).2 (by
    rw [← hkt]
    intro h'
    have h'' := CaseC3.genuine_conj _ h' k
    exact hgen (by rwa [show k⁻¹ * (k * t * k⁻¹) * k = t by group] at h''))
  refine isConj_iff.mpr ⟨k⁻¹ * h, ?_⟩
  rw [show k⁻¹ * h * (u : J ⧸ Subgroup.center J) * (k⁻¹ * h)⁻¹ =
    k⁻¹ * (h * (u : J ⧸ Subgroup.center J) * h⁻¹) * k by group, hh, ← hkt]
  group

theorem isConj_forty_iff {t : J ⧸ Subgroup.center J} (htt : t * t = 1) (ht1 : t ≠ 1) :
    IsConj (caseC3Word (Subgroup.center J) u m y x 40) t ↔
      CaseC3.Genuine (Subgroup.center J) t := by
  refine ⟨fun h => ?_, d.isConj_forty_of_genuine htype htt ht1⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have h' := CaseC3.genuine_conj _ d.caseC3BCD.genuine_forty c⁻¹
  rwa [inv_inv, hc] at h'

theorem isConj_self_iff {t : J ⧸ Subgroup.center J} (htt : t * t = 1) (ht1 : t ≠ 1) :
    IsConj (u : J ⧸ Subgroup.center J) t ↔ ¬ CaseC3.Genuine (Subgroup.center J) t := by
  refine ⟨fun h hg => d.not_genuine_self ?_, d.isConj_self_of_not_genuine htype htt ht1⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have h' := CaseC3.genuine_conj _ hg c
  rwa [← hc, show c⁻¹ * (c * (u : J ⧸ Subgroup.center J) * c⁻¹) * c = u by group] at h'

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
