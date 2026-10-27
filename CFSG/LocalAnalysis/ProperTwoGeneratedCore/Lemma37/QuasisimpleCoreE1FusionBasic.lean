module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentUPhiU
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC2Inv

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem e1_genW_split : ∀ v : Fin 64, c3GenW v →
    e1PQ ⟨v.val % 16, by omega⟩ ∧ c3Mul ⟨v.val % 16, by omega⟩ v = c3Mul v ⟨v.val % 16, by omega⟩ ∧
      e1PQ (c3Mul ⟨v.val % 16, by omega⟩ v) := by decide

theorem e1PQ_swap : ∀ v : Fin 64, e1PQ v → v.val < 16 ∨
    ((c3Conj 1 v).val < 16 ∧ e1PQ (c3Conj 1 v) ∧ c3Conj 1 (c3Conj 1 v) = v) := by decide

theorem e1PQ_left : ∀ q : Fin 64, e1PQ q → q.val < 16 → c3GenW (c3Mul 32 q) ∧
    c3Mul 32 (c3Mul 32 q) = q ∧ c3Mul (c3Mul 32 q) 32 = c3Mul 32 (c3Mul 32 q) := by decide

theorem e1_fusion_words : c3Mul 1 2 = c3Mul 2 1 ∧ c3Mul 3 2 = c3Mul 2 3 ∧ c3Conj 1 32 = 8 ∧
    c3Mul 32 40 = 8 := by decide

theorem ne_zero_of_c3GenW : ∀ v : Fin 64, c3GenW v → v ≠ 0 := by decide

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

theorem conj_self_of_mem_centralizer_singleton {G : Type*} [Group G] {g c : G}
    (hc : c ∈ Subgroup.centralizer {g}) : c * g * c⁻¹ = g := by
  rw [Subgroup.mem_centralizer_singleton_iff.mp hc, mul_inv_cancel_right]

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem not_genuine_of_e1PQ {v : Fin 64} (hv : e1PQ v) :
    ¬ CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x v) := by
  obtain ⟨h4, h0, hG⟩ := hv
  rw [d.caseC3BCD.genuine_even_iff (by omega)]
  rintro (h | h)
  exacts [h0 h, hG h]

theorem exists_conj_eight_of_e1PQ {q : Fin 64} (hq : e1PQ q) (hq16 : q.val < 16) :
    ∃ c ∈ Subgroup.centralizer {(u : J ⧸ Subgroup.center J)},
      c * caseC3Word (Subgroup.center J) u m y x q * c⁻¹ =
        caseC3Word (Subgroup.center J) u m y x 8 := by
  have hb := d.caseC3BCD
  obtain ⟨hgen, hq', hcomm⟩ := e1PQ_left q hq hq16
  have hu : (u : J ⧸ Subgroup.center J) = caseC3Word (Subgroup.center J) u m y x 32 :=
    CaseC3BCD.caseC3Word_thirtytwo.symm
  have huw : (u : J ⧸ Subgroup.center J) * caseC3Word (Subgroup.center J) u m y x (c3Mul 32 q) =
      caseC3Word (Subgroup.center J) u m y x q := by
    rw [hu, hb.caseC3Word_mul, hq']
  have hwu : Commute (caseC3Word (Subgroup.center J) u m y x (c3Mul 32 q))
      (u : J ⧸ Subgroup.center J) := by
    rw [hu]
    change _ * _ = _ * _
    rw [hb.caseC3Word_mul, hb.caseC3Word_mul, hcomm]
  have hw1 : caseC3Word (Subgroup.center J) u m y x (c3Mul 32 q) ≠ 1 := by
    rw [Ne, hb.caseC3Word_eq_one_iff]
    exact ne_zero_of_c3GenW _ hgen
  obtain ⟨c, hc, hcw⟩ := d.exists_conj_eq_forty hwu (hb.genuine_of_c3GenW hgen) hw1
    (by rw [huw]; exact d.not_genuine_of_e1PQ hq)
  refine ⟨c, hc, ?_⟩
  calc c * caseC3Word (Subgroup.center J) u m y x q * c⁻¹ =
        (c * (u : J ⧸ Subgroup.center J) * c⁻¹) *
          (c * caseC3Word (Subgroup.center J) u m y x (c3Mul 32 q) * c⁻¹) := by
          rw [← huw]; group
    _ = caseC3Word (Subgroup.center J) u m y x 8 := by
          rw [conj_self_of_mem_centralizer_singleton hc, hcw, hu, hb.caseC3Word_mul,
            e1_fusion_words.2.2.2]

theorem exists_conj_self_of_e1PQ {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHu : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≤ H)
    (hHS : (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) ≤ H) {v : Fin 64}
    (hv : e1PQ v) : ∃ h ∈ H, h * (u : J ⧸ Subgroup.center J) * h⁻¹ =
      caseC3Word (Subgroup.center J) u m y x v := by
  have hb := d.caseC3BCD
  have hx : caseC3Word (Subgroup.center J) u m y x 1 ∈ H := hHS (hb.caseC3Word_mem 1)
  have hleft : ∀ q, e1PQ q → q.val < 16 → ∃ h ∈ H, h * (u : J ⧸ Subgroup.center J) * h⁻¹ =
      caseC3Word (Subgroup.center J) u m y x q := by
    intro q hq hq16
    obtain ⟨c, hc, hcq⟩ := d.exists_conj_eight_of_e1PQ hq hq16
    refine ⟨c⁻¹ * caseC3Word (Subgroup.center J) u m y x 1, H.mul_mem (H.inv_mem (hHu hc)) hx, ?_⟩
    have h8 : caseC3Word (Subgroup.center J) u m y x 1 * (u : J ⧸ Subgroup.center J) *
        (caseC3Word (Subgroup.center J) u m y x 1)⁻¹ =
          caseC3Word (Subgroup.center J) u m y x 8 := by
      rw [← CaseC3BCD.caseC3Word_thirtytwo (Z := Subgroup.center J) (m := m) (y := y) (x := x),
        hb.caseC3Word_conj, e1_fusion_words.2.2.1]
    calc c⁻¹ * caseC3Word (Subgroup.center J) u m y x 1 * (u : J ⧸ Subgroup.center J) *
          (c⁻¹ * caseC3Word (Subgroup.center J) u m y x 1)⁻¹ =
        c⁻¹ * (caseC3Word (Subgroup.center J) u m y x 1 * (u : J ⧸ Subgroup.center J) *
          (caseC3Word (Subgroup.center J) u m y x 1)⁻¹) * c := by group
      _ = c⁻¹ * (c * caseC3Word (Subgroup.center J) u m y x q * c⁻¹) * c := by rw [h8, hcq]
      _ = caseC3Word (Subgroup.center J) u m y x q := by group
  rcases e1PQ_swap v hv with h16 | ⟨h16, hv', hvv⟩
  · exact hleft v hv h16
  · obtain ⟨h, hh, hhv⟩ := hleft _ hv' h16
    refine ⟨caseC3Word (Subgroup.center J) u m y x 1 * h, H.mul_mem hx hh, ?_⟩
    calc caseC3Word (Subgroup.center J) u m y x 1 * h * (u : J ⧸ Subgroup.center J) *
          (caseC3Word (Subgroup.center J) u m y x 1 * h)⁻¹ =
        caseC3Word (Subgroup.center J) u m y x 1 * (h * (u : J ⧸ Subgroup.center J) * h⁻¹) *
          (caseC3Word (Subgroup.center J) u m y x 1)⁻¹ := by group
      _ = caseC3Word (Subgroup.center J) u m y x v := by rw [hhv, hb.caseC3Word_conj, hvv]

theorem exists_conj_forty_of_commute {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHu : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≤ H) {n w : J ⧸ Subgroup.center J}
    (hn : ∃ h ∈ H, h * (u : J ⧸ Subgroup.center J) * h⁻¹ = n) (hwn : Commute w n)
    (hw : CaseC3.Genuine (Subgroup.center J) w) (hw1 : w ≠ 1)
    (hnw : ¬ CaseC3.Genuine (Subgroup.center J) (n * w)) :
    ∃ h ∈ H, h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹ = w := by
  obtain ⟨h, hh, rfl⟩ := hn
  have hw₁u : Commute (h⁻¹ * w * h) (u : J ⧸ Subgroup.center J) := by
    change _ * _ = _ * _
    calc h⁻¹ * w * h * (u : J ⧸ Subgroup.center J) =
          h⁻¹ * (w * (h * (u : J ⧸ Subgroup.center J) * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * (u : J ⧸ Subgroup.center J) * h⁻¹) * w) * h := by rw [hwn.eq]
      _ = (u : J ⧸ Subgroup.center J) * (h⁻¹ * w * h) := by group
  have hw₁1 : h⁻¹ * w * h ≠ 1 := fun h1 => hw1 (by
    rw [show w = h * (h⁻¹ * w * h) * h⁻¹ by group, h1]; group)
  have hw₁' : ¬ CaseC3.Genuine (Subgroup.center J) ((u : J ⧸ Subgroup.center J) * (h⁻¹ * w * h)) :=
    fun hg => hnw (by
      have h' := CaseC3.genuine_conj _ hg h⁻¹
      rwa [inv_inv, show h * ((u : J ⧸ Subgroup.center J) * (h⁻¹ * w * h)) * h⁻¹ =
        h * (u : J ⧸ Subgroup.center J) * h⁻¹ * w by group] at h')
  obtain ⟨c, hc, hcw⟩ := d.exists_conj_eq_forty hw₁u (CaseC3.genuine_conj _ hw h) hw₁1 hw₁'
  refine ⟨h * c⁻¹, H.mul_mem hh (H.inv_mem (hHu hc)), ?_⟩
  rw [← hcw]
  group

theorem exists_conj_forty_of_c3GenW {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHu : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≤ H)
    (hHS : (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) ≤ H) {v : Fin 64}
    (hv : c3GenW v) : ∃ h ∈ H, h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹ =
      caseC3Word (Subgroup.center J) u m y x v := by
  have hb := d.caseC3BCD
  obtain ⟨hq, hcomm, hp⟩ := e1_genW_split v hv
  refine d.exists_conj_forty_of_commute hHu (d.exists_conj_self_of_e1PQ hHu hHS hq) ?_
    (hb.genuine_of_c3GenW hv) ?_ ?_
  · change _ * _ = _ * _
    rw [hb.caseC3Word_mul, hb.caseC3Word_mul, hcomm]
  · rw [Ne, hb.caseC3Word_eq_one_iff]
    exact ne_zero_of_c3GenW v hv
  · rw [hb.caseC3Word_mul]
    exact d.not_genuine_of_e1PQ hp

theorem exists_conj_forty_of_mem_centralizer {H : Subgroup (J ⧸ Subgroup.center J)}
    (hHu : Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} ≤ H)
    (hHS : (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) ≤ H)
    {w : J ⧸ Subgroup.center J} (hwu : w ∈ Subgroup.centralizer {(u : J ⧸ Subgroup.center J)})
    (hww : w * w = 1) (hw1 : w ≠ 1) (hw : CaseC3.Genuine (Subgroup.center J) w) :
    ∃ h ∈ H, h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹ = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := d.caseC3BCD
  set C := Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} with hC
  set w' : C := ⟨w, hwu⟩
  have hp : IsPGroup 2 (Subgroup.zpowers w') := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one (show w' ^ 2 ^ 1 = 1 from Subtype.ext (by
        simp only [pow_one, pow_two, Subgroup.coe_mul, Subgroup.coe_one, w', hww])))
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨k, -, hk⟩ := exists_conj_mem_sylow_of_le (T.mapSurjective d.toCentralizer_surjective)
    le_top le_top hp
  have hkw := hk w' (Subgroup.mem_zpowers w')
  rw [Sylow.coe_mapSurjective] at hkw
  obtain ⟨t, htT, hte⟩ := Subgroup.mem_map.mp hkw
  have hmem : (k : J ⧸ Subgroup.center J) * w * (k : J ⧸ Subgroup.center J)⁻¹ ∈
      (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) := by
    have hte' := congrArg Subtype.val hte
    rw [d.coe_toCentralizer] at hte'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, w'] at hte'
    rw [← hte']
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ htT)
  obtain ⟨v, hv⟩ := hb.exists_caseC3Word (Subgroup.map_mono hb.le_top hmem)
  have hv2 : v.val % 2 = 0 := hb.caseC3Word_mem_bot_iff.mp (hv ▸ hmem)
  have hgen : CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x v) := by
    have h' := CaseC3.genuine_conj _ hw (k : J ⧸ Subgroup.center J)⁻¹
    rwa [inv_inv, ← hv] at h'
  have hv0 : v ≠ 0 := fun h0 => hw1 (by
    rw [h0, CaseC3BCD.caseC3Word_zero] at hv
    rw [show w = (k : J ⧸ Subgroup.center J)⁻¹ * ((k : J ⧸ Subgroup.center J) * w *
      (k : J ⧸ Subgroup.center J)⁻¹) * (k : J ⧸ Subgroup.center J) by group, ← hv]
    group)
  obtain ⟨h, hh, hhv⟩ := d.exists_conj_forty_of_c3GenW hHu hHS
    (((hb.genuine_even_iff hv2).mp hgen).resolve_left hv0)
  refine ⟨(k : J ⧸ Subgroup.center J)⁻¹ * h, H.mul_mem (H.inv_mem (hHu k.2)) hh, ?_⟩
  calc (k : J ⧸ Subgroup.center J)⁻¹ * h * caseC3Word (Subgroup.center J) u m y x 40 *
        ((k : J ⧸ Subgroup.center J)⁻¹ * h)⁻¹ =
      (k : J ⧸ Subgroup.center J)⁻¹ * (h * caseC3Word (Subgroup.center J) u m y x 40 * h⁻¹) *
        (k : J ⧸ Subgroup.center J) := by group
    _ = w := by rw [hhv, hv]; group

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
