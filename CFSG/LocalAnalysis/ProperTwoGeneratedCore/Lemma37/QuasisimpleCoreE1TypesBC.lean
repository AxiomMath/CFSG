module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1TypesBCBurnside
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1TypesBCFusion
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsCosets
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Classes
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1CentU

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

theorem e1_typeB_genuine_forty : ∀ v : Fin 64, e1Gen false false (c3Mul v 40) = true →
    v.val % 4 = 0 := by decide +kernel

theorem e1_commutator_mem : ∀ v w : Fin 64, (c3Mul (c3Conj v w) (c3Inv w)).val % 4 = 0 := by
  decide +kernel

theorem e1_coset_two : ∀ v w : Fin 64, v.val % 4 = 2 → w.val % 4 = 2 →
    (c3Mul (c3Inv v) w).val % 4 = 0 := by decide +kernel

theorem e1_six_powers : c3Mul 6 6 = 8 ∧ c3Mul (c3Mul 6 6) 6 = c3Inv 6 ∧
    (c3Inv 6).val % 4 = 2 ∧ c3Mul (c3Inv 6) (c3Inv 6) = 8 := by decide

open CFSG.Open

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
include d

theorem commute_forty (v : Fin 64) :
    Commute (caseC3Word (Subgroup.center J) u m y x v)
      (caseC3Word (Subgroup.center J) u m y x 40) := by
  change _ * _ = _ * _
  rw [d.caseC3BCD.caseC3Word_mul, d.caseC3BCD.caseC3Word_mul, c3Mul_forty_comm]

omit [Finite J] d in
theorem isConj_eight :
    IsConj (u : J ⧸ Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x 8) := by
  rw [CaseC3BCD.caseC3Word_eight]
  exact isConj_iff.mpr ⟨(x : J ⧸ Subgroup.center J), by
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]⟩

theorem commutator_eq_top : commutator (J ⧸ Subgroup.center J) = ⊤ := by
  have := d.setting.perfect
  exact Group.isPerfect_def.mp inferInstance

theorem false_of_typeC
    (htype : ¬ ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
      s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
    {gf gef : Bool} (hgg : (gf && gef) = false) (hor : (gf || gef) = true)
    (hlab : ∀ v, CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x v) ↔
      e1Gen gf gef v = true) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := d.caseC3BCD
  set S'' := S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J)) with hS''def
  have hS'' : (S'' : Subgroup (J ⧸ Subgroup.center J)) =
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) :=
    Sylow.coe_mapSurjective _ _
  have hUS : e1UBar (Subgroup.center J) u m y x gf ≤ (S'' : Subgroup (J ⧸ Subgroup.center J)) := by
    rw [hS'']
    exact hb.e1UBar_le gf
  have hU : (e1UBar (Subgroup.center J) u m y x gf).relIndex
      (S'' : Subgroup (J ⧸ Subgroup.center J)) = 2 := by
    rw [hS'']
    exact hb.relIndex_e1UBar gf
  set yb := caseC3Word (Subgroup.center J) u m y x 2 with hyb
  have hy2 : orderOf yb = 2 := hb.orderOf_caseC3Word (by decide) (by decide)
  obtain ⟨g, hg⟩ := Lemma37.exists_conj_mem_of_relIndex_eq_two d.commutator_eq_top S'' hUS hU hy2
  have hy1 : yb ≠ 1 := fun h => absurd (hb.caseC3Word_eq_one_iff.mp h) (by decide)
  obtain ⟨hyg, hyzg⟩ := hb.not_genuine_of_mem_e1EBar
    (hb.caseC3Word_mem_e1EBar_iff.mpr (by decide)) hy1
    (fun h => absurd (hb.caseC3Word_inj.mp h) (by decide))
  have hyy : yb * yb = 1 := hb.caseC3Word_mul_self_eq_one_iff.mpr (by decide)
  have htt : g⁻¹ * yb * g * (g⁻¹ * yb * g) = 1 := by
    rw [show g⁻¹ * yb * g * (g⁻¹ * yb * g) = g⁻¹ * (yb * yb) * g by group, hyy]
    group
  have ht1 : g⁻¹ * yb * g ≠ 1 := fun h => hy1 (by
    rw [show yb = g * (g⁻¹ * yb * g) * g⁻¹ by group, h]
    group)
  have htg : ¬ CaseC3.Genuine (Subgroup.center J) (g⁻¹ * yb * g) := fun h => hyg (by
    have h' := CaseC3.genuine_conj _ h g⁻¹
    rwa [inv_inv, show g * (g⁻¹ * yb * g) * g⁻¹ = yb by group] at h')
  have hut := d.isConj_of_mem_map_right_or_left
    (hb.mem_map_of_mem_e1UBar_of_typeC hgg hor hlab hg htt ht1 htg) ht1
  have huy : IsConj (u : J ⧸ Subgroup.center J) yb :=
    hut.trans (isConj_iff.mpr ⟨g, by group⟩)
  obtain ⟨h, hh, hhu⟩ := d.exists_mem_centralizer_conj_eq huy (d.commute_forty 2) hyzg
  have hhS : h * (u : J ⧸ Subgroup.center J) * h⁻¹ ∈
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) := by
    rw [hhu]
    exact hb.caseC3Word_mem 2
  rcases hb.conj_eq_of_mem_centralizer_of_not_typeD htype S rfl hh hhS with h1 | h1
  · have h2 : yb = caseC3Word (Subgroup.center J) u m y x 32 := by
      rw [← hhu, h1, CaseC3BCD.caseC3Word_thirtytwo]
    exact absurd (hb.caseC3Word_inj.mp h2) (by decide)
  · have h2 : yb = caseC3Word (Subgroup.center J) u m y x 8 := by
      rw [← hhu, h1, CaseC3BCD.caseC3Word_eight]
    exact absurd (hb.caseC3Word_inj.mp h2) (by decide)

theorem mem_sup_of_isConj_of_typeB
    (htype : ¬ ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
      s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
    (hlab : ∀ v, CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x v) ↔
      e1Gen false false v = true)
    {s : J ⧸ Subgroup.center J}
    (hs : s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)))
    (hus : IsConj (u : J ⧸ Subgroup.center J) s) :
    s ∈ (partCLeft T L ⊔ partCRight T L).map (QuotientGroup.mk' (Subgroup.center J)) := by
  have hb := d.caseC3BCD
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  rw [hb.caseC3Word_mem_sup_iff]
  by_cases hg : CaseC3.Genuine (Subgroup.center J)
      (caseC3Word (Subgroup.center J) u m y x v * caseC3Word (Subgroup.center J) u m y x 40)
  · rw [hb.caseC3Word_mul, hlab] at hg
    exact e1_typeB_genuine_forty v hg
  obtain ⟨h, hh, hhu⟩ := d.exists_mem_centralizer_conj_eq hus (d.commute_forty v) hg
  have hhS : h * (u : J ⧸ Subgroup.center J) * h⁻¹ ∈
      (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) := by
    rw [hhu]
    exact hs
  rcases hb.conj_eq_of_mem_centralizer_of_not_typeD htype S rfl hh hhS with h1 | h1
  · have h2 : caseC3Word (Subgroup.center J) u m y x v =
        caseC3Word (Subgroup.center J) u m y x 32 := by
      rw [← hhu, h1, CaseC3BCD.caseC3Word_thirtytwo]
    rw [hb.caseC3Word_inj.mp h2]
    decide
  · have h2 : caseC3Word (Subgroup.center J) u m y x v =
        caseC3Word (Subgroup.center J) u m y x 8 := by
      rw [← hhu, h1, CaseC3BCD.caseC3Word_eight]
    rw [hb.caseC3Word_inj.mp h2]
    decide

theorem exists_zpow_six (n : ℤ) : ∃ w : Fin 64,
    caseC3Word (Subgroup.center J) u m y x 6 ^ n = caseC3Word (Subgroup.center J) u m y x w ∧
      (w = 0 ∨ w = 8 ∨ (w.val % 4 = 2 ∧ c3Mul w w = 8)) := by
  have hb := d.caseC3BCD
  obtain ⟨h66, h666, hinv, hinv2⟩ := e1_six_powers
  have h4 : caseC3Word (Subgroup.center J) u m y x 6 ^ (4 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact hb.pow_four_eq_one (hb.caseC3Word_mem 6)
  rw [zpow_eq_zpow_emod n h4]
  have : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases this with h | h | h | h <;> rw [h]
  · exact ⟨0, by rw [zpow_zero, CaseC3BCD.caseC3Word_zero], Or.inl rfl⟩
  · exact ⟨6, zpow_one _, Or.inr (Or.inr (by decide))⟩
  · refine ⟨8, ?_, Or.inr (Or.inl rfl)⟩
    rw [zpow_ofNat, pow_two, hb.caseC3Word_mul, h66]
  · refine ⟨c3Inv 6, ?_, Or.inr (Or.inr ⟨hinv, hinv2⟩)⟩
    rw [zpow_ofNat, pow_succ, pow_two, hb.caseC3Word_mul, hb.caseC3Word_mul, h666]

theorem false_of_typeB
    (htype : ¬ ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
      s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
    (hlab : ∀ v, CaseC3.Genuine (Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x v) ↔
      e1Gen false false v = true) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb := d.caseC3BCD
  set Sb := (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)) with hSb
  set Wb := (partCLeft T L ⊔ partCRight T L).map (QuotientGroup.mk' (Subgroup.center J)) with hWb
  have hindex : Nat.Coprime 2 Sb.index := by
    have h := (S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center J))).not_dvd_index
    rw [Sylow.coe_mapSurjective] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h
  have hWS : Wb ≤ Sb := Subgroup.map_mono (hb.partC.sup_le.trans hb.le_top)
  have habel : ⁅Sb, Sb⁆ ≤ Wb := by
    rw [Subgroup.commutator_le]
    intro a ha c hc
    obtain ⟨v, rfl⟩ := hb.exists_caseC3Word ha
    obtain ⟨w, rfl⟩ := hb.exists_caseC3Word hc
    rw [commutatorElement_def, hb.caseC3Word_conj, hb.caseC3Word_inv, hb.caseC3Word_mul,
      hb.caseC3Word_mem_sup_iff]
    exact e1_commutator_mem v w
  have hnormal : (Wb.subgroupOf Sb).Normal := ⟨fun n hn s => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := Wb.mul_mem (habel (Subgroup.commutator_mem_commutator s.2 (hWS hn))) hn
    rwa [commutatorElement_def, inv_mul_cancel_right] at h⟩
  have hu8 : IsConj (u : J ⧸ Subgroup.center J) (caseC3Word (Subgroup.center J) u m y x 8) :=
    isConj_eight
  have hkey : ∀ (n : ℤ) (a : J ⧸ Subgroup.center J),
      a⁻¹ * caseC3Word (Subgroup.center J) u m y x 6 ^ n * a ∈ Sb →
      (caseC3Word (Subgroup.center J) u m y x 6 ^ n)⁻¹ *
        (a⁻¹ * caseC3Word (Subgroup.center J) u m y x 6 ^ n * a) ∈ Wb := by
    intro n a ha
    obtain ⟨w, hw, hw'⟩ := d.exists_zpow_six n
    rw [hw] at ha ⊢
    have hconj : ∀ t : J ⧸ Subgroup.center J, IsConj t (a⁻¹ * t * a) := fun t =>
      isConj_iff.mpr ⟨a⁻¹, by group⟩
    rcases hw' with rfl | rfl | ⟨hw2, hww⟩
    · rw [CaseC3BCD.caseC3Word_zero]
      simp
    · refine Wb.mul_mem (Wb.inv_mem (hb.caseC3Word_mem_sup_iff.mpr (by decide))) ?_
      exact d.mem_sup_of_isConj_of_typeB htype hlab ha (hu8.trans (hconj _))
    ·
      set t := a⁻¹ * caseC3Word (Subgroup.center J) u m y x w * a with ht
      have htt : t * t = a⁻¹ * caseC3Word (Subgroup.center J) u m y x 8 * a := by
        rw [ht, show a⁻¹ * caseC3Word (Subgroup.center J) u m y x w * a *
            (a⁻¹ * caseC3Word (Subgroup.center J) u m y x w * a) =
            a⁻¹ * (caseC3Word (Subgroup.center J) u m y x w *
              caseC3Word (Subgroup.center J) u m y x w) * a by group, hb.caseC3Word_mul, hww]
      have httW : t * t ∈ Wb := d.mem_sup_of_isConj_of_typeB htype hlab
        (Sb.mul_mem ha ha) (htt ▸ hu8.trans (hconj _))
      have htt1 : t * t ≠ 1 := fun h1 => by
        rw [htt] at h1
        have h8 : caseC3Word (Subgroup.center J) u m y x 8 = 1 := by
          rw [show caseC3Word (Subgroup.center J) u m y x 8 = a * (a⁻¹ *
            caseC3Word (Subgroup.center J) u m y x 8 * a) * a⁻¹ by group, h1]
          group
        exact absurd (hb.caseC3Word_eq_one_iff.mp h8) (by decide)
      have httg : ¬ CaseC3.Genuine (Subgroup.center J) (t * t) := fun h1 => by
        rw [htt] at h1
        have h' := CaseC3.genuine_conj _ h1 a⁻¹
        rw [inv_inv, show a * (a⁻¹ * caseC3Word (Subgroup.center J) u m y x 8 * a) * a⁻¹ =
          caseC3Word (Subgroup.center J) u m y x 8 by group, hlab] at h'
        exact absurd h' (by decide)
      obtain ⟨htT, htW⟩ := hb.mem_bot_of_mul_self ha httW htt1 httg
      obtain ⟨w', hw'⟩ := hb.exists_caseC3Word ha
      rw [← hw', hb.caseC3Word_mem_bot_iff] at htT
      rw [← hw', hb.caseC3Word_mem_sup_iff] at htW
      rw [← hw', hb.caseC3Word_inv, hb.caseC3Word_mul, hb.caseC3Word_mem_sup_iff]
      exact e1_coset_two w w' hw2 (by omega)
  refine Quasithin.generalized_thompson_transfer_one hindex ⟨hWS, hnormal⟩ habel
    (hb.caseC3Word_mem 6) (by rw [hb.caseC3Word_mem_sup_iff]; decide)
    ⟨2, hb.pow_four_eq_one (hb.caseC3Word_mem 6)⟩ hkey ?_
  rw [d.commutator_eq_top]
  exact Subgroup.mem_top _

theorem caseC3BCD_false_of_not_typeD
    (htype : ¬ ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
      s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s) : False := by
  obtain ⟨gf, gef, hgg, -, -, hlab⟩ := d.caseC3BCD.exists_e1Gen_of_not_typeD htype
  cases hor : (gf || gef)
  · obtain ⟨rfl, rfl⟩ : gf = false ∧ gef = false := by
      revert hor
      cases gf <;> cases gef <;> simp
    exact d.false_of_typeB htype hlab
  · exact d.false_of_typeC htype hgg hor hlab

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
