module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1Words
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Coords

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z)
include hb

omit hb in
theorem caseC3Word_one : caseC3Word Z u m y x 1 = (x : G ⧸ Z) := by
  simp [caseC3Word, c3Word]

omit hb in
theorem caseC3Word_two : caseC3Word Z u m y x 2 = (y : G ⧸ Z) := by
  simp [caseC3Word, c3Word]

omit hb in
theorem caseC3Word_three : caseC3Word Z u m y x 3 = (y : G ⧸ Z) * (x : G ⧸ Z) := by
  simp [caseC3Word, c3Word]

omit hb in
theorem caseC3Word_four : caseC3Word Z u m y x 4 = ((x * m * x⁻¹ : G) : G ⧸ Z) := by
  simp [caseC3Word, c3Word]

omit hb in
theorem caseC3Word_eight : caseC3Word Z u m y x 8 = ((x * u * x⁻¹ : G) : G ⧸ Z) := by
  simp [caseC3Word, c3Word]

omit hb in
theorem caseC3Word_sixteen : caseC3Word Z u m y x 16 = (m : G ⧸ Z) := by
  simp [caseC3Word, c3Word]

omit hb in
theorem caseC3Word_thirtytwo : caseC3Word Z u m y x 32 = (u : G ⧸ Z) := by
  simp [caseC3Word, c3Word]

variable [Finite G]

theorem caseC3Word_inj {v w : Fin 64} :
    caseC3Word Z u m y x v = caseC3Word Z u m y x w ↔ v = w :=
  hb.caseC3Word_bijective.1.eq_iff

theorem caseC3Word_mem (v : Fin 64) :
    caseC3Word Z u m y x v ∈ S.map (QuotientGroup.mk' Z) :=
  hb.caseC3Word_bijective.2.1 v

theorem exists_caseC3Word {s : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z)) :
    ∃ v, caseC3Word Z u m y x v = s :=
  hb.caseC3Word_bijective.2.2 s hs

theorem caseC3Word_eq_one_iff {v : Fin 64} : caseC3Word Z u m y x v = 1 ↔ v = 0 := by
  rw [← caseC3Word_zero (Z := Z) (u := u) (m := m) (y := y) (x := x), hb.caseC3Word_inj]

theorem caseC3Word_inv (v : Fin 64) :
    (caseC3Word Z u m y x v)⁻¹ = caseC3Word Z u m y x (c3Inv v) :=
  (eq_inv_of_mul_eq_one_right (by
    rw [hb.caseC3Word_mul, c3Mul_c3Inv, caseC3Word_zero])).symm

theorem caseC3Word_conj (v w : Fin 64) :
    caseC3Word Z u m y x v * caseC3Word Z u m y x w * (caseC3Word Z u m y x v)⁻¹ =
      caseC3Word Z u m y x (c3Conj v w) := by
  rw [hb.caseC3Word_inv, hb.caseC3Word_mul, hb.caseC3Word_mul]
  rfl

theorem caseC3Word_mul_self_eq_one_iff {v : Fin 64} :
    caseC3Word Z u m y x v * caseC3Word Z u m y x v = 1 ↔ c3Mul v v = 0 := by
  rw [hb.caseC3Word_mul, hb.caseC3Word_eq_one_iff]

omit [Finite G] in
theorem caseC3Word_mem_bot_iff {v : Fin 64} :
    caseC3Word Z u m y x v ∈ T.map (QuotientGroup.mk' Z) ↔ v.val % 2 = 0 :=
  ⟨fun h => by
    by_contra h'
    exact hb.caseC3Word_not_mem_bot (by omega) h, hb.caseC3Word_mem_bot⟩

omit [Finite G] in
theorem caseC3Word_mem_sup_iff {v : Fin 64} :
    caseC3Word Z u m y x v ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ↔ v.val % 4 = 0 := by
  refine ⟨fun h => ?_, hb.caseC3Word_mem_sup⟩
  by_contra h4
  by_cases h2 : v.val % 2 = 0
  · exact hb.caseC3Word_not_mem_sup h2 h4 h
  · exact hb.caseC3Word_not_mem_bot (by omega) (Subgroup.map_mono hb.partC.sup_le h)

omit [Finite G] in
theorem genuine_of_c3GenW {v : Fin 64} (hv : c3GenW v) :
    CaseC3.Genuine Z (caseC3Word Z u m y x v) := by
  have hc := hb.partC
  obtain ⟨φQ⟩ := hc.quaternion
  obtain ⟨φP⟩ := hb.quaternion_right
  obtain ⟨hv4, hvP, hvQ⟩ := hv
  have hw := caseC3Word_eq (Z := Z) (u := u) (m := m) (y := y) (x := x) v
  rw [show v.val % 2 = 0 by omega, show v.val / 2 % 2 = 0 by omega, pow_zero, pow_zero, mul_one,
    mul_one, ← QuotientGroup.mk_mul] at hw
  set p := u ^ (v.val / 32 % 2) * m ^ (v.val / 16 % 2) with hp
  set q := (x * u * x⁻¹) ^ (v.val / 8 % 2) * (x * m * x⁻¹) ^ (v.val / 4 % 2) with hq
  have hpP : p ∈ P₁ := hb.pPart_mem _ _
  have hqQ : q ∈ Q := hb.qPart_mem _ _
  have hp1 : (p : G ⧸ Z) ≠ 1 := fun h1 => by
    have := hb.pPart_mk_eq_one (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
    omega
  have hq1 : (q : G ⧸ Z) ≠ 1 := fun h1 => by
    have := hb.qPart_mk_eq_one (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1
    omega
  have hpp : p * p = e := quaternion_mul_self_of_ne φP hc.mem_right hc.order hpP
    (fun h => hp1 (by rw [h, QuotientGroup.mk_one])) (fun h => hp1 (by rw [h, hb.mk_centralElt]))
  have hqq : q * q = e := quaternion_mul_self_of_ne φQ hc.mem_left hc.order hqQ
    (fun h => hq1 (by rw [h, QuotientGroup.mk_one])) (fun h => hq1 (by rw [h, hb.mk_centralElt]))
  refine ⟨p * q, hw.symm, ?_⟩
  calc p * q * (p * q) = p * (q * p) * q := by group
    _ = p * (p * q) * q := by rw [hc.commute q hqQ p hpP]
    _ = (p * p) * (q * q) := by group
    _ = 1 := by rw [hpp, hqq, hc.centralElt_mul_self]

theorem c3Mul_self_of_genuine {v : Fin 64} (h : CaseC3.Genuine Z (caseC3Word Z u m y x v)) :
    c3Mul v v = 0 := by
  obtain ⟨g, hg, hgg⟩ := h
  rw [← hb.caseC3Word_mul_self_eq_one_iff, ← hg, ← QuotientGroup.mk_mul, hgg,
    QuotientGroup.mk_one]

theorem genuine_even_iff {v : Fin 64} (hv : v.val % 2 = 0) :
    CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ v = 0 ∨ c3GenW v := by
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hv0 : v = 0
    · exact Or.inl hv0
    have hne : caseC3Word Z u m y x v ≠ 1 := fun h1 => hv0 (hb.caseC3Word_eq_one_iff.mp h1)
    have hW := hb.toCaseC3.mem_of_genuine Z hb.mem_iff (hb.caseC3Word_mem_bot hv) h hne
    exact hb.c3GenW_of_genuine (hb.caseC3Word_mem_sup_iff.mp hW) h
  · rintro (rfl | h)
    · rw [caseC3Word_zero]
      exact ⟨1, QuotientGroup.mk_one Z, mul_one 1⟩
    · exact hb.genuine_of_c3GenW h

theorem genuine_outer_iff {v : Fin 64} (hv : v.val % 2 = 1) (hvv : c3Mul v v = 0) :
    CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔
      CaseC3.Genuine Z (caseC3Word Z u m y x (e1OuterRep v)) := by
  obtain ⟨w, -, hw⟩ := c3_outer_conj v hv hvv
  have hconj := hb.caseC3Word_conj w (e1OuterRep v)
  rw [hw] at hconj
  constructor
  · intro h
    have h' := CaseC3.genuine_conj Z h (caseC3Word Z u m y x w)
    rwa [← hconj, show (caseC3Word Z u m y x w)⁻¹ * (caseC3Word Z u m y x w *
      caseC3Word Z u m y x (e1OuterRep v) * (caseC3Word Z u m y x w)⁻¹) *
      caseC3Word Z u m y x w = caseC3Word Z u m y x (e1OuterRep v) by group] at h'
  · intro h
    have h' := CaseC3.genuine_conj Z h (caseC3Word Z u m y x w)⁻¹
    rwa [inv_inv, hconj] at h'

theorem genuine_iff_e1Gen {gf gef : Bool}
    (hf : CaseC3.Genuine Z (caseC3Word Z u m y x 1) ↔ gf = true)
    (hef : CaseC3.Genuine Z (caseC3Word Z u m y x 3) ↔ gef = true) (v : Fin 64) :
    CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen gf gef v = true := by
  by_cases hvv : c3Mul v v = 0
  · rcases Nat.mod_two_eq_zero_or_one v.val with hv | hv
    · rw [hb.genuine_even_iff hv, e1Gen_even_iff gf gef v hv]
    · rw [hb.genuine_outer_iff hv hvv, e1Gen_outer gf gef v hv hvv]
      unfold e1OuterRep
      split_ifs
      · rw [e1Gen_one]
        exact hf
      · rw [e1Gen_three]
        exact hef
  · exact ⟨fun h => absurd (hb.c3Mul_self_of_genuine h) hvv,
      fun h => absurd (mul_self_of_e1Gen gf gef v h) hvv⟩

theorem exists_e1Gen : ∃ gf gef : Bool, (CaseC3.Genuine Z (x : G ⧸ Z) ↔ gf = true) ∧
    (CaseC3.Genuine Z ((y : G ⧸ Z) * (x : G ⧸ Z)) ↔ gef = true) ∧
    ∀ v, CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen gf gef v = true := by
  classical
  refine ⟨decide (CaseC3.Genuine Z (x : G ⧸ Z)),
    decide (CaseC3.Genuine Z ((y : G ⧸ Z) * (x : G ⧸ Z))), by simp, by simp, ?_⟩
  exact hb.genuine_iff_e1Gen (by rw [caseC3Word_one]; simp) (by rw [caseC3Word_three]; simp)

theorem typeD_iff : (∀ s ∈ S.map (QuotientGroup.mk' Z), s ∉ T.map (QuotientGroup.mk' Z) →
      s * s = 1 → CaseC3.Genuine Z s) ↔
    CaseC3.Genuine Z (x : G ⧸ Z) ∧ CaseC3.Genuine Z ((y : G ⧸ Z) * (x : G ⧸ Z)) := by
  rw [← caseC3Word_three (Z := Z) (u := u) (m := m) (y := y) (x := x),
    ← caseC3Word_one (Z := Z) (u := u) (m := m) (y := y) (x := x)]
  constructor
  · intro h
    exact ⟨h _ (hb.caseC3Word_mem 1) (hb.caseC3Word_not_mem_bot (by decide))
        (hb.caseC3Word_mul_self_eq_one_iff.mpr (by decide)),
      h _ (hb.caseC3Word_mem 3) (hb.caseC3Word_not_mem_bot (by decide))
        (hb.caseC3Word_mul_self_eq_one_iff.mpr (by decide))⟩
  · rintro ⟨h1, h3⟩ s hs hsT hss
    obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
    have hv : v.val % 2 = 1 := by
      by_contra h'
      exact hsT (hb.caseC3Word_mem_bot (by omega))
    rw [hb.genuine_outer_iff hv (hb.caseC3Word_mul_self_eq_one_iff.mp hss)]
    unfold e1OuterRep
    split_ifs
    exacts [h1, h3]

theorem genuine_iff_of_typeD (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s) (v : Fin 64) :
    CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen true true v = true := by
  obtain ⟨h1, h3⟩ := hb.typeD_iff.mp htype
  exact hb.genuine_iff_e1Gen (iff_of_true (by rwa [caseC3Word_one]) rfl)
    (iff_of_true (by rwa [caseC3Word_three]) rfl) v

theorem exists_e1Gen_of_not_typeD (htype : ¬ ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s) :
    ∃ gf gef : Bool, (gf && gef) = false ∧ (CaseC3.Genuine Z (x : G ⧸ Z) ↔ gf = true) ∧
      (CaseC3.Genuine Z ((y : G ⧸ Z) * (x : G ⧸ Z)) ↔ gef = true) ∧
      ∀ v, CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen gf gef v = true := by
  obtain ⟨gf, gef, hf, hef, h⟩ := hb.exists_e1Gen
  refine ⟨gf, gef, ?_, hf, hef, h⟩
  rw [hb.typeD_iff, hf, hef] at htype
  revert htype
  cases gf <;> cases gef <;> simp

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
