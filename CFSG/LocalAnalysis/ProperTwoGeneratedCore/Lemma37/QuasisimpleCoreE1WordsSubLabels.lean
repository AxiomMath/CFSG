module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1WordsSub

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x m : G}

namespace CaseC3BCD

variable {Z : Subgroup G} [Z.Normal] (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G]
include hb

theorem sing_iff {v : Fin 64} :
    (caseC3Word Z u m y x v ∈ e1RBar Z u m y x ∧
      caseC3Word Z u m y x v * caseC3Word Z u m y x v = 1 ∧ caseC3Word Z u m y x v ≠ 1 ∧
      caseC3Word Z u m y x v ≠ caseC3Word Z u m y x 40) ↔ e1Sing v := by
  rw [hb.caseC3Word_mem_e1RBar_iff, hb.caseC3Word_mul_self_eq_one_iff, Ne,
    hb.caseC3Word_eq_one_iff, Ne, hb.caseC3Word_inj]
  rfl

theorem card_involution_e1RBar :
    Nat.card {s : G ⧸ Z // s ∈ e1RBar Z u m y x ∧ s * s = 1 ∧ s ≠ 1} = 19 :=
  (hb.card_subtype_eq (fun _ hs => hb.e1RBar_le hs.1) fun _ => by
    rw [hb.caseC3Word_mem_e1RBar_iff, hb.caseC3Word_mul_self_eq_one_iff, Ne,
      hb.caseC3Word_eq_one_iff]).trans card_e1R_involution

theorem card_sing : Nat.card {s : G ⧸ Z // s ∈ e1RBar Z u m y x ∧ s * s = 1 ∧ s ≠ 1 ∧
    s ≠ caseC3Word Z u m y x 40} = 18 :=
  (hb.card_subtype_eq (fun _ hs => hb.e1RBar_le hs.1) fun _ => hb.sing_iff).trans card_e1Sing

theorem sing_mul_forty {s : G ⧸ Z} (hs : s ∈ e1RBar Z u m y x) (hss : s * s = 1) (hs1 : s ≠ 1)
    (hsz : s ≠ caseC3Word Z u m y x 40) :
    (s * caseC3Word Z u m y x 40 ∈ e1RBar Z u m y x ∧
      s * caseC3Word Z u m y x 40 * (s * caseC3Word Z u m y x 40) = 1 ∧
      s * caseC3Word Z u m y x 40 ≠ 1 ∧
      s * caseC3Word Z u m y x 40 ≠ caseC3Word Z u m y x 40) ∧
    s * caseC3Word Z u m y x 40 ≠ s ∧
    (CaseC3.Genuine Z (s * caseC3Word Z u m y x 40) ↔ CaseC3.Genuine Z s) := by
  obtain ⟨v, -, rfl⟩ := hb.mem_e1RBar_iff.mp hs
  have hv := hb.sing_iff.mp ⟨hs, hss, hs1, hsz⟩
  obtain ⟨gf, gef, -, -, hlab⟩ := hb.exists_e1Gen
  rw [hb.caseC3Word_mul, hb.sing_iff, Ne, hb.caseC3Word_inj, hlab, hlab,
    e1Gen_mul_forty gf gef v hv]
  exact ⟨(e1Sing_mul_forty v hv).1, (e1Sing_mul_forty v hv).2, Iff.rfl⟩

theorem card_sing_genuine {gf gef : Bool}
    (hlab : ∀ v, CaseC3.Genuine Z (caseC3Word Z u m y x v) ↔ e1Gen gf gef v = true) :
    Nat.card {s : G ⧸ Z // (s ∈ e1RBar Z u m y x ∧ s * s = 1 ∧ s ≠ 1 ∧
      s ≠ caseC3Word Z u m y x 40) ∧ CaseC3.Genuine Z s} = 4 + 4 * (gf.toNat + gef.toNat) :=
  (hb.card_subtype_eq (fun _ hs => hb.e1RBar_le hs.1.1)
    fun v => and_congr hb.sing_iff (hlab v)).trans (card_e1Sing_e1Gen gf gef)

theorem not_genuine_of_mem_e1EBar {s : G ⧸ Z} (hs : s ∈ e1EBar Z u m y x) (hs1 : s ≠ 1)
    (hsz : s ≠ caseC3Word Z u m y x 40) :
    ¬ CaseC3.Genuine Z s ∧ ¬ CaseC3.Genuine Z (s * caseC3Word Z u m y x 40) := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1EBar_iff.mp hs
  obtain ⟨gf, gef, -, -, hlab⟩ := hb.exists_e1Gen
  have h := e1Gen_e1E gf gef v hv (fun h => hs1 (by rw [h, caseC3Word_zero]))
    (fun h => hsz (by rw [h]))
  rw [hb.caseC3Word_mul, hlab, hlab, h.1, h.2]
  exact ⟨Bool.false_ne_true, Bool.false_ne_true⟩

theorem mem_e1EBar_of_typeD (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s) {s : G ⧸ Z}
    (hs : s ∈ e1RBar Z u m y x) (hss : s * s = 1) (hgen : ¬ CaseC3.Genuine Z s) :
    s ∈ e1EBar Z u m y x := by
  obtain ⟨v, hv, rfl⟩ := hb.mem_e1RBar_iff.mp hs
  rw [hb.genuine_iff_of_typeD htype, Bool.not_eq_true] at hgen
  exact hb.caseC3Word_mem_e1EBar_iff.mpr
    (e1E_of_e1R_typeD v hv (hb.caseC3Word_mul_self_eq_one_iff.mp hss) hgen)

theorem mem_e1EBar_of_typeD' (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s) {s : G ⧸ Z}
    (hs : s ∈ S.map (QuotientGroup.mk' Z)) (hss : s * s = 1) (hgen : ¬ CaseC3.Genuine Z s)
    (hgen' : ¬ CaseC3.Genuine Z (s * caseC3Word Z u m y x 40)) : s ∈ e1EBar Z u m y x := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  rw [hb.caseC3Word_mul, hb.genuine_iff_of_typeD htype, Bool.not_eq_true] at hgen'
  rw [hb.genuine_iff_of_typeD htype, Bool.not_eq_true] at hgen
  exact hb.caseC3Word_mem_e1EBar_iff.mpr
    (e1E_of_typeD v (hb.caseC3Word_mul_self_eq_one_iff.mp hss) hgen hgen')

theorem eq_e1EBar_of_typeD (htype : ∀ s ∈ S.map (QuotientGroup.mk' Z),
      s ∉ T.map (QuotientGroup.mk' Z) → s * s = 1 → CaseC3.Genuine Z s)
    {A : Subgroup (G ⧸ Z)} (hAS : A ≤ S.map (QuotientGroup.mk' Z))
    (hzA : caseC3Word Z u m y x 40 ∈ A) (hcard : 8 ≤ Nat.card A) (hsq : ∀ s ∈ A, s * s = 1)
    (hgen : ∀ s ∈ A, s ≠ 1 → s ≠ caseC3Word Z u m y x 40 → ¬ CaseC3.Genuine Z s) :
    A = e1EBar Z u m y x := by
  have hzz : caseC3Word Z u m y x 40 * caseC3Word Z u m y x 40 = 1 :=
    hb.caseC3Word_mul_self_eq_one_iff.mpr c3Mul_forty_forty
  refine Subgroup.eq_of_le_of_card_ge (fun s hs => ?_) (hb.card_e1EBar ▸ hcard)
  by_cases hs1 : s = 1
  · rw [hs1]
    exact Subgroup.one_mem _
  by_cases hsz : s = caseC3Word Z u m y x 40
  · rw [hsz]
    exact hb.forty_mem_e1EBar
  refine hb.mem_e1EBar_of_typeD' htype (hAS hs) (hsq s hs) (hgen s hs hs1 hsz)
    (hgen _ (A.mul_mem hs hzA) (fun h => hsz ?_) (fun h => hs1 ?_))
  · rw [show s = s * caseC3Word Z u m y x 40 * caseC3Word Z u m y x 40 by
      rw [mul_assoc, hzz, mul_one], h, one_mul]
  · rw [show s = s * caseC3Word Z u m y x 40 * caseC3Word Z u m y x 40 by
      rw [mul_assoc, hzz, mul_one], h, hzz]

theorem conj_e1EBar_of_outer {s t : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z))
    (hsT : s ∉ T.map (QuotientGroup.mk' Z)) (hss : s * s = 1) (ht : t ∈ e1EBar Z u m y x) :
    s * t * s⁻¹ = t ∨ s * t * s⁻¹ = t * caseC3Word Z u m y x 40 := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  obtain ⟨w, hw, rfl⟩ := hb.mem_e1EBar_iff.mp ht
  rw [hb.caseC3Word_mem_bot_iff] at hsT
  rw [hb.caseC3Word_conj, hb.caseC3Word_mul, hb.caseC3Word_inj, hb.caseC3Word_inj]
  exact e1E_conj_outer v w (by omega) (hb.caseC3Word_mul_self_eq_one_iff.mp hss) hw

omit hb [Finite G] in
theorem caseC3Word_twenty : caseC3Word Z u m y x 20 = ((m * (x * m * x⁻¹) : G) : G ⧸ Z) := by
  simp [caseC3Word, c3Word]

theorem conj_transvection {v : Fin 64} (hv : v.val % 2 = 0) (hj : v.val / 16 % 2 = 1)
    (hl : v.val / 4 % 2 = 1) :
    (caseC3Word Z u m y x v * (u : G ⧸ Z) * (caseC3Word Z u m y x v)⁻¹ = (u : G ⧸ Z) ∧
      caseC3Word Z u m y x v * ((x * u * x⁻¹ : G) : G ⧸ Z) * (caseC3Word Z u m y x v)⁻¹ =
        ((x * u * x⁻¹ : G) : G ⧸ Z) ∧
      caseC3Word Z u m y x v * (y : G ⧸ Z) * (caseC3Word Z u m y x v)⁻¹ =
        (y : G ⧸ Z) * caseC3Word Z u m y x 40) ∧
    ∀ t ∈ e1EBar Z u m y x, caseC3Word Z u m y x v * t * (caseC3Word Z u m y x v)⁻¹ = t ∨
      caseC3Word Z u m y x v * t * (caseC3Word Z u m y x v)⁻¹ = t * caseC3Word Z u m y x 40 := by
  obtain ⟨h32, h8, h2⟩ := (e1_transvection_iff v hv).mpr ⟨hj, hl⟩
  refine ⟨⟨?_, ?_, ?_⟩, fun t ht => ?_⟩
  · rw [← caseC3Word_thirtytwo (Z := Z) (m := m) (y := y) (x := x), hb.caseC3Word_conj, h32]
  · rw [← caseC3Word_eight (Z := Z) (m := m) (y := y), hb.caseC3Word_conj, h8]
  · rw [← caseC3Word_two (Z := Z) (u := u) (m := m) (x := x), hb.caseC3Word_conj, h2,
      hb.caseC3Word_mul]
    rfl
  · obtain ⟨w, hw, rfl⟩ := hb.mem_e1EBar_iff.mp ht
    rw [hb.caseC3Word_conj, e1_transvection_conj v w hv hj hl hw, hb.caseC3Word_mul]
    split_ifs
    exacts [Or.inl rfl, Or.inr rfl]

theorem pow_four_eq_one {s : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z)) : s ^ 4 = 1 := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, pow_two, hb.caseC3Word_mul, hb.caseC3Word_mul,
    c3_exponent_four, caseC3Word_zero]

theorem mul_self_PQ_iff {v : Fin 64} :
    (caseC3Word Z u m y x v * caseC3Word Z u m y x v ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ∧
      caseC3Word Z u m y x v * caseC3Word Z u m y x v ≠ 1 ∧
      ¬ CaseC3.Genuine Z (caseC3Word Z u m y x v * caseC3Word Z u m y x v)) ↔
    e1PQ (c3Mul v v) := by
  rw [hb.caseC3Word_mul, hb.caseC3Word_mem_sup_iff, Ne, hb.caseC3Word_eq_one_iff]
  constructor
  · rintro ⟨h4, h0, hg⟩
    exact ⟨h4, h0, fun h => hg ((hb.genuine_even_iff (by omega)).mpr (Or.inr h))⟩
  · rintro ⟨h4, h0, hg⟩
    refine ⟨h4, h0, fun h => ?_⟩
    rcases (hb.genuine_even_iff (by omega)).mp h with h' | h'
    exacts [h0 h', hg h']

theorem mem_bot_of_mul_self {s : G ⧸ Z} (hs : s ∈ S.map (QuotientGroup.mk' Z))
    (hW : s * s ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z)) (h1 : s * s ≠ 1)
    (hgen : ¬ CaseC3.Genuine Z (s * s)) :
    s ∈ T.map (QuotientGroup.mk' Z) ∧ s ∉ (Q ⊔ P₁).map (QuotientGroup.mk' Z) := by
  obtain ⟨v, rfl⟩ := hb.exists_caseC3Word hs
  have h2 := e1PQ_mul_self v (hb.mul_self_PQ_iff.mp ⟨hW, h1, hgen⟩)
  rw [hb.caseC3Word_mem_bot_iff, hb.caseC3Word_mem_sup_iff]
  omega

theorem card_mul_self_PQ : Nat.card {s : G ⧸ Z // s ∈ S.map (QuotientGroup.mk' Z) ∧
    (s * s ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ∧ s * s ≠ 1 ∧ ¬ CaseC3.Genuine Z (s * s))} = 8 :=
  (hb.card_subtype_eq (fun _ hs => hs.1)
    fun _ => (and_iff_right (hb.caseC3Word_mem _)).trans hb.mul_self_PQ_iff).trans
    card_e1PQ_mul_self.1

end CaseC3BCD

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
