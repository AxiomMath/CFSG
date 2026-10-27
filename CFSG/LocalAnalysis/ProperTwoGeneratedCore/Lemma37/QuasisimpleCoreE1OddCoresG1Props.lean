module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreE1OddCoresG1

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Assembly.Dichotomy

variable {G : Type} [Group G]

namespace CaseC3BCD

variable {T Q P₁ S : Subgroup G} {e u y x m : G} {Z : Subgroup G} [Z.Normal]
  (hb : CaseC3BCD T Q P₁ S e u y x m Z) [Finite G] {τ : G ⧸ Z}
  (hτN : τ ∈ e1NBar Z u m y x)
  (hτfpf : ∀ s ∈ e1RBar Z u m y x, s ≠ 1 → s ≠ caseC3Word Z u m y x 40 →
    τ * s * τ⁻¹ ≠ s ∧ τ * s * τ⁻¹ ≠ s * caseC3Word Z u m y x 40)
  (hτ3 : ∀ s ∈ e1RBar Z u m y x, τ ^ 3 * s = s * τ ^ 3)
include hb hτN hτfpf hτ3

theorem exists_of_mem_e1GBar {g : G ⧸ Z} (hg : g ∈ e1GBar Z u m y x τ) :
    ∃ v ∈ e1VBar Z u m y x, g = v ∨ g = v * (τ * caseC3Word Z u m y x 20 * τ⁻¹) :=
  exists_of_mem_sup_zpowers (conj_mul_self_eq_one (hb.caseC3Word_mul_self_eq_one_iff.mpr
    (by decide)) τ) (fun _ hv => hb.commute_of_mem_e1VBar hτN
      (hb.e1GBar_commute hτN hτfpf hτ3) hv) hg

theorem isElemAbelian_e1GBar : CFSG.Assembly.IsElemAbelian 2 (e1GBar Z u m y x τ) := by
  set r' := τ * caseC3Word Z u m y x 20 * τ⁻¹ with hr'
  have hr'r' : r' * r' = 1 :=
    conj_mul_self_eq_one (hb.caseC3Word_mul_self_eq_one_iff.mpr (by decide)) τ
  have hVr' : ∀ v ∈ e1VBar Z u m y x, Commute v r' := fun _ hv =>
    hb.commute_of_mem_e1VBar hτN (hb.e1GBar_commute hτN hτfpf hτ3) hv
  have hVV : ∀ v ∈ e1VBar Z u m y x, ∀ w ∈ e1VBar Z u m y x, Commute v w := fun _ hv _ hw =>
    hb.commute_of_mem_e1WBar (hb.e1VBar_le_e1WBar hv) (hb.e1VBar_le_e1WBar hw)
  have hV2 : ∀ v ∈ e1VBar Z u m y x, v * v = 1 := fun _ hv =>
    hb.mul_self_of_mem_e1WBar (hb.e1VBar_le_e1WBar hv)
  have hcomm : ∀ g ∈ e1GBar Z u m y x τ, ∀ h ∈ e1GBar Z u m y x τ, Commute g h := by
    intro g hg h hh
    obtain ⟨v, hv, hgv⟩ := hb.exists_of_mem_e1GBar hτN hτfpf hτ3 hg
    obtain ⟨w, hw, hhw⟩ := hb.exists_of_mem_e1GBar hτN hτfpf hτ3 hh
    have hv' := hVr' v hv
    have hw' := hVr' w hw
    have hvw := hVV v hv w hw
    rcases hgv with rfl | rfl <;> rcases hhw with rfl | rfl
    · exact hvw
    · exact hvw.mul_right hv'
    · exact hvw.mul_left hw'.symm
    · exact (hvw.mul_right hv').mul_left (hw'.symm.mul_right (Commute.refl r'))
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2).eq⟩⟩, fun g hg => ?_⟩
  rw [pow_two]
  obtain ⟨v, hv, hgv⟩ := hb.exists_of_mem_e1GBar hτN hτfpf hτ3 hg
  have hv' := (hVr' v hv).eq
  have hvv := hV2 v hv
  rcases hgv with rfl | rfl
  · exact hvv
  · rw [show v * r' * (v * r') = v * (r' * v) * r' by group, ← hv',
      show v * (v * r') * r' = v * v * (r' * r') by group, hvv, hr'r', one_mul]

omit hτ3 in
theorem conj_not_mem_e1VBar : τ * caseC3Word Z u m y x 20 * τ⁻¹ ∉ e1VBar Z u m y x := by
  intro h
  obtain ⟨t, ht, hteq⟩ := hb.mem_e1VBar_iff.mp h
  have h1 : caseC3Word Z u m y x 20 ≠ 1 := by rw [Ne, hb.caseC3Word_eq_one_iff]; decide
  have hz : caseC3Word Z u m y x 20 ≠ caseC3Word Z u m y x 40 := by
    rw [Ne, hb.caseC3Word_inj]; decide
  obtain ⟨hne1, hne2⟩ := hτfpf _ (hb.caseC3Word_mem_e1RBar_iff.mpr (by decide)) h1 hz
  have hτz := hb.conj_forty_of_mem_e1NBar hτN
  rcases ht with rfl | rfl | rfl | rfl
  · rw [caseC3Word_zero, show (1 : G ⧸ Z) = τ * 1 * τ⁻¹ by group] at hteq
    exact h1 (mul_left_cancel (mul_right_cancel hteq)).symm
  · exact hne1 hteq.symm
  · rw [← hτz] at hteq
    exact hz (mul_left_cancel (mul_right_cancel hteq)).symm
  · exact hne2 (by rw [← hteq, show (60 : Fin 64) = c3Mul 20 40 by decide, hb.caseC3Word_mul])

omit hτ3 in
theorem le_card_e1GBar : 8 ≤ Nat.card (e1GBar Z u m y x τ) := by
  have hle : e1VBar Z u m y x ≤ e1GBar Z u m y x τ := le_sup_left
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hle
  rw [hb.card_e1VBar] at hk
  have hne : Nat.card (e1GBar Z u m y x τ) ≠ 4 := fun h4 => by
    have heq : e1VBar Z u m y x = e1GBar Z u m y x τ :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [h4, hb.card_e1VBar])
    refine hb.conj_not_mem_e1VBar hτN hτfpf ?_
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hpos : 0 < Nat.card (e1GBar Z u m y x τ) := Nat.card_pos
  omega

theorem genuine_of_mem_e1GBar {g : G ⧸ Z} (hg : g ∈ e1GBar Z u m y x τ) (hg1 : g ≠ 1) :
    CaseC3.Genuine Z g := by
  set zb := caseC3Word Z u m y x 40 with hzb
  set r := caseC3Word Z u m y x 20 with hr
  set r' := τ * r * τ⁻¹ with hr'
  have hconj : ∀ {s : G ⧸ Z}, CaseC3.Genuine Z s → CaseC3.Genuine Z (τ * s * τ⁻¹) := fun hs => by
    have h := CaseC3.genuine_conj Z hs τ⁻¹
    rwa [inv_inv] at h
  have hτz : τ * zb * τ⁻¹ = zb := hb.conj_forty_of_mem_e1NBar hτN
  have hzr : zb * r = caseC3Word Z u m y x 60 := by rw [hb.caseC3Word_mul]; rfl
  have hrz : r * zb = caseC3Word Z u m y x 60 := by rw [hb.caseC3Word_mul]; rfl
  have hzz : zb * zb = 1 := hb.forty_mul_self
  have hzconj : ∀ s : G ⧸ Z, zb * (τ * s * τ⁻¹) = τ * (zb * s) * τ⁻¹ := fun s => by
    rw [show τ * (zb * s) * τ⁻¹ = τ * zb * τ⁻¹ * (τ * s * τ⁻¹) by group, hτz]
  have g20 : CaseC3.Genuine Z r := hb.genuine_of_c3GenW e1V_facts.2.2.1
  have g40 : CaseC3.Genuine Z zb := hb.genuine_of_c3GenW e1V_facts.2.2.2.1
  have g60 : CaseC3.Genuine Z (caseC3Word Z u m y x 60) := hb.genuine_of_c3GenW
    e1V_facts.2.2.2.2.1
  have g1 : CaseC3.Genuine Z r' := hconj g20
  have g2 : CaseC3.Genuine Z (zb * r') := by rw [hzconj, hzr]; exact hconj g60
  have g3 : CaseC3.Genuine Z (τ * r' * τ⁻¹) := hconj g1
  have g4 : CaseC3.Genuine Z (zb * (τ * r' * τ⁻¹)) := by rw [hzconj]; exact hconj g2
  have hrr' : r * r' = τ * r' * τ⁻¹ ∨ r * r' = zb * (τ * r' * τ⁻¹) := by
    have hr''r'' := conj_mul_self_eq_one (conj_mul_self_eq_one
      (hb.caseC3Word_mul_self_eq_one_iff.mpr (by decide) : r * r = 1) τ) τ
    have key : r * r' = r * r' * (τ * r' * τ⁻¹) * (τ * r' * τ⁻¹) := by
      rw [mul_assoc (r * r'), hr''r'', mul_one]
    rcases hb.e1GBar_prod hτN hτfpf hτ3 with h | h <;> rw [h] at key
    · exact Or.inl (key.trans (one_mul _))
    · exact Or.inr key
  have g5 : CaseC3.Genuine Z (r * r') := by rcases hrr' with h | h <;> rw [h] <;> assumption
  have g6 : CaseC3.Genuine Z (caseC3Word Z u m y x 60 * r') := by
    rw [← hzr, mul_assoc]
    rcases hrr' with h | h <;> rw [h]
    · exact g4
    · rw [← mul_assoc, hzz, one_mul]; exact g3
  obtain ⟨v, hv, rfl | rfl⟩ := hb.exists_of_mem_e1GBar hτN hτfpf hτ3 hg <;>
    obtain ⟨t, ht, rfl⟩ := hb.mem_e1VBar_iff.mp hv <;> rcases ht with rfl | rfl | rfl | rfl
  · exact absurd caseC3Word_zero hg1
  · exact g20
  · exact g40
  · exact g60
  · rw [caseC3Word_zero, one_mul]; exact g1
  · exact g5
  · exact g2
  · exact g6

theorem mem_normalizer_e1GBar :
    τ ∈ Subgroup.normalizer (e1GBar Z u m y x τ : Set (G ⧸ Z)) := by
  set zb := caseC3Word Z u m y x 40 with hzb
  set r := caseC3Word Z u m y x 20 with hr
  set r' := τ * r * τ⁻¹ with hr'
  set G₁ := e1GBar Z u m y x τ with hG₁
  have hVG : e1VBar Z u m y x ≤ G₁ := le_sup_left
  have hr'G : r' ∈ G₁ := Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hrG : r ∈ G₁ := hVG (hb.mem_e1VBar_iff.mpr ⟨20, by decide, rfl⟩)
  have hzG : zb ∈ G₁ := hVG (hb.mem_e1VBar_iff.mpr ⟨40, by decide, rfl⟩)
  have hτz : τ * zb * τ⁻¹ = zb := hb.conj_forty_of_mem_e1NBar hτN
  have hV : ∀ v ∈ e1VBar Z u m y x, τ * v * τ⁻¹ ∈ G₁ := by
    intro v hv
    obtain ⟨t, ht, rfl⟩ := hb.mem_e1VBar_iff.mp hv
    rcases ht with rfl | rfl | rfl | rfl
    · rw [caseC3Word_zero, mul_one, mul_inv_cancel]
      exact G₁.one_mem
    · exact hr'G
    · rw [hτz]
      exact hzG
    · rw [show (60 : Fin 64) = c3Mul 40 20 by decide, ← hb.caseC3Word_mul,
        show τ * (zb * r) * τ⁻¹ = τ * zb * τ⁻¹ * (τ * r * τ⁻¹) by group, hτz]
      exact G₁.mul_mem hzG hr'G
  have hr'' : τ * r' * τ⁻¹ ∈ G₁ := by
    have hp : r * r' * (τ * r' * τ⁻¹) ∈ G₁ := by
      rcases hb.e1GBar_prod hτN hτfpf hτ3 with h | h <;> rw [h]
      · exact G₁.one_mem
      · exact hzG
    rw [show τ * r' * τ⁻¹ = (r * r')⁻¹ * (r * r' * (τ * r' * τ⁻¹)) by group]
    exact G₁.mul_mem (G₁.inv_mem (G₁.mul_mem hrG hr'G)) hp
  refine mem_normalizer_of_forall_conj_mem fun g hg => ?_
  obtain ⟨v, hv, hgv | hgv⟩ := hb.exists_of_mem_e1GBar hτN hτfpf hτ3 hg <;> rw [hgv]
  · exact hV v hv
  · rw [show τ * (v * (τ * r * τ⁻¹)) * τ⁻¹ = τ * v * τ⁻¹ * (τ * (τ * r * τ⁻¹) * τ⁻¹) by group]
    exact G₁.mul_mem (hV v hv) hr''

end CaseC3BCD

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {z u : J}

namespace E1Data

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {S : Sylow 2 J}
  {y x m : J} (d : E1Data Q B z u T L S y x m)
  (htype : ∀ s ∈ (S : Subgroup J).map (QuotientGroup.mk' (Subgroup.center J)),
    s ∉ (partCSylow T).map (QuotientGroup.mk' (Subgroup.center J)) → s * s = 1 →
      CaseC3.Genuine (Subgroup.center J) s)
  {τ : J ⧸ Subgroup.center J} (hτN : τ ∈ e1NBar (Subgroup.center J) u m y x)
  (hτfpf : ∀ s ∈ e1RBar (Subgroup.center J) u m y x, s ≠ 1 →
    s ≠ caseC3Word (Subgroup.center J) u m y x 40 →
      τ * s * τ⁻¹ ≠ s ∧ τ * s * τ⁻¹ ≠ s * caseC3Word (Subgroup.center J) u m y x 40)
  (hτ3 : ∀ s ∈ e1RBar (Subgroup.center J) u m y x, τ ^ 3 * s = s * τ ^ 3)
include d htype hτN hτfpf hτ3

theorem oddCoreSpanCompleted_e1GBar :
    OddCoreSpanCompleted (e1GBar (Subgroup.center J) u m y x τ) := by
  have hb := d.caseC3BCD
  have hE := hb.isElemAbelian_e1GBar hτN hτfpf hτ3
  refine (balanced_oddCoreSpan_completed _ hE (hb.le_card_e1GBar hτN hτfpf)
    fun a ha _ b hb' hb1 => ?_).1
  have hsq : ∀ g ∈ e1GBar (Subgroup.center J) u m y x τ, g * g = 1 := fun g hg => by
    rw [← pow_two]
    exact hE.2 g hg
  exact d.involutionOddCore_inf_le_of_genuine htype (hsq a ha)
    (congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : e1GBar _ _ _ _ _ τ) ⟨b, hb'⟩))
    (hsq b hb') hb1 (hb.genuine_of_mem_e1GBar hτN hτfpf hτ3 hb' hb1)

theorem oddCoreSpan_e1GBar :
    oddCoreSpan (e1GBar (Subgroup.center J) u m y x τ) =
    oddCoreSpan (e1WBar (Subgroup.center J) u m y x) := by
  have hb := d.caseC3BCD
  rw [← d.oddCoreSpan_e1VBar htype]
  exact (oddCoreSpan_eq_of_completed _ _ (hb.isElemAbelian_e1GBar hτN hτfpf hτ3)
    (hb.le_card_e1GBar hτN hτfpf) (d.oddCoreSpanCompleted_e1GBar htype hτN hτfpf hτ3)
    le_sup_left (by rw [hb.card_e1VBar])).symm

end E1Data

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
