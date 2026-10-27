module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseC
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalCaseB

public section

namespace CFSG.ComponentClassification.RankTwoClassical

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoStandard

@[expose] def Step73 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (D : ClassicalModel A), AS76b.Hyp31 A →
    RankTwoClassicalEvenType (rankTwoQuot A) → 4 ≤ D.q

variable {G : Type} [Group G] [Finite G]

theorem step74_of_ne_symplectic (I : Inputs74) (hS : ClassicalSplit)
    (h117 : ClassicalPrimaryPerfect) (h33 : Lemma33Three) (h73 : Step73) {A : Subgroup G}
    (D : ClassicalModel A) (hfam : D.family ≠ .symplectic) (hA : Hyp31 A)
    (hTy : RankTwoClassicalEvenType (rankTwoQuot A)) :
    ∃ (R T : Subgroup G) (g : G), Choice74 D R T g := by
  have hq := h73 G A D hA hTy
  have hOut := I.hOut ↥A hA.standard.1.1 hTy
  obtain ⟨g₀, hg₀, R, T₀, hR, hT₀, -, -, hTR, -, -⟩ := section3Config_of I.h32 h33 I.h4 I.h34 G A hA
  have hc₀ : Sec3 A R T₀ g₀ := ⟨hA, hR, hg₀, hT₀, commutator_eq_bot_iff_le_centralizer.mp hTR⟩
  obtain ⟨T, g, hm⟩ := exists_minChoice D hc₀
  have hc := hm.sec3
  obtain ⟨t₀, ht₀, ht₀1⟩ := T.bot_or_exists_ne_one.resolve_left hc.T_ne_bot
  obtain ⟨p₀, hp₀, hρ₀⟩ := hc.exists_aPart I.h32 I.h4 I.h34 ht₀
  obtain ⟨hZ, -, -, -⟩ := hc.case14 I hTy D hfam hq ht₀ ht₀1 hp₀ hρ₀
  obtain ⟨t, ht, ht1, p, hp, hρ, hpn⟩ := hc.exists_choiceMeasure I.h32 I.h4 I.h34 D hZ
  have hprim : D.IsPrimary p := by
    by_contra hnp
    obtain ⟨y, hJ⟩ := hc.exists_jData I hTy D hfam hq ht ht1 hp hρ
    have hsw := hc.swap
    obtain ⟨t', ht', ht'1⟩ :=
      (rightConjugate R g⁻¹).bot_or_exists_ne_one.resolve_left hsw.T_ne_bot
    obtain ⟨p', hp', hρ'⟩ := hsw.exists_aPart I.h32 I.h4 I.h34 ht'
    obtain ⟨y', hJ'⟩ := hsw.exists_jData I hTy D hfam hq ht' ht'1 hp' hρ'
    rcases hc.dichotomy I.h32 I.h4 I.h34 hJ hJ' with hTA | hTA
    ·
      have hno : ∀ (T' : Subgroup G) (x : G), Sec3 A R T' x → ¬ T' ≤ A := by
        intro T' x h' hT'
        apply hc.T_ne_bot
        rw [← hTA]
        exact (inf_eq_left.mpr (hm.le_of_le T' x h' hT')).symm
      obtain ⟨T', x, h', s, hs, hs1, q, hqA, hqρ, m, hmn, hqm⟩ :=
        hc.caseC I hTy D hfam hq hS ht ht1 hp hρ hnp hpn hno
      have hle := hm.le_of_mem h' (Or.inr fun hTA' => hno T g hc hTA') hs hs1 hqA hqρ hqm
      omega
    ·
      obtain ⟨T', x, h', hT'A, s, hs, hs1, hsA, m, hmn, hsm⟩ :=
        hc.caseB I hTy D hfam hq hS ht ht1 hp hρ hnp hpn hTA
      have hle := hm.le_of_mem h' (Or.inl hT'A) hs hs1 hsA
        (by rw [inv_mul_cancel]; exact one_mem _) hsm
      omega
  obtain ⟨-, hfus, -⟩ :=
    I.h222.conclusion14 D hfam hq (hc.hyp221 I.h32 I.h4 I.h34 I.h2 hOut I.hF hTy)
  have hall : ∀ t' ∈ T, t' ≠ 1 → ∀ p' ∈ A, t'⁻¹ * p' ∈ R → D.IsPrimary p' := by
    intro t' ht' ht'1 p' hp' hρ'
    obtain ⟨b, hb, hbp⟩ := hfus t ht ht1 t' ht' ht'1 p p' (hc.isAPart I.h32 ht hp hρ)
      (hc.isAPart I.h32 ht' hp' hρ')
    rw [← hbp]
    exact D.isPrimary_conj hprim hb
  have hTA := hc.inf_eq_bot_of_primary I.h4 I.h32 I.h34 h117 D hq hOut hZ hall
  refine ⟨R, T, g, hc.sylowR, hc.not_mem, hc.sylowT, hc.le_centralizer, hTA, hall, ?_, hZ, hq⟩
  intro x hx
  apply hc.T_ne_bot
  rw [← hTA]
  exact (inf_eq_left.mpr (hm.le_of_le _ x (hc.sec3_of_le I.h32 hZ hx) hx)).symm

end CFSG.ComponentClassification.RankTwoClassical
