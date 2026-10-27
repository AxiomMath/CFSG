module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveA5
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveDefs

public section

namespace CFSG.ComponentClassification.RankTwoAltFive

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc75Lemma31

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_sup {H K : Subgroup G} {y : G} (hH : y ∈ normalizer (H : Set G))
    (hK : y ∈ normalizer (K : Set G)) : y ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [← rightConjugate_eq_self_iff] at hH hK ⊢
  change (H ⊔ K).map _ = _
  rw [Subgroup.map_sup]
  exact congrArg₂ (· ⊔ ·) hH hK

omit [Finite G] in
theorem mem_normalizer_inf {H K : Subgroup G} {y : G} (hH : y ∈ normalizer (H : Set G))
    (hK : y ∈ normalizer (K : Set G)) : y ∈ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hH hK ⊢
  intro h
  rw [mem_inf, mem_inf, hH h, hK h]

omit [Finite G] in
noncomputable def conjEquiv (A : Subgroup G) (x : G) : ↥(rightConjugate A x) ≃* ↥A :=
  (A.equivMapOfInjective _ (MulAut.conj x⁻¹).injective).symm

theorem isSylowOf_four {A P : Subgroup G} (e : ↥A ≃* A5) (hPA : P ≤ A)
    (hP : Nat.card P = 4) : IsSylowOf 2 P A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isSylowOf_of_card hPA (by rw [hP, Nat.card_congr e.toEquiv, fact_A5]; rfl)

theorem exists_sec3 (hcfg : Section3Config) {A R : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) :
    ∃ g : G, g ∉ normalizer (A : Set G) ∧ ∃ T : Subgroup G,
      IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g) ∧
        T ≤ normalizer (A : Set G) ∧ T ≤ centralizer (R : Set G) := by
  obtain ⟨g, hg, R₁, T, hR₁, hT, hTN, -, hTR, -, -⟩ := hcfg G A hA
  obtain ⟨c, hc, hRc⟩ := Lemma22.exists_conj_eq_of_isSylowOf hR₁ hR
  have hcN : c⁻¹ ∈ normalizer (A : Set G) :=
    inv_mem (centralizer_le_normalizer _ hc)
  have hRc' : R = rightConjugate R₁ c⁻¹ := by
    rw [hRc]
    change R₁.map (MulAut.conj c).toMonoidHom = R₁.map (MulAut.conj c⁻¹⁻¹).toMonoidHom
    rw [inv_inv]
  refine ⟨g * c⁻¹, fun h => hg ?_, rightConjugate T c⁻¹, ?_, ?_, ?_⟩
  · simpa using mul_mem h (inv_mem hcN)
  · rw [← rightConjugate_mul]
    exact AschbacherTheorem3.isSylowOf_rightConjugate hT c⁻¹
  · exact Lemma36.rightConjugate_le hTN (le_normalizer hcN)
  · have hTR' : T ≤ centralizer (R₁ : Set G) := by
      rw [commutator_eq_bot_iff_le_centralizer] at hTR
      exact hTR
    rw [hRc', centralizer_rightConjugate]
    exact map_mono hTR'

theorem card_sec3V (h32 : Lemma32) (h332 : Lemma33Two) {A R T : Subgroup G} {g : G}
    (hA : Hyp31 A) (eA : ↥A ≃* A5) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hg : g ∉ normalizer (A : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTR : T ≤ centralizer (R : Set G)) :
    Nat.card R = 4 ∧ Nat.card (R ⊔ T : Subgroup G) = 16 ∧ sec3V R T = R ⊔ T ∧
      Nat.card (sec3V R T ⊓ A : Subgroup G) = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVe, hVR, -⟩ := lemma35 h32 h332 hA hR hT hTR
  have hR4 := Lemma36.four_le_card hA hR
  have hRT := Lemma36.inf_eq_bot_of_not_mem hA hR hg hT
  obtain ⟨xT, hTx, -⟩ := Lemma36.exists_conj_eq hR hT
  have hRTV : R ⊔ T ≤ sec3V R T := le_sec3V_of ⟨xT, hTx⟩
  have hTcard : Nat.card T = Nat.card R := by rw [hTx, rightConjugate_card]
  have hsupRT : Nat.card (R ⊔ T : Subgroup G) = Nat.card R * Nat.card R := by
    rw [card_sup_eq_mul (hTR.trans (centralizer_le_normalizer _)) hRT, hTcard]
  have hVp : IsPGroup 2 ↥(sec3V R T) := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 v v.2)⟩
  have hW4 : Nat.card (sec3V R T ⊓ A : Subgroup G) ∣ 4 := by
    have hWp : IsPGroup 2 ↥((sec3V R T ⊓ A).subgroupOf A) :=
      (hVp.to_le inf_le_left).comap_subtype
    have h := card_dvd_four_of_isPGroup eA hWp
    rwa [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv] at h
  have hRW : R ⊓ (sec3V R T ⊓ A) = ⊥ := by
    rw [eq_bot_iff, ← inf_centralizer_eq_bot eA]
    exact fun x hx => mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hx).2).2, hR.le (mem_inf.mp hx).1⟩
  have hWR : sec3V R T ⊓ A ≤ normalizer (R : Set G) :=
    (inf_le_right.trans (le_centralizer_iff.mp hR.le)).trans (centralizer_le_normalizer _)
  have hsupRW : Nat.card (sec3V R T) =
      Nat.card R * Nat.card (sec3V R T ⊓ A : Subgroup G) := by
    conv_lhs => rw [hVR]
    exact card_sup_eq_mul hWR hRW
  have hle := Subgroup.card_le_of_le hRTV
  rw [hsupRT, hsupRW] at hle
  have hWle : Nat.card (sec3V R T ⊓ A : Subgroup G) ≤ 4 := Nat.le_of_dvd (by norm_num) hW4
  have hR4' : Nat.card R ≤ 4 :=
    Nat.le_of_mul_le_mul_left (hle.trans (Nat.mul_le_mul_left _ hWle)) (by omega)
  have hRc : Nat.card R = 4 := le_antisymm hR4' hR4
  have hWc : Nat.card (sec3V R T ⊓ A : Subgroup G) = 4 := by
    rw [hRc] at hle
    omega
  have hVc : Nat.card (sec3V R T) = 16 := by rw [hsupRW, hRc, hWc]
  have hRTc : Nat.card (R ⊔ T : Subgroup G) = 16 := by rw [hsupRT, hRc]
  exact ⟨hRc, hRTc, (eq_of_le_of_card_ge hRTV (by rw [hVc, hRTc])).symm, hWc⟩

theorem sup_inf_eq (h332 : Lemma33Two) {A R T : Subgroup G} (hA : Hyp31 A)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hVe : IsElemAbelian 2 (sec3V R T)) {x : G}
    (hx : rightConjugate R x ≤ sec3V R T) :
    rightConjugate R x ⊔ (sec3V R T ⊓ rightConjugate A x) = sec3V R T := by
  have hVp : IsPGroup 2 ↥(sec3V R T) := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 v v.2)⟩
  have hRxC : rightConjugate R x ≤ centralizer (rightConjugate A x : Set G) := by
    rw [centralizer_rightConjugate]
    exact map_mono hR.le
  have hVAK : sec3V R T ≤ rightConjugate A x ⊔ rightConjugate (centralizer (A : Set G)) x := by
    refine iSup₂_le fun z hz => ?_
    have hzV : rightConjugate R z ≤ sec3V R T := le_sec3V hz
    have hzc : rightConjugate R z ≤ centralizer (rightConjugate R x : Set G) :=
      (hzV.trans (le_centralizer_self_of_isElemAbelian hVe)).trans
        (centralizer_le fun v hv => hx hv)
    have hc : rightConjugate (rightConjugate R z) x⁻¹ ≤ centralizer (R : Set G) := by
      have h1 : centralizer (R : Set G) =
          rightConjugate (centralizer (rightConjugate R x : Set G)) x⁻¹ := by
        rw [← centralizer_rightConjugate, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]
      rw [h1]
      exact map_mono hzc
    have hle := conj_le_sup_centralizer h332 hA hR ⟨z * x⁻¹, by rw [rightConjugate_mul]⟩ hc
    calc rightConjugate R z = rightConjugate (rightConjugate (rightConjugate R z) x⁻¹) x := by
          rw [rightConjugate_mul, rightConjugate_mul]
          congr 1
          group
      _ ≤ rightConjugate (A ⊔ centralizer (A : Set G)) x := map_mono hle
      _ = rightConjugate A x ⊔ rightConjugate (centralizer (A : Set G)) x := Subgroup.map_sup _ _ _
  have hKxA : rightConjugate (centralizer (A : Set G)) x ≤
      normalizer (rightConjugate A x : Set G) := by
    rw [← centralizer_rightConjugate]
    exact centralizer_le_normalizer _
  have hVle : sec3V R T ≤ rightConjugate R x ⊔ rightConjugate A x :=
    le_sup_of_isSylowOf hKxA (AschbacherTheorem3.isSylowOf_rightConjugate hR x) hx hVp hVAK
  exact (eq_sup_inf_of_le_sup hx (hRxC.trans (centralizer_le_normalizer _)) hVle).symm

theorem star36 (h332 : Lemma33Two) {A R T : Subgroup G} (hA : Hyp31 A) (eA : ↥A ≃* A5)
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hVe : IsElemAbelian 2 (sec3V R T))
    (hR4 : Nat.card R = 4) (hV : Nat.card (sec3V R T) = 16) : Star36 A R (sec3V R T) := by
  intro x hx
  set V := sec3V R T with hVdef
  set P := V ⊓ rightConjugate A x with hPdef
  have eAx : ↥(rightConjugate A x) ≃* A5 := (conjEquiv A x).trans eA
  have hsup : rightConjugate R x ⊔ P = V := sup_inf_eq h332 hA hR hVe hx
  have hRxC : rightConjugate R x ≤ centralizer (rightConjugate A x : Set G) := by
    rw [centralizer_rightConjugate]
    exact map_mono hR.le
  have hPN : P ≤ normalizer (rightConjugate R x : Set G) :=
    (inf_le_right.trans (le_centralizer_iff.mp hRxC)).trans (centralizer_le_normalizer _)
  have hinf : rightConjugate R x ⊓ P = ⊥ := by
    rw [eq_bot_iff, ← inf_centralizer_eq_bot eAx]
    exact fun v hv => mem_inf.mpr ⟨(mem_inf.mp (mem_inf.mp hv).2).2, hRxC (mem_inf.mp hv).1⟩
  have hP4 : Nat.card P = 4 := by
    have h := card_sup_eq_mul hPN hinf
    rw [hsup, hV, rightConjugate_card, hR4] at h
    omega
  obtain ⟨y, hyA, hyP, hy3, htr, hnorm⟩ := exists_klein_three eAx inf_le_right hP4
  have hyR : y ∈ normalizer (rightConjugate R x : Set G) :=
    centralizer_le_normalizer _ (le_centralizer_iff.mp hRxC hyA)
  have hyV : y ∈ normalizer (V : Set G) := by
    rw [← hsup]
    exact mem_normalizer_sup hyR hyP
  have hPC : P ≤ centralizer (V : Set G) :=
    inf_le_left.trans (le_centralizer_self_of_isElemAbelian hVe)
  refine ⟨y, mem_inf.mpr ⟨hyA, hyV⟩, by rw [hy3]; decide, htr, fun z hz => ?_⟩
  obtain ⟨hzA, hzV⟩ := mem_inf.mp hz
  have hwA : z⁻¹ * y * z ∈ rightConjugate A x := by
    have h := (mem_normalizer_iff.mp (inv_mem hzA) y).mp hyA
    rwa [inv_inv] at h
  have hwV : z⁻¹ * y * z ∈ normalizer (V : Set G) := mul_mem (mul_mem (inv_mem hzV) hyV) hzV
  have hwP : z⁻¹ * y * z ∈ normalizer (P : Set G) :=
    mem_normalizer_inf hwV (le_normalizer hwA)
  have h := hnorm _ hwA hwP
  rw [sup_comm] at h
  exact (sup_le_sup_left hPC _) h

theorem case310Local_of (h32 : Lemma32) (h332 : Lemma33Two) {A R T : Subgroup G} {g : G}
    (hA : Hyp31 A) (eA : ↥A ≃* A5) (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hno : ∀ x : G, ¬ rightConjugate R x ≤ A) (hg : g ∉ normalizer (A : Set G))
    (hT : IsSylowOf 2 T (rightConjugate (centralizer (A : Set G)) g))
    (hTN : T ≤ normalizer (A : Set G)) (hTR : T ≤ centralizer (R : Set G)) :
    RankTwoClassical.Case310Local A R g T ((R ⊔ T) ⊓ A) := by
  obtain ⟨hR4, hRT16, hVeq, hW4⟩ := card_sec3V h32 h332 hA eA hR hg hT hTR
  obtain ⟨hVe, -, -⟩ := lemma35 h32 h332 hA hR hT hTR
  have hV16 : Nat.card (sec3V R T) = 16 := by rw [hVeq, hRT16]
  have hstar := star36 h332 hA eA hR hVe hR4 hV16
  obtain ⟨xT, hTx, hAx⟩ := Lemma36.exists_conj_eq hR hT
  have hcard : Nat.card R * Nat.card R ≤ Nat.card (sec3V R T) := by rw [hR4, hV16]
  have hcomm : ∀ x : G, rightConjugate R x ≤ sec3V R T →
      ⁅rightConjugate A x ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ =
        sec3V R T ⊓ rightConjugate A x := by
    intro x hx
    obtain ⟨y, hy, hodd, htr, -⟩ := hstar x hx
    exact (Lemma36.conjData h332 hA hR hVe hcard hR4.ge hx hy hodd htr).commutator_eq
  have hRV : R ≤ sec3V R T := hVeq ▸ le_sup_left
  have hTV : T ≤ sec3V R T := hVeq ▸ le_sup_right
  have hcA : ⁅A ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ = sec3V R T ⊓ A := by
    have h := hcomm 1 (by rw [rightConjugate_one]; exact hRV)
    rwa [rightConjugate_one] at h
  have hcAg : ⁅rightConjugate A g ⊓ normalizer (sec3V R T : Set G), sec3V R T⁆ =
      sec3V R T ⊓ rightConjugate A g := by
    have h := hcomm xT (hTx ▸ hTV)
    rwa [hAx] at h
  rcases lemma36 h32 h332 G A R T g hA hR hg hT hTR hstar with ⟨h1, -, -⟩ | ⟨h1, h2, h3⟩
  ·
    exfalso
    apply hno xT
    rw [← hTx, ← h1, hcA]
    exact inf_le_right
  rw [hcA, hcAg] at h1
  rw [hcA] at h2
  rw [hVeq] at h1 h2 h3 hVe
  have hspread : ∀ x : G, rightConjugate R x ≤ R ⊔ T →
      rightConjugate R x ⊓ ((R ⊔ T) ⊓ A) = ⊥ := by
    intro x hx
    rw [eq_bot_iff]
    intro v hv
    rw [mem_bot]
    by_contra hv1
    obtain ⟨hvR, hv0⟩ := mem_inf.mp hv
    exact (h2 v (hx hvR)).mpr ⟨x, hx, hvR, hv1⟩ hv0
  have hVp : IsPGroup 2 ↥(R ⊔ T) := fun v => ⟨1, Subtype.ext (by simpa using hVe.2 v v.2)⟩
  refine ⟨hg, hT, hTN, hTR, isSylowOf_four eA inf_le_right (by rw [← hVeq]; exact hW4),
    by rw [h1]; exact inf_le_right, hVe, hRT16, rfl, h1.symm, hspread, ?_, ?_, h3⟩
  · intro v hv hv0
    obtain ⟨x, hx, hvx, -⟩ := (h2 v hv).mp hv0
    exact ⟨x, hx, hvx⟩
  ·
    intro x
    rw [eq_bot_iff]
    intro v hv
    rw [mem_bot]
    by_contra hv1
    obtain ⟨hv0, hvK⟩ := mem_inf.mp hv
    have hvV : v ∈ R ⊔ T := (inf_le_left : (R ⊔ T) ⊓ A ≤ R ⊔ T) hv0
    have hKte := tightlyEmbedded_rightConjugate (tightlyEmbedded_centralizer hA.standard) x
    have hWp : IsPGroup 2 ↥((R ⊔ T) ⊓ rightConjugate (centralizer (A : Set G)) x) :=
      hVp.to_le inf_le_left
    have hW1 : (R ⊔ T) ⊓ rightConjugate (centralizer (A : Set G)) x ≠ ⊥ := fun h =>
      hv1 (by rw [← mem_bot, ← h]; exact mem_inf.mpr ⟨hvV, hvK⟩)
    have hVW : R ⊔ T ≤
        normalizer (((R ⊔ T) ⊓ rightConjugate (centralizer (A : Set G)) x : Subgroup G) : Set G) :=
      le_normalizer_of_le hVe inf_le_left le_rfl
    have hVN : R ⊔ T ≤ normalizer (rightConjugate A x : Set G) := by
      intro w hw
      have h := normalizer_two_subgroup_le _ _ hKte hWp inf_le_right hW1 (hVW hw)
      rw [mem_normalizer_rightConjugate_iff] at h ⊢
      rwa [← normalizer_centralizer_eq hA.standard]
    have eAx : ↥(rightConjugate A x) ≃* A5 := (conjEquiv A x).trans eA
    have hle := card_le_of_le_normalizer eAx hVN hVe
    rw [hRT16, centralizer_rightConjugate] at hle
    obtain ⟨S, hS, hWS⟩ := exists_isSylowOf_le
      (inf_le_right : (R ⊔ T) ⊓ rightConjugate (centralizer (A : Set G)) x ≤ _) hWp
    obtain ⟨h, -, hSh⟩ :=
      Lemma22.exists_conj_eq_of_isSylowOf (AschbacherTheorem3.isSylowOf_rightConjugate hR x) hS
    have hS' : S = rightConjugate R (x * h⁻¹) := by
      rw [hSh, ← rightConjugate_mul]
      change (rightConjugate R x).map (MulAut.conj h).toMonoidHom =
        (rightConjugate R x).map (MulAut.conj h⁻¹⁻¹).toMonoidHom
      rw [inv_inv]
    have hS4 : Nat.card S = 4 := by rw [hS', rightConjugate_card, hR4]
    have hWS' : (R ⊔ T) ⊓ rightConjugate (centralizer (A : Set G)) x = S :=
      eq_of_le_of_card_ge hWS (by rw [hS4]; omega)
    have hSV : rightConjugate R (x * h⁻¹) ≤ R ⊔ T := by
      rw [← hS', ← hWS']
      exact inf_le_left
    have hvS : v ∈ rightConjugate R (x * h⁻¹) := by
      rw [← hS', ← hWS']
      exact mem_inf.mpr ⟨hvV, hvK⟩
    have h0 := hspread (x * h⁻¹) hSV
    exact hv1 (by rw [← mem_bot, ← h0]; exact mem_inf.mpr ⟨hvS, hv0⟩)

end CFSG.ComponentClassification.RankTwoAltFive
