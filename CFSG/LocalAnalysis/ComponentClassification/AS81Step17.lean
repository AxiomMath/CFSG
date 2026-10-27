module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step17L2
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step17Aut
public import CFSG.LocalAnalysis.ComponentClassification.Asc75T4Conj
public import CFSG.LocalAnalysis.ComponentClassification.AS76bLemma35
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Setup

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoL3Four

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rightConjugate_sup (A B : Subgroup G) (g : G) :
    rightConjugate (A ⊔ B) g = rightConjugate A g ⊔ rightConjugate B g :=
  map_sup A B _

omit [Finite G] in
theorem rightConjugate_rightConjugate_inv_cancel (X : Subgroup G) (g : G) :
    rightConjugate (rightConjugate X g) g⁻¹ = X := by
  rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

omit [Finite G] in
theorem rightConjugate_le_normalizer_rightConjugate {E X : Subgroup G}
    (h : E ≤ normalizer (X : Set G)) (g : G) :
    rightConjugate E g ≤ normalizer (rightConjugate X g : Set G) := by
  intro e he
  rw [mem_rightConjugate_iff] at he
  rw [mem_normalizer_iff]
  intro x
  rw [mem_rightConjugate_iff, mem_rightConjugate_iff]
  have h1 := mem_normalizer_iff.mp (h he) (g * x * g⁻¹)
  have e1 : g * (e * x * e⁻¹) * g⁻¹ = (g * e * g⁻¹) * (g * x * g⁻¹) * (g * e * g⁻¹)⁻¹ := by group
  rw [e1]
  exact h1

theorem rightConjugate_mem_oddNStar {E X : Subgroup G} (hX : X ∈ oddNStar E) (g : G) :
    rightConjugate X g ∈ oddNStar (rightConjugate E g) := by
  obtain ⟨⟨hXo, hEX⟩, hmax⟩ := hX
  refine ⟨⟨by rw [rightConjugate_card]; exact hXo,
    rightConjugate_le_normalizer_rightConjugate hEX g⟩, fun Y ⟨hYo, hEY⟩ hXY => ?_⟩
  have h1 : rightConjugate Y g⁻¹ ≤ X := by
    refine hmax ⟨by rw [rightConjugate_card]; exact hYo, ?_⟩ ?_
    · have := rightConjugate_le_normalizer_rightConjugate hEY g⁻¹
      rwa [rightConjugate_rightConjugate_inv_cancel] at this
    · have := AschbacherTheorem3.rightConjugate_le_rightConjugate hXY g⁻¹
      rwa [rightConjugate_rightConjugate_inv_cancel] at this
  have := AschbacherTheorem3.rightConjugate_le_rightConjugate h1 g
  rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at this

theorem sq_eq_one_of_mem_center {A R : Subgroup G} (hR : IsSylowOf 2 R (centralizer (A : Set G)))
    (hRe : IsElemAbelian 2 R) :
    ∀ z ∈ center ↥A, IsPGroup 2 (zpowers z) → z ^ 2 = 1 := by
  intro z hz h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzK : (z : G) ∈ centralizer (A : Set G) := mem_centralizer_iff.mpr fun a ha =>
    congrArg Subtype.val (mem_center_iff.mp hz ⟨a, ha⟩)
  obtain ⟨n, hn⟩ := h2 ⟨z, mem_zpowers z⟩
  have hn' : (z : G) ^ 2 ^ n = 1 := by
    have := congrArg (fun w : ↥(zpowers z) => ((w : ↥A) : G)) hn
    simpa using this
  obtain ⟨a, haK, haz⟩ := AS76b.exists_conj_mem_of_isSylowOf hR hzK hn'
  have h1 : (a * (z : G) * a⁻¹) ^ 2 = 1 := hRe.2 _ haz
  rw [conj_pow, mul_inv_eq_one, mul_eq_left] at h1
  exact Subtype.ext (by simpa using h1)

theorem eq_oddCoreIn_of_mem_oddNStar (h4 : AS76b.Asc75Theorem4) {A R E : Subgroup G}
    (hstd : standardComponentIsStandard A) (hFs : IsSimpleGroup (CFSG.generalizedFitting G))
    (hKn : ¬ (centralizer (A : Set G)).Normal) (hL : TypeL34 (rankTwoQuot A))
    (hR : IsSylowOf 2 R (centralizer (A : Set G))) (hRe : IsElemAbelian 2 R)
    (hR4 : Nat.card R = 4) (hE : IsElemAbelian 2 E) (hE64 : Nat.card E = 64) (hRE : R ≤ E)
    (hEAR : E ≤ A ⊔ R) {X : Subgroup G} (hX : X ∈ oddNStar E) :
    X = AS76b.oddCoreIn (centralizer (A : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer (A : Set G) with hKdef
  set O := AS76b.oddCoreIn K with hOdef
  have hK := AS76b.tightlyEmbedded_centralizer hstd
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have hRK : R ≤ K := hR.le
  obtain ⟨⟨hXo, hEX⟩, hmax⟩ := hX
  have hX2 : ¬ 2 ∣ Nat.card X := fun h => (Nat.not_even_iff_odd.mpr hXo) (even_iff_two_dvd.mpr h)
  have hRX : R ≤ normalizer (X : Set G) := hRE.trans hEX
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hXNA : X ≤ normalizer (A : Set G) := by
    refine le_of_forall_inf_centralizer_le
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.isElementaryAbelian_of_sq_eq_one hRe.2)
      (by rw [hR4]; norm_num) hX2 hRX ?_
    intro r hr hr1 y hy
    rw [← hNK]
    exact RankTwoSporadic.mem_normalizer_of_commute_of_tightlyEmbedded hK (hRK hr) hr1
      (hRe.2 r hr) (mem_centralizer_singleton_iff.mp hy.2)
  have hEK : E ⊓ K = R := hR.eq_of_le (le_inf hRE hRK) inf_le_right
    ((AS81.isPGroup_two_of_isElemAbelian hE).to_le inf_le_left)
  have hZ₀ : E ⊓ A ⊓ K = R ⊓ A := by
    rw [inf_right_comm, hEK]
  have hRN : R ≤ normalizer ((E ⊓ A : Subgroup G) : Set G) := by
    intro r hr
    refine Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun x hx => ?_)
    exact hcommE x hx.1 r (hRE hr)
  have hsupE : (E ⊓ A) ⊔ R = E := by
    refine le_antisymm (sup_le inf_le_left hRE) fun e he => ?_
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_eq_mul_of_le_sup hRK hRE hEAR he
    exact mul_mem (mem_sup_left ha) (mem_sup_right hr)
  have hcardEA : Nat.card (E ⊓ A : Subgroup G) = 16 * Nat.card (E ⊓ A ⊓ K : Subgroup G) := by
    have h := card_sup_mul_card_inf hRN
    rw [hsupE, hE64, hR4, show (E ⊓ A) ⊓ R = R ⊓ A by
      rw [inf_right_comm, inf_eq_right.mpr hRE]] at h
    rw [hZ₀]
    omega
  have hq : CFSG.Open.IsQuasisimple ↥A := hstd.1
  have hZ := sq_eq_one_of_mem_center hR hRe
  have hEn : Nontrivial E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE64]
    norm_num
  have hXK : X ≤ K := by
    refine le_of_forall_inf_centralizer_hyperplane_le
      (CFSG.LocalAnalysis.ComponentInitial.FieldFourCover.isElementaryAbelian_of_sq_eq_one hE.2)
      hEn hX2 hEX ?_
    intro B hBE hB2 y hy
    have hyA := hXNA hy.1
    have hyo : Odd (orderOf y) := hXo.of_dvd_nat (Subgroup.orderOf_dvd_natCard X hy.1)
    refine mem_centralizer_of_odd_of_fix hq hL hZ (H := E ⊓ A) (B := B ⊓ A) inf_le_right
      (AS76b.IsElemAbelian.mono hE inf_le_left) hcardEA (inf_le_inf_right A hBE) ?_ hyA hyo ?_
    ·
      change 8 * Nat.card (B ⊓ A ⊓ K : Subgroup G) ≤ Nat.card (B ⊓ A : Subgroup G)
      have h1 : B.relIndex (E ⊓ A) ≤ 2 := by
        rw [← hB2]
        exact relIndex_le_of_le_right inf_le_left (by rw [hB2]; norm_num)
      have h2 := relIndex_mul_card B (E ⊓ A)
      rw [show B ⊓ (E ⊓ A) = B ⊓ A by rw [← inf_assoc, inf_eq_left.mpr hBE]] at h2
      have h3 : Nat.card (B ⊓ A ⊓ K : Subgroup G) ≤ Nat.card (E ⊓ A ⊓ K : Subgroup G) :=
        Subgroup.card_le_of_le (inf_le_inf_right K (inf_le_inf_right A hBE))
      have h4 : Nat.card (E ⊓ A : Subgroup G) ≤ 2 * Nat.card (B ⊓ A : Subgroup G) := by
        rw [← h2]
        exact Nat.mul_le_mul_right _ h1
      omega
    · intro b hb
      have := mem_centralizer_iff.mp hy.2 b hb.1
      rw [← this, mul_inv_cancel_right]
  have hKN : A ⊔ R ≤ normalizer (K : Set G) := by
    rw [hNK]
    exact sup_le le_normalizer (hRK.trans (Subgroup.centralizer_le_normalizer _))
  have hEO : E ≤ normalizer (O : Set G) :=
    (hEAR.trans hKN).trans (AS76b.normalizer_le_normalizer_oddCoreIn K)
  have hXO : X ≤ normalizer (O : Set G) := hXK.trans (AS76b.le_normalizer_oddCoreIn K)
  have hOX : O ≤ X := by
    have hP : Odd (Nat.card (O ⊔ X : Subgroup G)) := by
      have h := card_sup_mul_card_inf hXO
      have h1 : Nat.card (O ⊔ X : Subgroup G) ∣ Nat.card O * Nat.card X := ⟨_, h.symm⟩
      exact ((AS76b.odd_card_oddCoreIn K).mul hXo).of_dvd_nat h1
    have hEOX : E ≤ normalizer ((O ⊔ X : Subgroup G) : Set G) := by
      intro e he
      refine AS76b.mem_normalizer_of_map_conj_le ?_
      rw [Subgroup.map_sup]
      refine sup_le_sup ?_ ?_
      · rintro _ ⟨o, ho, rfl⟩
        exact (mem_normalizer_iff.mp (hEO he) o).mp ho
      · rintro _ ⟨x, hx, rfl⟩
        exact (mem_normalizer_iff.mp (hEX he) x).mp hx
    exact le_sup_left.trans (hmax ⟨hP, hEOX⟩ le_sup_right)
  have hXle : X ≤ O := le_oddCoreIn_of_le_normalizer h4 hK hR hRe (by rw [hR4]; norm_num) hFs hKn hXK hRX hXo
  exact le_antisymm hXle hOX

omit [Finite G] in
theorem not_normal_centralizer {A : Subgroup G} (hstd : standardComponentIsStandard A)
    (hA : ¬ A.Normal) : ¬ (centralizer (A : Set G)).Normal := by
  intro hK
  apply hA
  have hNK := AS76b.normalizer_centralizer_eq hstd
  rw [← normalizer_eq_top_iff] at hK ⊢
  rw [← hNK]
  exact hK

theorem step17a_of_frame (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) {A R : Subgroup G} {g : G}
    {E F : Subgroup G} (hF : Frame G A A R g E F) (hL : TypeL34 (rankTwoQuot A)) :
    ∀ X ∈ oddNStar E, X ≠ ⊥ →
      (∀ h ∈ normalizer (E : Set G),
        X = AS76b.oddCoreIn (centralizer (rightConjugate A h : Set G))) ∧
      normalizer (X : Set G) ≠ ⊤ ∧ A ≤ normalizer (X : Set G) ∧
      RankTwoHypNF ↥(normalizer (X : Set G)) (A.subgroupOf (normalizer (X : Set G))) := by
  intro X hX hX1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB := hF.base
  have hstd := hB.hyp.standard
  have hFs := (h34 G A hB.hyp31).2
  have hKn := not_normal_centralizer hstd hB.hyp.not_normal
  set K := centralizer (A : Set G) with hKdef
  have hNK := AS76b.normalizer_centralizer_eq hstd
  have core : ∀ E' : Subgroup G, IsElemAbelian 2 E' → Nat.card E' = 64 → R ≤ E' →
      E' ≤ A ⊔ R → ∀ Y ∈ oddNStar E', Y = AS76b.oddCoreIn K := fun E' h1 h2 h3 h5 Y hY =>
    eq_oddCoreIn_of_mem_oddNStar h4 hstd hFs hKn hL hF.sylowR hF.elemR hF.cardR h1 h2 h3 h5 hY
  have hXO := core E hF.elemE hF.cardE hF.R_le_E hF.E_le X hX
  have hAN : A ≤ normalizer (X : Set G) := by
    rw [hXO]
    intro a ha
    refine AS76b.normalizer_le_normalizer_oddCoreIn K ?_
    rw [hNK]
    exact le_normalizer ha
  refine ⟨fun h hh => ?_, ?_, hAN, ?_⟩
  ·
    have hEh : rightConjugate E h⁻¹ = E := (rightConjugate_eq_self_iff E h⁻¹).mpr (inv_mem hh)
    have h1 := rightConjugate_mem_oddNStar hX h⁻¹
    rw [hEh] at h1
    have h2 := core E hF.elemE hF.cardE hF.R_le_E hF.E_le _ h1
    calc X = rightConjugate (rightConjugate X h⁻¹) h := by
          rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
      _ = rightConjugate (AS76b.oddCoreIn K) h := by rw [h2]
      _ = AS76b.oddCoreIn (rightConjugate K h) := (Asc75T4.oddCoreIn_rightConjugate K h).symm
      _ = AS76b.oddCoreIn (centralizer (rightConjugate A h : Set G)) := by
          rw [AS76b.centralizer_rightConjugate]
  ·
    intro htop
    have hn : X.Normal := normalizer_eq_top_iff.mp htop
    have hle : X ≤ standardComponentOddCore G := le_sSup ⟨hn, hX.1.1⟩
    rw [hB.oddCore] at hle
    exact hX1 (le_bot_iff.mp hle)
  set N := normalizer (X : Set G) with hNdef
  have hRN : R ≤ N := by
    rw [hNdef, hXO]
    exact hF.sylowR.le.trans (AS76b.le_normalizer_oddCoreIn K)
  have heven : Even (Nat.card (centralizer (A : Set G) ⊓ N : Subgroup G)) := by
    have h4' : 4 ∣ Nat.card (K ⊓ N : Subgroup G) := by
      rw [← hF.cardR]
      exact Subgroup.card_dvd_of_le (le_inf hF.sylowR.le hRN)
    exact even_iff_two_dvd.mpr ((by norm_num : 2 ∣ 4).trans h4')
  have hstd₁ := GMS78.standard_subgroupOf hstd hAN heven
  have hgN : g ∈ N := by
    have hEg := le_sup_of_frame hE16 hF hL
    have hE'AR : rightConjugate E g⁻¹ ≤ A ⊔ R := by
      have := AschbacherTheorem3.rightConjugate_le_rightConjugate hEg g⁻¹
      rwa [rightConjugate_sup, rightConjugate_rightConjugate_inv_cancel,
        rightConjugate_rightConjugate_inv_cancel] at this
    have hRE' : R ≤ rightConjugate E g⁻¹ := by
      have hRgE : rightConjugate R g ≤ E := by
        have : rightConjugate R g ≤ E ⊓ F := by
          rw [hF.inf_eq]
          exact le_sup_right
        exact this.trans inf_le_left
      have := AschbacherTheorem3.rightConjugate_le_rightConjugate hRgE g⁻¹
      rwa [rightConjugate_rightConjugate_inv_cancel] at this
    have h1 := core _ (AS76b.isElemAbelian_rightConjugate hF.elemE g⁻¹)
      (by rw [rightConjugate_card]; exact hF.cardE) hRE' hE'AR _
      (rightConjugate_mem_oddNStar hX g⁻¹)
    have hXg : rightConjugate X g⁻¹ = X := h1.trans hXO.symm
    have : g⁻¹ ∈ N := (rightConjugate_eq_self_iff X g⁻¹).mp hXg
    simpa using inv_mem this
  have hnn : ¬ (A.subgroupOf N).Normal := by
    intro hn
    apply hF.not_mem
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨a, ha, rfl⟩
    have h1 := hn.conj_mem ⟨a, hAN ha⟩ (mem_subgroupOf.mpr ha) ⟨g, hgN⟩
    rw [mem_subgroupOf] at h1
    simpa using h1
  have hrank : 2 ≤ Open.pRank 2 (centralizer ((A.subgroupOf N : Subgroup ↥N) : Set ↥N)) := by
    refine CFSG.SectionRank.le_pRank one_lt_two (E := R.subgroupOf N) ?_
      (isElemAbelian_subgroupOf hF.elemR N) ?_
    · intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (mem_centralizer_iff.mp (hF.sylowR.le (mem_subgroupOf.mp hx)) y
        (mem_subgroupOf.mp hy))
    · rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hF.cardR]
      exact Nat.card_congr (subgroupOfEquivOfLe hRN).toEquiv
  exact ⟨hstd₁, hnn, hrank⟩

theorem step17_of (h4 : AS76b.Asc75Theorem4) (h34 : AS76b.Asc08Lemma34)
    {d : L34E16Cert}
    (hE16 : RankTwoL3Four.HypII.l34CheckWE16 d = true) : Step17 := by
  intro G _ _ A R g E F hF hL hbelow X hX hX1
  obtain ⟨hconj, hNtop, hAN, hH⟩ := step17a_of_frame h4 h34 hE16 hF hL X hX hX1
  refine ⟨hconj, hAN, ?_⟩
  have hcard : Nat.card (normalizer (X : Set G)) < Nat.card G := by
    have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hNtop)
    rwa [card_top] at this
  let eA : ↥(A.subgroupOf (normalizer (X : Set G))) ≃* ↥A := subgroupOfEquivOfLe hAN
  have hL₁ : TypeL34 (rankTwoQuot (A.subgroupOf (normalizer (X : Set G)))) :=
    statedClassicalModel_of_mulEquiv
      (QuotientGroup.congr (center _) (center _) eA (Subgroup.map_center_eq eA)) hL
  exact hbelow _ _ hcard hH hL₁

end CFSG.ComponentClassification.AS81
