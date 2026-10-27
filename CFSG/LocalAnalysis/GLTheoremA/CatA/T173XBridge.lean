module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172XInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS10I1416Chev2
public import CFSG.LocalAnalysis.GLTheoremA.S10.CatDistinct
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridgePlus
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172BInner
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CInner
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110m
import CFSG.LocalAnalysis.GLTheoremA.CatA.HSubTCompU6
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173Facts
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDOdd

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173X

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S10 CFSG.LocalAnalysis.GLTheoremA.T173

private theorem exists_isOmPA_of_chevTwo_aux1 (n Q : ℕ) (hQ : Odd Q) :
    Q ^ (n * (n - 1)) ∣ orderD n Q := by
  have hg : Nat.gcd 4 (Q ^ n - 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hcop : Nat.Coprime Q 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_pow_right_iff (by norm_num) Q 2).2 hQ.coprime_two_right
  have hcopg : Nat.Coprime (Q ^ (n * (n - 1))) (Nat.gcd 4 (Q ^ n - 1)) :=
    (hcop.coprime_dvd_right hg).pow_left _
  have hGd : Nat.gcd 4 (Q ^ n - 1) ∣ Q ^ (n * (n - 1)) * ((Q ^ n - 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (Q ^ n - 1) * orderD n Q =
      Q ^ (n * (n - 1)) * ((Q ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by
    have h1 : Q ^ (n * (n - 1)) * (Q ^ n - 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1) =
        Q ^ (n * (n - 1)) * ((Q ^ n - 1) *
          ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by ring
    unfold orderD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have hdvd : Q ^ (n * (n - 1)) ∣ Nat.gcd 4 (Q ^ n - 1) * orderD n Q := by
    rw [hmul]
    exact dvd_mul_right _ _
  exact hcopg.dvd_of_dvd_mul_left hdvd

theorem exists_isOmPA_of_chevTwo (hb : CatDistinct.OrderBridge) (hOdd : Chev2OddAmb) {X : Type} [Group X] [Finite X]
    (hchev : IsChevSimple 2 X) (hX : catalogIs X (onLie T173ClassD)) :
    ∃ l f : ℕ, 4 ≤ l ∧ 1 ≤ f ∧ catalogIs X (isOmPA l (2 ^ f)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hX
  rcases i with _ | ⟨n, hn⟩ | d | _
  · exact absurd hi (by simp [onLie, T173ClassD])
  · exact absurd hi (by simp [onLie, T173ClassD])
  · obtain ⟨dd, hv⟩ := d
    cases dd with
    | D r q =>
      have hr : 4 ≤ r := by
        have h := ((TauCeti.LieTypeIndex.valid_iff (TauCeti.LieTypeIndex.D r q)).1 hv).1
        simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
      by_cases hq2 : q.p = 2
      · refine ⟨r, q.exponent, hr, Nat.succ_le_of_lt q.exponent_pos, ?_⟩
        refine ⟨TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩, Or.inl ?_, ⟨e⟩⟩
        change r = r ∧ q.card = 2 ^ q.exponent
        exact ⟨rfl, by rw [TauCeti.PrimePower.card_def, hq2]⟩
      · exfalso
        have hChevS : IsChevSimple q.p X :=
          Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩, by
            simp [onLie, TauCeti.LieTypeIndex.characteristic_D], ⟨e⟩⟩
        have hsmall : catalogIs X chev2Small := hOdd q.p X q.prime_p hq2 hchev hChevS
        have hle : Nat.card X ≤ 25920 :=
          CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110m.card_le_of_catalogIs_chev2Spor_d4cls
            hb (catalogIs_chev2Spor_of_small hsmall)
        have hQodd : Odd q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact (q.prime_p.eq_two_or_odd'.resolve_left hq2).pow
        have hcard : Nat.card X = orderD r q.card := hb ⟨.D r q, hv⟩ X ⟨e⟩
        have hdvd : q.card ^ 12 ∣ Nat.card X := by
          rw [hcard]
          have h12 : 12 ≤ r * (r - 1) := by
            have h3 : 3 ≤ r - 1 := by omega
            calc 12 = 4 * 3 := by norm_num
              _ ≤ r * (r - 1) := Nat.mul_le_mul hr h3
          exact (pow_dvd_pow q.card h12).trans (exists_isOmPA_of_chevTwo_aux1 r q.card hQodd)
        have h3 : 3 ≤ q.card := by
          rw [TauCeti.PrimePower.card_def]
          have hp3 : 3 ≤ q.p := by have h2 := q.prime_p.two_le; omega
          exact le_trans hp3 (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.p)
        have hge : 3 ^ 12 ≤ Nat.card X :=
          le_trans (Nat.pow_le_pow_left h3 12) (Nat.le_of_dvd (Nat.card_pos_iff.2 ⟨⟨1⟩, inferInstance⟩) hdvd)
        norm_num at hge
        omega
    | _ => exact absurd hi (by simp [onLie, T173ClassD])
  · exact absurd hi (by simp [onLie, T173ClassD])

private theorem exists_isOmMA_of_chevTwo_aux1 (n Q : ℕ) (hQ : Odd Q) :
    Q ^ (n * (n - 1)) ∣ orderTwistedD n Q := by
  have hg : Nat.gcd 4 (Q ^ n + 1) ∣ 4 := Nat.gcd_dvd_left _ _
  have hcop : Nat.Coprime Q 4 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
    exact (Nat.coprime_pow_right_iff (by norm_num) Q 2).2 hQ.coprime_two_right
  have hcopg : Nat.Coprime (Q ^ (n * (n - 1))) (Nat.gcd 4 (Q ^ n + 1)) :=
    (hcop.coprime_dvd_right hg).pow_left _
  have hGd : Nat.gcd 4 (Q ^ n + 1) ∣ Q ^ (n * (n - 1)) * ((Q ^ n + 1) *
      ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) :=
    Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.gcd_dvd_right _ _) _) _
  have hmul : Nat.gcd 4 (Q ^ n + 1) * orderTwistedD n Q =
      Q ^ (n * (n - 1)) * ((Q ^ n + 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by
    have h1 : Q ^ (n * (n - 1)) * (Q ^ n + 1) *
        ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1) =
        Q ^ (n * (n - 1)) * ((Q ^ n + 1) *
          ∏ i ∈ Finset.Icc 1 (n - 1), (Q ^ (2 * i) - 1)) := by ring
    unfold orderTwistedD
    rw [h1]
    exact Nat.mul_div_cancel' hGd
  have hdvd : Q ^ (n * (n - 1)) ∣ Nat.gcd 4 (Q ^ n + 1) * orderTwistedD n Q := by
    rw [hmul]
    exact dvd_mul_right _ _
  exact hcopg.dvd_of_dvd_mul_left hdvd

theorem exists_isOmMA_of_chevTwo (hb : CatDistinct.OrderBridge) (hOdd : Chev2OddAmb) {X : Type} [Group X] [Finite X]
    (hchev : IsChevSimple 2 X) (hX : catalogIs X (onLie T173ClassTD)) :
    ∃ l f : ℕ, 4 ≤ l ∧ 1 ≤ f ∧ catalogIs X (isOmMA l (2 ^ f)) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := hX
  rcases i with _ | ⟨n, hn⟩ | d | _
  · exact absurd hi (by simp [onLie, T173ClassTD])
  · exact absurd hi (by simp [onLie, T173ClassTD])
  · obtain ⟨dd, hv⟩ := d
    cases dd with
    | twistedD r q =>
      have hr : 4 ≤ r := by
        have h := ((TauCeti.LieTypeIndex.valid_iff (TauCeti.LieTypeIndex.twistedD r q)).1 hv).1
        simpa [TauCeti.LieTypeIndex.inStandardRange_iff] using h
      by_cases hq2 : q.p = 2
      · refine ⟨r, q.exponent, hr, Nat.succ_le_of_lt q.exponent_pos, ?_⟩
        refine ⟨TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩, Or.inl ?_, ⟨e⟩⟩
        change r = r ∧ q.card = 2 ^ q.exponent
        exact ⟨rfl, by rw [TauCeti.PrimePower.card_def, hq2]⟩
      · exfalso
        have hChevS : IsChevSimple q.p X :=
          Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩, by
            simp [onLie, TauCeti.LieTypeIndex.characteristic_D], ⟨e⟩⟩
        have hsmall : catalogIs X chev2Small := hOdd q.p X q.prime_p hq2 hchev hChevS
        have hle : Nat.card X ≤ 25920 :=
          CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110m.card_le_of_catalogIs_chev2Spor_d4cls
            hb (catalogIs_chev2Spor_of_small hsmall)
        have hQodd : Odd q.card := by
          rw [TauCeti.PrimePower.card_def]
          exact (q.prime_p.eq_two_or_odd'.resolve_left hq2).pow
        have hcard : Nat.card X = orderTwistedD r q.card := hb ⟨.twistedD r q, hv⟩ X ⟨e⟩
        have hdvd : q.card ^ 12 ∣ Nat.card X := by
          rw [hcard]
          have h12 : 12 ≤ r * (r - 1) := by
            have h3 : 3 ≤ r - 1 := by omega
            calc 12 = 4 * 3 := by norm_num
              _ ≤ r * (r - 1) := Nat.mul_le_mul hr h3
          exact (pow_dvd_pow q.card h12).trans (exists_isOmMA_of_chevTwo_aux1 r q.card hQodd)
        have h3 : 3 ≤ q.card := by
          rw [TauCeti.PrimePower.card_def]
          have hp3 : 3 ≤ q.p := by have h2 := q.prime_p.two_le; omega
          exact le_trans hp3 (Nat.le_self_pow (Nat.ne_of_gt q.exponent_pos) q.p)
        have hge : 3 ^ 12 ≤ Nat.card X :=
          le_trans (Nat.pow_le_pow_left h3 12) (Nat.le_of_dvd (Nat.card_pos_iff.2 ⟨⟨1⟩, inferInstance⟩) hdvd)
        norm_num at hge
        omega
    | _ => exact absurd hi (by simp [onLie, T173ClassTD])
  · exact absurd hi (by simp [onLie, T173ClassTD])

theorem nontrivial_of_isOmPA {X : Type} [Group X] {l q : ℕ} (hl : 4 ≤ l) (h : catalogIs X (isOmPA l q)) :
    Nontrivial X := by
  obtain ⟨i0, hi0, ⟨eCat⟩⟩ := h
  rcases hi0 with hi0 | ⟨h3, -⟩
  · let P : TauCeti.LieTypeIndex → Prop := fun d => ∃ hv : d.Valid, isOmP l q (.lie ⟨d, hv⟩)
    have hS_onLie : catalogIs X (onLie P) := by
      refine ⟨i0, ?_, ⟨eCat⟩⟩
      cases i0 with
      | cyclic a b => simp [isOmP, onLie] at hi0
      | alternating a b => simp [isOmP, onLie] at hi0
      | sporadic s => simp [isOmP, onLie] at hi0
      | lie idx => exact ⟨idx.2, hi0⟩
    obtain ⟨d, hv, hPd, ⟨e0⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS_onLie
    cases d with
    | D r q' =>
      exact (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
        X r q'.p q'.exponent
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD r q' hv e0)).1
    | _ => simp [P, isOmP, onLie] at hPd
  · omega

theorem nontrivial_of_isOmMA {X : Type} [Group X] {l q : ℕ} (hl : 4 ≤ l) (h : catalogIs X (isOmMA l q)) :
    Nontrivial X := by
  obtain ⟨i0, hi0, ⟨eCat⟩⟩ := h
  rcases hi0 with hi0 | ⟨h3, -⟩
  · let P : TauCeti.LieTypeIndex → Prop := fun d => ∃ hv : d.Valid, isOmM l q (.lie ⟨d, hv⟩)
    have hS_onLie : catalogIs X (onLie P) := by
      refine ⟨i0, ?_, ⟨eCat⟩⟩
      cases i0 with
      | cyclic a b => simp [isOmM, onLie] at hi0
      | alternating a b => simp [isOmM, onLie] at hi0
      | sporadic s => simp [isOmM, onLie] at hi0
      | lie idx => exact ⟨idx.2, hi0⟩
    obtain ⟨d, hv, hPd, ⟨e0⟩⟩ := CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS_onLie
    cases d with
    | twistedD r q' =>
      exact (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus
        X r q'.p q'.exponent
        (CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD r q' hv e0)).1
    | _ => simp [P, isOmM, onLie] at hPd
  · omega

private theorem splits_of_isOmPA_aux1 {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {p n k : ℕ} (hqs : CFSG.Open.IsQuasisimple ↥S) (hn : 4 ≤ n)
    (hS : catalogIs (PSimple p S) (isOmPA n (2 ^ k))) :
    StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .POmegaPlus n 2 k := by
  obtain ⟨i0, hi0, ⟨eCat⟩⟩ := hS
  let P : TauCeti.LieTypeIndex → Prop :=
    fun d => ∃ hv : d.Valid, isOmP n (2 ^ k) (.lie ⟨d, hv⟩)
  have hS_onLie : catalogIs (PSimple p S) (onLie P) := by
    refine ⟨i0, ?_, ⟨eCat⟩⟩
    rcases hi0 with h1 | ⟨hn3, -⟩
    · cases i0 with
      | cyclic a b => simp [isOmP, onLie] at h1
      | alternating a b => simp [isOmP, onLie] at h1
      | sporadic s => simp [isOmP, onLie] at h1
      | lie idx => exact ⟨idx.2, h1⟩
    · omega
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaPlus n 2 k := by
    obtain ⟨d, hv, hPd, ⟨e0⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS_onLie
    cases d with
    | D r q =>
      obtain ⟨hv', hPd'⟩ := hPd
      have hrq : r = n ∧ q.card = 2 ^ k := by simpa [isOmP, onLie] using hPd'
      obtain ⟨hr, hqc⟩ := hrq
      have hcard2 : 2 ≤ q.card := q.isPrimePow_card.two_le
      have hkpos : k ≠ 0 := by
        intro hk
        subst hk
        rw [pow_zero] at hqc
        omega
      have hpow : q.p ^ q.exponent = 2 ^ k := by
        rw [← TauCeti.PrimePower.card_def, hqc]
      obtain ⟨hq2, hqexp⟩ :=
        Nat.Prime.pow_inj' q.prime_p Nat.prime_two (Nat.ne_of_gt q.exponent_pos) hkpos hpow
      have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq2 e0
      simpa [hr, hq2, hqexp] using hM
    | _ => simp [P, isOmP, onLie] at hPd
  have hnt : Nontrivial (PSimple p S) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
      (PSimple p S) n 2 k hmodel).1
  obtain ⟨ePZ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter p S hqs hnt
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ePZ hmodel

private theorem splits_of_isOmPA_aux2 {n k : ℕ} (hn : 4 ≤ n) :
    ∀ lab : CFSG.Assembly.LargeEvenLabel,
      CFSG.StandardType.GGLabelIso lab ⟨.D, n, k⟩ → lab = ⟨.D, n, k⟩ := by
  intro lab h
  obtain ⟨t, r, m⟩ := lab
  unfold CFSG.StandardType.GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem splits_of_isOmPA_aux3 {p l f : ℕ}
    (h : GLASplit16 p (⟨.D, l, f⟩ : CFSG.Assembly.LargeEvenLabel)) :
    p ∣ 2 ^ f - 1 ∨ (f = 1 ∧ p = 3) := by
  rw [GLASplit16, CFSG.Assembly.LargeEvenSplit16] at h
  rcases h with h | h | h | h
  · exact Or.inl h.2
  · exact absurd h.1 (by simp [CFSG.Assembly.LargeEvenUntwisted])
  · rcases h.1 with h' | h' | h' | h'
    all_goals simp at h'
  · exact Or.inr h

theorem splits_of_isOmPA (hRig : CFSG.StandardType.GGLabelRigidInput) {Ω : Type} [Group Ω] [Finite Ω]
    {S B : Subgroup Ω} {p l f : ℕ} (hqs : CFSG.Open.IsQuasisimple ↥S) (hl : 4 ≤ l) (hf : 1 ≤ f)
    (hS : catalogIs (PSimple p S) (isOmPA l (2 ^ f))) (hsplit : SplitInnerDiagMarking16 p B S) :
    p ∣ 2 ^ f - 1 ∨ (f = 1 ∧ p = 3) := by
  have hqs' : CFSG.IsQuasisimple ↥S :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open hqs
  have hmodelZ := splits_of_isOmPA_aux1 hqs hl hS
  have hHasTarget : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥S (· = ⟨.D, l, f⟩) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_statedClassicalModel_POmegaPlus hqs' hmodelZ
  obtain ⟨-, lab, hlab, hraw⟩ := hsplit
  obtain ⟨labT, hlabT, hHasLabTarget, R0, hR0, I0, F0, θ0, hPeq⟩ :=
    CFSG.StandardType.largeEvenMarking_exists_hasLabel hHasTarget
  subst hPeq
  have hHasLab : CFSG.StandardType.GGHasLabel lab (↥S ⧸ Subgroup.center ↥S) := by
    unfold CFSG.StandardType.GGHasLabel
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hIso : CFSG.StandardType.GGLabelIso lab ⟨.D, l, f⟩ :=
    hRig lab ⟨.D, l, f⟩ (↥S ⧸ Subgroup.center ↥S) hlab hlabT hHasLab hHasLabTarget
  have hlab_eq : lab = ⟨.D, l, f⟩ := splits_of_isOmPA_aux2 hl lab hIso
  subst hlab_eq
  obtain ⟨R, _, I, F, hcont⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hsplit16, -⟩ := hcont
  exact splits_of_isOmPA_aux3 hsplit16

private theorem splits_of_isOmMA_aux1 {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {p n k : ℕ} (hqs : CFSG.Open.IsQuasisimple ↥S) (hn : 4 ≤ n)
    (hS : catalogIs (PSimple p S) (isOmMA n (2 ^ k))) :
    StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .POmegaMinus n 2 k := by
  obtain ⟨i0, hi0, ⟨eCat⟩⟩ := hS
  let P : TauCeti.LieTypeIndex → Prop :=
    fun d => ∃ hv : d.Valid, isOmM n (2 ^ k) (.lie ⟨d, hv⟩)
  have hS_onLie : catalogIs (PSimple p S) (onLie P) := by
    refine ⟨i0, ?_, ⟨eCat⟩⟩
    rcases hi0 with h1 | ⟨hn3, -⟩
    · cases i0 with
      | cyclic a b => simp [isOmM, onLie] at h1
      | alternating a b => simp [isOmM, onLie] at h1
      | sporadic s => simp [isOmM, onLie] at h1
      | lie idx => exact ⟨idx.2, h1⟩
    · omega
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaMinus n 2 k := by
    obtain ⟨d, hv, hPd, ⟨e0⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS_onLie
    cases d with
    | twistedD r q =>
      obtain ⟨hv', hPd'⟩ := hPd
      have hrq : r = n ∧ q.card = 2 ^ k := by simpa [isOmM, onLie] using hPd'
      obtain ⟨hr, hqc⟩ := hrq
      have hcard2 : 2 ≤ q.card := q.isPrimePow_card.two_le
      have hkpos : k ≠ 0 := by
        intro hk
        subst hk
        rw [pow_zero] at hqc
        omega
      have hpow : q.p ^ q.exponent = 2 ^ k := by
        rw [← TauCeti.PrimePower.card_def, hqc]
      obtain ⟨hq2, hqexp⟩ :=
        Nat.Prime.pow_inj' q.prime_p Nat.prime_two (Nat.ne_of_gt q.exponent_pos) hkpos hpow
      have hM :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq2 e0
      simpa [hr, hq2, hqexp] using hM
    | _ => simp [P, isOmM, onLie] at hPd
  have hnt : Nontrivial (PSimple p S) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus
      (PSimple p S) n 2 k hmodel).1
  obtain ⟨ePZ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter p S hqs hnt
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ePZ hmodel

private theorem splits_of_isOmMA_aux2 {n k : ℕ} (hn : 4 ≤ n) :
    ∀ lab : CFSG.Assembly.LargeEvenLabel,
      CFSG.StandardType.GGLabelIso lab ⟨.twD, n, k⟩ → lab = ⟨.twD, n, k⟩ := by
  intro lab h
  obtain ⟨t, r, m⟩ := lab
  unfold CFSG.StandardType.GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

private theorem splits_of_isOmMA_aux3 {p l f : ℕ}
    (h : GLASplit16 p (⟨.twD, l, f⟩ : CFSG.Assembly.LargeEvenLabel)) :
    p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1 := by
  rw [GLASplit16, CFSG.Assembly.LargeEvenSplit16] at h
  rcases h with h | h | h | h
  · exact absurd h.1 (by simp [CFSG.Assembly.LargeEvenUntwisted])
  · exact Or.inr h.2.2.2
  · exact Or.inl h.2
  · have hf1 : f = 1 := h.1
    have hp3 : p = 3 := h.2
    subst hf1
    subst hp3
    norm_num

theorem splits_of_isOmMA (hRig : CFSG.StandardType.GGLabelRigidInput) {Ω : Type} [Group Ω] [Finite Ω]
    {S B : Subgroup Ω} {p l f : ℕ} (hqs : CFSG.Open.IsQuasisimple ↥S) (hl : 4 ≤ l) (hf : 1 ≤ f)
    (hS : catalogIs (PSimple p S) (isOmMA l (2 ^ f))) (hsplit : SplitInnerDiagMarking16 p B S) :
    p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1 := by
  have hqs' : CFSG.IsQuasisimple ↥S :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open hqs
  have hmodelZ := splits_of_isOmMA_aux1 hqs hl hS
  have hHasTarget : CFSG.LocalAnalysis.GLTheoremA.Y10F.HasLabel ↥S (· = ⟨.twD, l, f⟩) :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.hasLabel_of_statedClassicalModel_POmegaMinus hqs' hmodelZ
  obtain ⟨-, lab, hlab, hraw⟩ := hsplit
  obtain ⟨labT, hlabT, hHasLabTarget, R0, hR0, I0, F0, θ0, hPeq⟩ :=
    CFSG.StandardType.largeEvenMarking_exists_hasLabel hHasTarget
  subst hPeq
  have hHasLab : CFSG.StandardType.GGHasLabel lab (↥S ⧸ Subgroup.center ↥S) := by
    unfold CFSG.StandardType.GGHasLabel
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨-, -, θ, -⟩
    exact ⟨θ⟩
  have hIso : CFSG.StandardType.GGLabelIso lab ⟨.twD, l, f⟩ :=
    hRig lab ⟨.twD, l, f⟩ (↥S ⧸ Subgroup.center ↥S) hlab hlabT hHasLab hHasLabTarget
  have hlab_eq : lab = ⟨.twD, l, f⟩ := splits_of_isOmMA_aux2 hl lab hIso
  subst hlab_eq
  obtain ⟨R, _, I, F, hcont⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hsplit16, -⟩ := hcont
  exact splits_of_isOmMA_aux3 hsplit16

private theorem isPGroup_two_center_of_isOmPA_aux1 {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {p n k : ℕ} (hqs : CFSG.Open.IsQuasisimple ↥S) (hn : 4 ≤ n)
    (hS : catalogIs (PSimple p S) (isOmPA n (2 ^ k))) :
    StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .POmegaPlus n 2 k := by
  obtain ⟨i0, hi0, ⟨eCat⟩⟩ := hS
  let P : TauCeti.LieTypeIndex → Prop :=
    fun d => ∃ hv : d.Valid, isOmP n (2 ^ k) (.lie ⟨d, hv⟩)
  have hS_onLie : catalogIs (PSimple p S) (onLie P) := by
    refine ⟨i0, ?_, ⟨eCat⟩⟩
    rcases hi0 with h1 | ⟨hn3, -⟩
    · cases i0 with
      | cyclic a b => simp [isOmP, onLie] at h1
      | alternating a b => simp [isOmP, onLie] at h1
      | sporadic s => simp [isOmP, onLie] at h1
      | lie idx => exact ⟨idx.2, h1⟩
    · omega
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaPlus n 2 k := by
    obtain ⟨d, hv, hPd, ⟨e0⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS_onLie
    cases d with
    | D r q =>
      obtain ⟨hv', hPd'⟩ := hPd
      have hrq : r = n ∧ q.card = 2 ^ k := by simpa [isOmP, onLie] using hPd'
      obtain ⟨hr, hqc⟩ := hrq
      have hcard2 : 2 ≤ q.card := q.isPrimePow_card.two_le
      have hkpos : k ≠ 0 := by
        intro hk
        subst hk
        rw [pow_zero] at hqc
        omega
      have hpow : q.p ^ q.exponent = 2 ^ k := by
        rw [← TauCeti.PrimePower.card_def, hqc]
      obtain ⟨hq2, hqexp⟩ :=
        Nat.Prime.pow_inj' q.prime_p Nat.prime_two (Nat.ne_of_gt q.exponent_pos) hkpos hpow
      have hM := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq2 e0
      simpa [hr, hq2, hqexp] using hM
    | _ => simp [P, isOmP, onLie] at hPd
  have hnt : Nontrivial (PSimple p S) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaPlus
      (PSimple p S) n 2 k hmodel).1
  obtain ⟨ePZ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter p S hqs hnt
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ePZ hmodel

private theorem isPGroup_two_center_of_isOmPA_aux3 {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} (hqs : CFSG.Open.IsQuasisimple ↥S) (Z₂ : Subgroup ↥S) [Z₂.Normal]
    (hZ₂ : Z₂ ≤ Subgroup.center ↥S) (P : Sylow 2 (Subgroup.center ↥S))
    (hZ₂eq : Z₂ = (P : Subgroup (Subgroup.center ↥S)).map (Subgroup.center ↥S).subtype) :
    Odd (Nat.card (Subgroup.center (↥S ⧸ Z₂))) := by
  classical
  let Z : Subgroup ↥S := Subgroup.center ↥S
  have hZ₂le : Z₂ ≤ Z := hZ₂
  haveI : Group.IsPerfect ↥S := ⟨hqs.1⟩
  let ψ : ↥S →* ↥S ⧸ Z₂ := QuotientGroup.mk' Z₂
  have hcenterL : Z.map ψ = Subgroup.center (↥S ⧸ Z₂) :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel ψ
      (QuotientGroup.mk'_surjective Z₂) (by rw [QuotientGroup.ker_mk']; exact hZ₂le)
  have hPsub : Z₂.subgroupOf Z = P := by
    rw [hZ₂eq, ← Subgroup.comap_subtype]
    exact Subgroup.comap_map_eq_self_of_injective Z.subtype_injective (P : Subgroup Z)
  have hkercomp : (ψ.comp Z.subtype).ker = Z₂.subgroupOf Z := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : ↥S)
  have hrange : (ψ.comp Z.subtype).range = Z.map ψ := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hcenterL]
  have hiso : Z ⧸ (Z₂.subgroupOf Z) ≃* Z.map ψ :=
    (QuotientGroup.quotientMulEquivOfEq hkercomp.symm).trans
      ((QuotientGroup.quotientKerEquivRange (ψ.comp Z.subtype)).trans
        (MulEquiv.subgroupCongr hrange))
  rw [← Nat.card_congr hiso.toEquiv, ← Subgroup.index_eq_card, hPsub]
  exact Nat.not_even_iff_odd.mp (by rw [even_iff_two_dvd]; exact P.not_dvd_index)

private theorem isPGroup_two_center_of_isOmPA_aux2
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hqs : CFSG.Open.IsQuasisimple ↥S) {l f : ℕ}
    (hmodelZ : StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .POmegaPlus l 2 f) :
    IsPGroup 2 (Subgroup.center ↥S) := by
  classical
  let Z : Subgroup ↥S := Subgroup.center ↥S
  let P : Sylow 2 Z := default
  let Z₂ : Subgroup ↥S := (P : Subgroup Z).map Z.subtype
  have hZ₂le : Z₂ ≤ Z := Subgroup.map_subtype_le (P : Subgroup Z)
  haveI : Z₂.Normal := Subgroup.normal_of_le_center hZ₂le
  haveI : Z.Normal := Subgroup.normal_of_le_center (le_refl Z)
  let ψ : ↥S →* ↥S ⧸ Z₂ := QuotientGroup.mk' Z₂
  haveI : Group.IsPerfect ↥S := ⟨hqs.1⟩
  have hLq : CFSG.IsQuasisimple (↥S ⧸ Z₂) :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open
      (CFSG.ComponentClassification.Quasisimple.central_quotient hqs Z₂ hZ₂le)
  have hcenterL : Z.map ψ = Subgroup.center (↥S ⧸ Z₂) :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel ψ
      (QuotientGroup.mk'_surjective Z₂) (by rw [QuotientGroup.ker_mk']; exact hZ₂le)
  have hmodelQ : StatedClassicalModel ((↥S ⧸ Z₂) ⧸ Subgroup.center (↥S ⧸ Z₂)) .POmegaPlus l 2 f := by
    haveI : (Z.map ψ).Normal := by rw [hcenterL]; infer_instance
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.congr (Z.map ψ) (Subgroup.center (↥S ⧸ Z₂)) (MulEquiv.refl _)
        (by simpa using hcenterL)).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient Z₂ Z hZ₂le)).symm hmodelZ
  have hodd : Odd (Nat.card (Subgroup.center (↥S ⧸ Z₂))) :=
    isPGroup_two_center_of_isOmPA_aux3 hqs Z₂ hZ₂le P rfl
  have hZbot : Subgroup.center (↥S ⧸ Z₂) = ⊥ :=
    (CFSG.SectionRank.EvenCover.even_split_orthogonal_odd_cover_catalog_step hLq hodd hmodelQ).1
  have hZle : Z ≤ Z₂ := by
    have hmapbot : Z.map ψ = ⊥ := hcenterL.trans hZbot
    rw [Subgroup.map_eq_bot_iff] at hmapbot
    rwa [QuotientGroup.ker_mk'] at hmapbot
  change IsPGroup 2 Z
  exact (le_antisymm hZle hZ₂le).symm ▸ (P.isPGroup'.map Z.subtype)

theorem isPGroup_two_center_of_isOmPA
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hqs : CFSG.Open.IsQuasisimple ↥S) {p l f : ℕ} (hl : 4 ≤ l) (hf : 1 ≤ f)
    (hS : catalogIs (PSimple p S) (isOmPA l (2 ^ f))) : IsPGroup 2 (Subgroup.center ↥S) :=
  isPGroup_two_center_of_isOmPA_aux2 hqs (isPGroup_two_center_of_isOmPA_aux1 hqs hl hS)

private theorem isPGroup_two_center_of_isOmMA_aux1 {Ω : Type} [Group Ω] [Finite Ω]
    {S : Subgroup Ω} {p n k : ℕ} (hqs : CFSG.Open.IsQuasisimple ↥S) (hn : 4 ≤ n)
    (hS : catalogIs (PSimple p S) (isOmMA n (2 ^ k))) :
    StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .POmegaMinus n 2 k := by
  obtain ⟨i0, hi0, ⟨eCat⟩⟩ := hS
  let P : TauCeti.LieTypeIndex → Prop :=
    fun d => ∃ hv : d.Valid, isOmM n (2 ^ k) (.lie ⟨d, hv⟩)
  have hS_onLie : catalogIs (PSimple p S) (onLie P) := by
    refine ⟨i0, ?_, ⟨eCat⟩⟩
    rcases hi0 with h1 | ⟨hn3, -⟩
    · cases i0 with
      | cyclic a b => simp [isOmM, onLie] at h1
      | alternating a b => simp [isOmM, onLie] at h1
      | sporadic s => simp [isOmM, onLie] at h1
      | lie idx => exact ⟨idx.2, h1⟩
    · omega
  have hmodel : StatedClassicalModel (PSimple p S) .POmegaMinus n 2 k := by
    obtain ⟨d, hv, hPd, ⟨e0⟩⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.CatB.exists_lieIndex hS_onLie
    cases d with
    | twistedD r q =>
      obtain ⟨hv', hPd'⟩ := hPd
      have hrq : r = n ∧ q.card = 2 ^ k := by simpa [isOmM, onLie] using hPd'
      obtain ⟨hr, hqc⟩ := hrq
      have hcard2 : 2 ≤ q.card := q.isPrimePow_card.two_le
      have hkpos : k ≠ 0 := by
        intro hk
        subst hk
        rw [pow_zero] at hqc
        omega
      have hpow : q.p ^ q.exponent = 2 ^ k := by
        rw [← TauCeti.PrimePower.card_def, hqc]
      obtain ⟨hq2, hqexp⟩ :=
        Nat.Prime.pow_inj' q.prime_p Nat.prime_two (Nat.ne_of_gt q.exponent_pos) hkpos hpow
      have hM :=
        CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq2 e0
      simpa [hr, hq2, hqexp] using hM
    | _ => simp [P, isOmM, onLie] at hPd
  have hnt : Nontrivial (PSimple p S) :=
    (CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_of_statedClassicalModel_POmegaMinus
      (PSimple p S) n 2 k hmodel).1
  obtain ⟨ePZ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.HSubT.psimple_nonempty_equiv_quotCenter p S hqs hnt
  exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ePZ hmodel

private theorem isPGroup_two_center_of_isOmMA_aux2
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hqs : CFSG.Open.IsQuasisimple ↥S) {l f : ℕ}
    (hmodelZ : StatedClassicalModel (↥S ⧸ Subgroup.center ↥S) .POmegaMinus l 2 f) :
    IsPGroup 2 (Subgroup.center ↥S) := by
  classical
  let Z : Subgroup ↥S := Subgroup.center ↥S
  let P : Sylow 2 Z := default
  let Z₂ : Subgroup ↥S := (P : Subgroup Z).map Z.subtype
  have hZ₂le : Z₂ ≤ Z := Subgroup.map_subtype_le (P : Subgroup Z)
  haveI : Z₂.Normal := Subgroup.normal_of_le_center hZ₂le
  haveI : Z.Normal := Subgroup.normal_of_le_center (le_refl Z)
  let ψ : ↥S →* ↥S ⧸ Z₂ := QuotientGroup.mk' Z₂
  haveI : Group.IsPerfect ↥S := ⟨hqs.1⟩
  have hLq : CFSG.IsQuasisimple (↥S ⧸ Z₂) :=
    CFSG.LocalAnalysis.GLTheoremA.S172X.isQuasisimple_of_open
      (CFSG.ComponentClassification.Quasisimple.central_quotient hqs Z₂ hZ₂le)
  have hcenterL : Z.map ψ = Subgroup.center (↥S ⧸ Z₂) :=
    CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel ψ
      (QuotientGroup.mk'_surjective Z₂) (by rw [QuotientGroup.ker_mk']; exact hZ₂le)
  have hmodelQ : StatedClassicalModel ((↥S ⧸ Z₂) ⧸ Subgroup.center (↥S ⧸ Z₂)) .POmegaMinus l 2 f := by
    haveI : (Z.map ψ).Normal := by rw [hcenterL]; infer_instance
    exact CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
      ((QuotientGroup.congr (Z.map ψ) (Subgroup.center (↥S ⧸ Z₂)) (MulEquiv.refl _)
        (by simpa using hcenterL)).symm.trans
        (QuotientGroup.quotientQuotientEquivQuotient Z₂ Z hZ₂le)).symm hmodelZ
  have hodd : Odd (Nat.card (Subgroup.center (↥S ⧸ Z₂))) :=
    isPGroup_two_center_of_isOmPA_aux3 hqs Z₂ hZ₂le P rfl
  have hZbot : Subgroup.center (↥S ⧸ Z₂) = ⊥ :=
    (CFSG.SectionRank.EvenCover.even_nonsplit_orthogonal_odd_cover_catalog_step hLq hodd hmodelQ).1
  have hZle : Z ≤ Z₂ := by
    have hmapbot : Z.map ψ = ⊥ := hcenterL.trans hZbot
    rw [Subgroup.map_eq_bot_iff] at hmapbot
    rwa [QuotientGroup.ker_mk'] at hmapbot
  change IsPGroup 2 Z
  exact (le_antisymm hZle hZ₂le).symm ▸ (P.isPGroup'.map Z.subtype)

theorem isPGroup_two_center_of_isOmMA
    {Ω : Type} [Group Ω] [Finite Ω] {S : Subgroup Ω}
    (hqs : CFSG.Open.IsQuasisimple ↥S) {p l f : ℕ} (hl : 4 ≤ l) (hf : 1 ≤ f)
    (hS : catalogIs (PSimple p S) (isOmMA l (2 ^ f))) : IsPGroup 2 (Subgroup.center ↥S) :=
  isPGroup_two_center_of_isOmMA_aux2 hqs (isPGroup_two_center_of_isOmMA_aux1 hqs hl hS)

theorem exists_model_D
    (hRig : CFSG.StandardType.GGLabelRigidInput) (hb : CatDistinct.OrderBridge) (hOdd : Chev2OddAmb)
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (hD : catalogIs (PSimple p S) (onLie T173ClassD)) :
    ∃ (l f : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module F V) (_ : FiniteDimensional F V) (Q : QuadraticForm F V),
      4 ≤ l ∧ Nat.card F = 2 ^ f ∧ (QuadraticMap.polarBilin Q).Nondegenerate ∧ Module.finrank F V = 2 * l ∧
        CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ (p ∣ 2 ^ f - 1 ∨ (f = 1 ∧ p = 3)) ∧
        IsPGroup 2 (Subgroup.center ↥S) ∧
        Nonempty (S172X.S172Model S B ↥(CFSG.RankThree.Classical2.orthDerived Q)) := by
  obtain ⟨l, f, hl, hf, hS⟩ := exists_isOmPA_of_chevTwo hb hOdd hcfg.chev hD
  obtain ⟨F, hFf, hFfin, hFchar, V, hVa, hVm, hVfd, Q, hF, hnd, hdim, hplus, hθ⟩ :=
    S172C.exists_omegaPlus_model (n := l) (k := f) hl hf
  have hBin := S172B.mem_sup_centralizer_of_innerDiagMarking_plus hRig hcfg.qs hl hS
    (innerDiagMarking_of_split16 hcfg.split)
  obtain ⟨e⟩ := hθ (PSimple p S) hS
  haveI : Nontrivial (PSimple p S) := nontrivial_of_isOmPA hl hS
  haveI : Nontrivial ↥(CFSG.RankThree.Classical2.orthDerived Q) := e.injective.nontrivial
  obtain ⟨M⟩ := S172X.S172Model.nonempty_of_pSimple_equiv hcfg.normal hcfg.qs hBin e
  exact ⟨l, f, F, hFf, hFfin, hFchar, V, hVa, hVm, hVfd, Q, hl, hF, hnd, hdim, hplus,
    splits_of_isOmPA hRig hcfg.qs hl hf hS hcfg.split, isPGroup_two_center_of_isOmPA hcfg.qs hl hf hS, ⟨M⟩⟩

theorem exists_model_TD
    (hRig : CFSG.StandardType.GGLabelRigidInput) (hb : CatDistinct.OrderBridge) (hOdd : Chev2OddAmb)
    {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B N D K : Subgroup Ω} {x : Ω}
    (hcfg : Cfg173 p S B N D K x) (hD : catalogIs (PSimple p S) (onLie T173ClassTD)) :
    ∃ (l f : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (V : Type) (_ : AddCommGroup V)
      (_ : Module F V) (_ : FiniteDimensional F V) (Q : QuadraticForm F V),
      4 ≤ l ∧ Nat.card F = 2 ^ f ∧ (QuadraticMap.polarBilin Q).Nondegenerate ∧ Module.finrank F V = 2 * l ∧
        ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q ∧ (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧
        IsPGroup 2 (Subgroup.center ↥S) ∧
        Nonempty (S172X.S172Model S B ↥(CFSG.RankThree.Classical2.orthDerived Q)) := by
  obtain ⟨l, f, hl, hf, hS⟩ := exists_isOmMA_of_chevTwo hb hOdd hcfg.chev hD
  obtain ⟨F, hFf, hFfin, hFchar, V, hVa, hVm, hVfd, Q, hF, hnd, hdim, hminus, hθ⟩ :=
    S172C.exists_omegaMinus_model (n := l) (k := f) hl hf
  have hBin := S172C.mem_sup_centralizer_of_innerDiagMarking hRig hcfg.qs hl hS
    (innerDiagMarking_of_split16 hcfg.split)
  obtain ⟨e⟩ := hθ (PSimple p S) hS
  haveI : Nontrivial (PSimple p S) := nontrivial_of_isOmMA hl hS
  haveI : Nontrivial ↥(CFSG.RankThree.Classical2.orthDerived Q) := e.injective.nontrivial
  obtain ⟨M⟩ := S172X.S172Model.nonempty_of_pSimple_equiv hcfg.normal hcfg.qs hBin e
  exact ⟨l, f, F, hFf, hFfin, hFchar, V, hVa, hVm, hVfd, Q, hl, hF, hnd, hdim, hminus,
    splits_of_isOmMA hRig hcfg.qs hl hf hS hcfg.split, isPGroup_two_center_of_isOmMA hcfg.qs hl hf hS, ⟨M⟩⟩

end CFSG.LocalAnalysis.GLTheoremA.T173X

end
