module

public import CFSG.LocalAnalysis.GLTheoremA.S12.Inputs122
public import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.LocalAnalysis.SeitzReduction.CrossChar
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofLieOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

private theorem tri_two_pow_mod_three (n : ℕ) : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by
  induction n with
  | zero => norm_num
  | succ k ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> norm_num

private theorem tri_halfSplit (lab : GLALabel) (c : Prop) (h : lab.tag = .D ∨ lab.tag = .triD4) :
    GLAHalfSplit16 3 lab c := by
  rcases tri_two_pow_mod_three lab.n with h1 | h2
  · have hd : 3 ∣ 2 ^ lab.n - 1 := by omega
    rcases h with ht | ht
    · exact Or.inl (Or.inl ⟨by simp [CFSG.Assembly.LargeEvenUntwisted, ht], hd⟩)
    · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨Or.inr (Or.inl ht), hd⟩)))
  · have hd : 3 ∣ 2 ^ lab.n + 1 := by omega
    rcases h with ht | ht
    · exact Or.inr (Or.inl ⟨Or.inr (Or.inl ht), hd⟩)
    · exact Or.inl (Or.inr (Or.inl ⟨by simp [CFSG.Assembly.LargeEvenUntwisted, ht],
        by simp [ht], by simp [ht], hd⟩))

private theorem tri_tag_D (lab : GLALabel) (h : CFSG.StandardType.markTag lab = .POmegaPlus) :
    lab.tag = .D := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [CFSG.StandardType.markTag] at h <;> (try split_ifs at h) <;> simp_all

private theorem tri_tag_T (lab : GLALabel) (h : CFSG.StandardType.markTag lab = .trialityD4) :
    lab.tag = .triD4 := by
  obtain ⟨t, r, n⟩ := lab
  cases t <;> simp only [CFSG.StandardType.markTag] at h <;> (try split_ifs at h) <;> simp_all

private theorem tri_labelOf {G : Type} [Group G] {J : Subgroup G} (hq : CFSG.Open.IsQuasisimple ↥J)
    {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hM : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) t n 2 f) (Φ : GLALabel → Prop)
    (hΦ : ∀ lab : GLALabel, CFSG.StandardType.markTag lab = t → Φ lab) :
    ∃ lab : GLALabel, LabelOf J lab ∧ Φ lab := by
  obtain ⟨hc, lab, hlab, hraw⟩ :=
    CFSG.StandardType.Canonical.largeEvenMarking_of_lieModel_centerQuot hq.1 hM
  obtain ⟨R, hR, I, F, hs, hna, θ, hP⟩ := CFSG.StandardType.largeEvenRawDatum_exists hraw
  have hraw' : CFSG.Assembly.LargeEvenRawDatum lab (fun R _ I F => IsSimpleGroup R ∧
      (∃ a b : R, a * b ≠ b * a) ∧ ∃ θ : ↥J ⧸ Subgroup.center ↥J ≃* R, lab = lab) :=
    CFSG.StandardType.Canonical.largeEvenRawDatum_imp hlab (fun R _ I F h => h.2.1)
      (fun R _ I F h _ => ⟨h.1, h.2.1, by obtain ⟨θ, -⟩ := h.2.2; exact ⟨θ, rfl⟩⟩) hraw
  exact ⟨lab, ⟨hc, lab, hlab, hraw'⟩, hΦ lab hP.1⟩

private theorem tri_quot_equiv {G : Type} [Group G] [Finite G] {X J : Subgroup G}
    (hJ : GLAPComponent 3 X J) (hq : CFSG.Open.IsQuasisimple ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple 3 J) := by
  have hnt : Nontrivial (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hJ)
  have hOtop : GLAPPrimeCore 3 ↥J ≠ ⊤ := by
    intro h
    rw [h] at hnt
    exact not_subsingleton_iff_nontrivial.2 hnt QuotientGroup.subsingleton_quotient_top
  have hOZ : GLAPPrimeCore 3 ↥J ≤ Subgroup.center ↥J :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hOtop
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hq.2
  haveI := hq.2.toNontrivial
  have hZbot : Subgroup.center (↥J ⧸ Subgroup.center ↥J) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (↥J ⧸ Subgroup.center ↥J)) with h | h
    · exact h
    · exfalso
      have hall : ∀ a b : ↥J, ⁅a, b⁆ ∈ Subgroup.center ↥J := by
        intro a b
        have ha : (QuotientGroup.mk a⁻¹ : ↥J ⧸ Subgroup.center ↥J) ∈
            Subgroup.center (↥J ⧸ Subgroup.center ↥J) := h ▸ Subgroup.mem_top _
        have hc := Subgroup.mem_center_iff.1 ha (QuotientGroup.mk b⁻¹)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hc
        have e : (b⁻¹ * a⁻¹)⁻¹ * (a⁻¹ * b⁻¹) = ⁅a, b⁆ := by
          rw [commutatorElement_def]; group
        rwa [e] at hc
      have hle : commutator ↥J ≤ Subgroup.center ↥J :=
        Subgroup.commutator_le.2 fun a _ b _ => hall a b
      rw [hq.1, top_le_iff] at hle
      have hsub : Subsingleton (↥J ⧸ Subgroup.center ↥J) := by
        rw [hle]; exact QuotientGroup.subsingleton_quotient_top
      exact not_subsingleton _ hsub
  let f : ↥J →* PSimple 3 J :=
    (QuotientGroup.mk' (Subgroup.center (PQuot 3 J))).comp (QuotientGroup.mk' (GLAPPrimeCore 3 ↥J))
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _)
  have hker : f.ker = Subgroup.center ↥J := by
    ext x
    simp only [MonoidHom.mem_ker, f, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have hxZ : (QuotientGroup.mk x : ↥J ⧸ Subgroup.center ↥J) ∈
          Subgroup.center (↥J ⧸ Subgroup.center ↥J) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
        have hw := Subgroup.mem_center_iff.1 hx (QuotientGroup.mk w)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hw
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
        exact hOZ hw
      rw [hZbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hxZ
      exact hxZ
    · intro hx
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx w]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

private theorem tri_lie_of_onLie {P : TauCeti.LieTypeIndex → Prop} {i : TauCeti.CFSGIndex}
    (h : onLie P i) : ∃ j : TauCeti.ValidLieTypeIndex, i = .lie j ∧ P j.1 := by
  rcases i with _ | _ | j | _
  · exact h.elim
  · exact h.elim
  · exact ⟨j, rfl, h⟩
  · exact h.elim

private theorem tri_D4 {i : TauCeti.CFSGIndex} (h : isD4any i) : ∃ (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.D 4 q).Valid), i = .lie ⟨.D 4 q, hv⟩ ∧ q.p = 2 := by
  obtain ⟨j, rfl, hj⟩ := tri_lie_of_onLie h
  obtain ⟨d, hv⟩ := j
  split at hj
  next q heq => subst heq; exact ⟨q, hv, rfl, hj⟩
  next => exact hj.elim

private theorem tri_T {i : TauCeti.CFSGIndex}
    (h : onLie (fun | .trialityD4 _ => True | _ => False) i) : ∃ (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid), i = .lie ⟨.trialityD4 q, hv⟩ := by
  obtain ⟨j, rfl, hj⟩ := tri_lie_of_onLie h
  obtain ⟨d, hv⟩ := j
  split at hj
  next q heq => subst heq; exact ⟨q, hv, rfl⟩
  next => exact hj.elim

private theorem tri_odd_false {S : Type} [Group S] {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.trialityD4 q).Valid) (hp : q.p ≠ 2)
    (e : S ≃* TauCeti.ValidLieTypeIndex.Group ⟨.trialityD4 q, hv⟩) (hchev : IsChevSimple 2 S) :
    False := by
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  have hto : 0 < (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by decide
  have hKc : Nat.card (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order)) =
      (q.p ^ q.exponent) ^ (CFSG.Blueprint.Chevalley.TwistTag.D4).order := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero q.exponent_pos.ne' hto.ne'), pow_mul]
  obtain ⟨b⟩ := CFSG.TauCetiBridge.chevalleyBridges.trialityD4 q hv hp
    (GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order))
    (by rw [hKc, TauCeti.PrimePower.card_def]) (iterateFrobenius _ q.p q.exponent)
    (fun x => by rw [iterateFrobenius_def, TauCeti.PrimePower.card_def])
  have hC : CFSG.Blueprint.ChevalleyExceptionalModel S .trialityD4 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩,
      GaloisField q.p (q.exponent * (CFSG.Blueprint.Chevalley.TwistTag.D4).order), inferInstance,
      inferInstance, hKc, iterateFrobenius _ q.p q.exponent,
      fun x => by rw [iterateFrobenius_def], ⟨e.trans b.symm⟩⟩
  have hodd : CFSG.Blueprint.LieModel S .trialityD4 0 q.p q.exponent :=
    Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags], hC⟩)
  have hadm := CFSG.Blueprint.LieModel.admissible hodd
  have hO := CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput
  have hcard := (hO S .trialityD4 0 q.p q.exponent hadm hodd).2.1
  have hp3 : 3 ≤ q.p := by
    have := q.prime_p.two_le
    omega
  have hQ : 3 ≤ q.p ^ q.exponent := le_trans hp3 (Nat.le_self_pow q.exponent_pos.ne' _)
  have hNS : Nat.card S = (q.p ^ q.exponent) ^ 12 * ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
      ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) := by
    simpa [CFSG.ComponentClassification.CatLeaf.lieOrderDivisor,
      CFSG.ComponentClassification.CatLeaf.lieOrderNumerator] using hcard
  have hbig : 3 ^ 12 ≤ Nat.card S := by
    rw [hNS]
    have h6 : 2 ≤ (q.p ^ q.exponent) ^ 6 := le_trans (by omega) (Nat.pow_le_pow_left hQ 6)
    have h2 : 2 ≤ (q.p ^ q.exponent) ^ 2 := le_trans (by omega) (Nat.pow_le_pow_left hQ 2)
    have hX : 0 < ((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
        ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1) :=
      Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
    have h12 : 3 ^ 12 ≤ (q.p ^ q.exponent) ^ 12 := Nat.pow_le_pow_left hQ 12
    calc 3 ^ 12 ≤ (q.p ^ q.exponent) ^ 12 := h12
      _ ≤ (q.p ^ q.exponent) ^ 12 * (((q.p ^ q.exponent) ^ 8 + (q.p ^ q.exponent) ^ 4 + 1) *
          ((q.p ^ q.exponent) ^ 6 - 1) * ((q.p ^ q.exponent) ^ 2 - 1)) :=
        Nat.le_mul_of_pos_right _ hX
      _ = _ := by ring
  rcases CFSG.StandardType.ChevTwo.chevTwo_cases hchev with ⟨t', n', f', hX⟩ | ⟨e6⟩ | hPSU
  · have hodd' : CFSG.Blueprint.OddLieType S :=
      ⟨.trialityD4, 0, q.p, q.exponent, q.prime_p, hp, hadm, hodd⟩
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType hO hX hodd' with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 2 (2 ^ 2) = 60 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 2 (2 ^ 2) = 1 from rfl] at h
      norm_num at hbig
      omega
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSL 3 (2 ^ 1) = 168 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSL 3 (2 ^ 1) = 1 from rfl] at h
      norm_num at hbig
      omega
    · have h := (hO S _ _ 2 _ (CFSG.Blueprint.LieModel.admissible hX) hX).2.1
      rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 4 (2 ^ 1) = 25920 from by decide,
        show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 4 (2 ^ 1) = 1 from rfl] at h
      norm_num at hbig
      omega
  · obtain ⟨e6'⟩ := e6
    have h6 : Nat.card S = 360 := by
      rw [Nat.card_congr e6'.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    norm_num at hbig
    omega
  · have hL : CFSG.Blueprint.LieModel S .PSU 3 3 1 :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags], hPSU⟩
    have h := (hO S .PSU 3 3 1 (CFSG.Blueprint.LieModel.admissible hL) hL).2.1
    rw [show CFSG.ComponentClassification.CatLeaf.lieOrderNumerator .PSU 3 (3 ^ 1) = 6048 from by decide,
      show CFSG.ComponentClassification.CatLeaf.lieOrderDivisor .PSU 3 (3 ^ 1) = 1 from rfl] at h
    norm_num at hbig
    omega

theorem trihalf_holds (G : Type) [Group G] [Finite G] : TriHalfSplitAt G := by
  intro X J hJ hq hchev hcase
  obtain ⟨eJ⟩ := tri_quot_equiv hJ hq
  rcases hcase with hD | hT
  · obtain ⟨i, hi, ⟨eS⟩⟩ := hD
    obtain ⟨q, hv, rfl, hq2⟩ := tri_D4 hi
    have hM : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .POmegaPlus 4 2 q.exponent := by
      have h := CFSG.Models.lieModel_D 4 q hv (eJ.trans eS)
      rw [hq2] at h
      exact CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
        (by simp [CFSG.Blueprint.classicalTags]) h
    obtain ⟨lab, hlab, hΦ⟩ := tri_labelOf hq hM (fun lab => (lab.tag = .D ∨ lab.tag = .triD4) ∧
        GLAHalfSplit16 3 lab (Subgroup.center ↥J = ⊥))
      (fun lab h => ⟨Or.inl (tri_tag_D lab h), tri_halfSplit lab _ (Or.inl (tri_tag_D lab h))⟩)
    exact ⟨lab, hlab, hΦ⟩
  · obtain ⟨i, hi, ⟨eS⟩⟩ := hT
    obtain ⟨q, hv, rfl⟩ := tri_T hi
    by_cases hp2 : q.p = 2
    · have hB := CFSG.TauCetiBridge.Even.chevalleyBridgesAll
      have hM : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .trialityD4 0 2 q.exponent :=
        Or.inr (Or.inl ⟨rfl, by simp [CFSG.Blueprint.chevalleyExceptionalTags],
          ⟨Nat.prime_two, q.exponent_pos, rfl⟩,
          CFSG.StandardType.ChevTwo.twistedChevalleyModel_of_bridge hB.trialityD4 q hv hp2 (eJ.trans eS)⟩)
      obtain ⟨lab, hlab, hΦ⟩ := tri_labelOf hq hM (fun lab => (lab.tag = .D ∨ lab.tag = .triD4) ∧
          GLAHalfSplit16 3 lab (Subgroup.center ↥J = ⊥))
        (fun lab h => ⟨Or.inr (tri_tag_T lab h), tri_halfSplit lab _ (Or.inr (tri_tag_T lab h))⟩)
      exact ⟨lab, hlab, hΦ⟩
    · exact (tri_odd_false hv hp2 eS hchev).elim

end CFSG.LocalAnalysis.GLTheoremA
