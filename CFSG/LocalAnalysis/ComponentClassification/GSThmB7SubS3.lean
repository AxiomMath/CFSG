module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SubL
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SubB2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3g
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBHypB2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58ReChoice
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S3f

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem exists_B2_of_eq_sub
    (hS : SchreierFor Blueprint.Catalog) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexReduced) (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hDC : CFDoubleCover)
    (hheld : KProperRelativeB.HeldInput) (hRS : RestrictedStandardInput)
    (hB7 : EmbedsTQuotStatement) (hST : SuzukiTausskyInput) (hRec : CFSp4RecognitionStd)
    (hTwo : CFSp4TwoCentral)
    (hW : ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW)
    (hCov : CFSp4CoverInv)
    [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h : Hyp52 X)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J)
    (hiso : GSIsoAt h.a h.J)
    (hnB1 : ¬ ConclusionB1 h.J) (hnB2a : ¬ ConclusionB2a h.a h.J) (hTab : h.Table517)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hJL : Blueprint.LieModel (OddBar h.J) .PSL 2 p f) (hKa : conjugate h.K h.a = h.K)
    (hKL : Blueprint.LieModel (OddBar h.K) .PSL 2 p (2 * f)) :
    ∃ h' : Hyp52 X, h'.a = h.a ∧ h'.J = h.J ∧ GSMaximalUnbalancingTriple h'.a h'.x h'.J ∧
      ∃ B₂ : Subgroup X, B₂ ≠ ⊥ ∧ B₂ ≤ h'.P ∧ Nat.card B₂ = Nat.card h'.B ∧
        Nat.card ↥(h'.S ⊓ normalizer (B₂ : Set X)) = Nat.card ↥h'.Q ∧
        (∀ L : Subgroup X, ¬ IsoCorrSub h'.a h'.J B₂ L) ∧
        ∀ h₂ : Hyp52 X, h₂.a = h'.a → h₂.J = h'.J → h₂.B = B₂ →
          conjugate h₂.K h₂.a ≠ h₂.K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNP := h.normalizer_P_eq hCFi hTab
  have hCN := h.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
  obtain ⟨-, hSa⟩ := h.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
  have hB2 : 2 < Nat.card h.B := by
    have hne : Nat.card h.B ≠ 2 := fun hB => hnB1
      (lemma71_step1_of_doubleCover hCI hUc hDC hnonab hz hU h hB (hB6 X h)
        (.inl ⟨hKa, p, f, hp, hp2, hf, hJL, hKL⟩))
    have h1 : Nat.card h.B ≠ 1 := fun h1 => h.B_ne_bot (Subgroup.eq_bot_of_card_eq _ h1)
    have h0 : 0 < Nat.card h.B := Nat.card_pos
    omega
  obtain ⟨hBP, -⟩ := h.lemma71_step2a hNP hB2
  obtain ⟨y, hy⟩ := h.exists_isX0Min hBP
  have hcy : h.SecCond y :=
    ⟨(mem_inf.mp hy.1).2, hy.2.1, hy.2.2, hy.Q_le_normalizer_B0, hy.mem_normalizer_Q⟩
  obtain ⟨h', ha', hJ', hB', hK', ⟨c, hcmem, -, hx'c⟩, -, hT', hc, hSylB⟩ :=
    h.exists_reChoice58 hS hnonab hK hmax hiso hCN hSa hcy
  have hyQ := hc.mem_normalizer_Q
  have hyP := hc.mem_P
  have hyT := hc.not_mem_T
  have hmax' : GSMaximalUnbalancingTriple h'.a h'.x h'.J := by
    rw [ha', hx'c, hJ']
    exact ⟨gsUnbalancingTriple_conj hmax.1 (mem_inf.mp hcmem).1 (mem_inf.mp hcmem).2, hmax.2⟩
  have hiso' : GSIsoAt h'.a h'.J := by rw [ha', hJ']; exact hiso
  have hnB1' : ¬ ConclusionB1 h'.J := by rw [hJ']; exact hnB1
  have hnB2a' : ¬ ConclusionB2a h'.a h'.J := by rw [ha', hJ']; exact hnB2a
  have hNP' : h'.T = h'.B ⊔ zpowers h'.a ∧ h'.B ⊓ zpowers h'.a = ⊥ ∧
      ∀ b ∈ h'.B, b * h'.a = h'.a * b := by
    rw [hT', hB', ha']
    exact hNP
  have hZJ' := h'.center_eq_bot hB1 hB6 hCF23 hCF24
  have hCN' := h'.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
  obtain ⟨-, hSa'⟩ := h'.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
  have hW' : h'.NoFusionW :=
    hW X h' ⟨inferInstance, hnonab, hK, hz, hU, hmax', hiso', hnB1', hnB2a'⟩
  have hB2' : 2 < Nat.card h'.B := by rw [hB']; exact hB2
  obtain ⟨-, h2a⟩ := h'.lemma71_step2a hNP' hB2'
  have hyNT : y ∈ normalizer (h'.T : Set X) := mem_normalizer_T_of hyP hyQ
  have hyNB : y ∉ normalizer (h'.B : Set X) := fun hyB =>
    hyT (mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hyP).1, hyB⟩, hyP⟩)
  obtain ⟨hrel2, hB0ne⟩ := h2a y hyNT hyNB
  have hidx : Nat.card h'.B = 2 * Nat.card (h'.secB0 y) := by
    have h2 := relIndex_mul_card (H := h'.B ⊓ conjugate h'.B y) (K := h'.B)
    rw [hrel2, inf_eq_left.mpr inf_le_left] at h2
    exact h2.symm
  have hKa' : conjugate h'.K h'.a = h'.K := by rw [hK', ha']; exact hKa
  have hJL' : Blueprint.LieModel (OddBar h'.J) .PSL 2 p f := hJ' ▸ hJL
  have hKL' : Blueprint.LieModel (OddBar h'.K) .PSL 2 p (2 * f) := hK' ▸ hKL
  obtain ⟨k₀, -, -, -, -, -, -, hk₀P, -, hk₀T, -, -, hOJ₀, hOK₀, hconj₀, -, eT₀, hcard₀⟩ :=
    hc.exists_hyp59_subQuot_of_T_eq hCN' hSa' hNP'.1 hW'
  have hKG := Hyp52.isKGroupCat_subQuot (h := h') (y := y) hnonab hK hB0ne
  have hLB := localB_of_isKGroupCat hS hUc hheld hKG k₀.oddCore_eq_bot
  have hLie := lieModel_psp_of_section_sub hRS hRec hB7 hc hKG hLB k₀ hk₀P hk₀T hOJ₀ hOK₀
    hconj₀ eT₀ hcard₀ hNP'.1 hidx hZJ' hKa' hp hp2 hf h5 hJL' hKL'
  have hLay := lieModel_Lay_of_section_sub hCov hc k₀ hp hp2 hf hLie hZJ'
  obtain ⟨k, hka, hkJ, -, -, -, hkS, hkP, hkQ, hkT, -, -, hOJ, -, -, -, eT, hcard⟩ :=
    hc.exists_hyp59_subQuot_of_kappa hSylB hCN' (kappa_of_lieModel_Lay hc hLay)
  have hkB : Nat.card k.B = 2 := Sub71Aux.card_B_sub hcard hidx
  have hkT2 := Sub71Aux.card_T_quot_sub k eT hNP'.1
  have hP8 : 8 ≤ Nat.card k.toHyp52.P := Sub71Aux.eight_le_card_P_sub hB7 hc k hkP.ge hkT hkT2
  have hkJL : Blueprint.LieModel (↥k.J ⧸ pPrimeCore 2 ↥k.J) .PSL 2 p f := by
    obtain ⟨eJ⟩ := hOJ hZJ'
    exact LieType.CurtisTits.lieModel_of_mulEquiv eJ.symm hJL'
  obtain ⟨hF, hsimple, -, -, -⟩ := k.generalizedFitting_simple
  have : (generalizedFitting (h'.subQuot y)).Normal :=
    LocalCores.generalized_fitting_characteristic.2
  have hJF : k.J ≤ generalizedFitting (h'.subQuot y) := by
    rw [hF]
    refine le_iSup₂_of_le (1 : h'.subQuot y) (one_mem _) fun w hw => ?_
    rw [mem_conjugate_iff, one_mul, inv_one, mul_one]
    exact hw
  have hR2 : IsPGroup 2 k.toHyp52.P := k.toHyp52.isPGroup_S.to_le inf_le_left
  have hRle : k.toHyp52.P ≤ centralizer ({k.a} : Set (h'.subQuot y)) ⊓ coreActionKernel k.J :=
    le_inf (inf_le_left.trans (k.S_le.trans inf_le_left)) inf_le_right
  obtain ⟨t, htR, ht2, M, hMC, hMcomp, hMa, hJM⟩ := hTwo (h'.subQuot y) p f hp hp2 hf h5 hsimple
    hLie k.a k.orderOf_a k.J hJF k.J_le k.isPComponent_J hkJL k.toHyp52.P hR2 hRle
    (isSylowIn_P_inf_normal k.toHyp52 _)
  have htP : t ∈ k.toHyp52.P := (mem_inf.mp htR).1
  have htt : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at this
  have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; exact absurd ht2 (by norm_num)
  obtain ⟨pp, rr, hpp, hrr, hcl, hcpp, -, hrel, hSp, hPC, hpa⟩ :=
    k.presentation_of_index_two hB7 hST hkT2 hP8
  have hP2 : IsPGroup 2 ↥k.toHyp52.P := hR2
  have hnab : rr * pp * rr⁻¹ ≠ pp := by
    intro he
    have hrc : rr ∈ k.toHyp52.P ⊓ centralizer ({pp} : Set (h'.subQuot y)) := by
      refine mem_inf.mpr ⟨hrr, mem_centralizer_singleton_iff.mpr ?_⟩
      calc rr * pp = (rr * pp * rr⁻¹) * rr := by group
        _ = pp * rr := by rw [he]
    rw [hPC] at hrc
    exact not_mem_zpowers_of_presentation hpp hcl hcpp hrc
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hP2) ⟨pp, hpp⟩
  rw [Subgroup.orderOf_mk] at hn
  have h4 : 4 ≤ orderOf pp := by omega
  have hpow : ∃ n : ℕ, orderOf pp = 2 ^ n := ⟨n, hn⟩
  have h2pp : 2 ∣ orderOf pp := by
    rw [hn]
    exact dvd_pow_self 2 (by rintro rfl; rw [pow_zero] at hn; omega)
  have hinv : ∀ w ∈ zpowers pp, w * w = 1 → w ≠ 1 → w = k.a := by
    intro w hw hww hw1
    have h1 := mem_zpowers_half_of_sq_eq_one h2pp hw (by rw [pow_two]; exact hww)
    rw [hpa] at h1
    rcases Seven.eq_one_or_of_mem_zpowers k.orderOf_a h1 with h2 | h2
    · exact absurd h2 hw1
    · exact h2
  have htp : t ∉ zpowers pp := by
    intro htz
    apply hMa
    rw [← hinv t htz htt ht1]
    exact conjugate_eq_of_le_centralizer hMC
  obtain ⟨b, hb, hBb⟩ := exists_eq_zpowers_of_card_two hkB
  have hbB : b ∈ k.B := hBb ▸ mem_zpowers b
  have hbP : b ∈ k.toHyp52.P := k.toHyp52.B_le hbB
  have hbp : b ∉ zpowers pp := by
    intro hbz
    have hbb : b * b = 1 := by
      have := pow_orderOf_eq_one b
      rwa [hb, pow_two] at this
    have hb1 : b ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hb; exact absurd hb (by norm_num)
    apply k.toHyp52.a_not_mem_B
    rw [← hinv b hbz hbb hb1]
    exact hbB
  have hcmp := card_centralizer_eq_of_maxClass (S := k.S) inf_le_left hpp hrr hcl hcpp hrel hpow
    h4 hnab hSp (fun s hs w hw => k.toHyp52.conj_mem_P hs hw) htP htp hbP hbp
  have hkQb : k.toHyp52.Q = k.S ⊓ centralizer ({b} : Set (h'.subQuot y)) := by
    show k.S ⊓ normalizer (k.B : Set (h'.subQuot y)) = _
    rw [hBb, UnbalancedCorr.normalizer_zpowers_eq_centralizer hb]
  rw [hkP] at htP
  obtain ⟨g, hgH, hgP, hgt, hg1, hg2⟩ := exists_lift_sub htP htt ht1
  set B₂ := B2 h' y g with hB₂
  have hgS : (g : X) ∈ h'.S := (mem_inf.mp hgP).1
  have hgord : orderOf (h'.secMk y g) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hg2) hg1
  have hB₂P : B₂ ≤ h'.P := B2_le_P hgP hg2
  have hB₂card : Nat.card B₂ = Nat.card h'.B := by rw [card_B2 hgord, hidx]
  have hB₂ne : B₂ ≠ ⊥ := by
    intro h0
    have h1 := hB₂card
    rw [h0, Subgroup.card_bot] at h1
    omega
  have hQcount : Nat.card ↥k.toHyp52.Q * Nat.card (h'.secB0 y) = Nat.card ↥h'.Q := by
    rw [hkQ]
    exact Hyp52.card_map_subQ_mul (h'.isPGroup_S.to_le inf_le_left)
      ((h'.secB0_le_B y).trans h'.B_le_Q) hc.Q_le_secSub
  have hScount := card_S_inf_normalizer_B2_sub hgH hgS hg1 hg2
  rw [← hkS, hgt, hcmp, ← hkQb, hQcount] at hScount
  have hge : Nat.card ↥h'.Q ≤ Nat.card ↥(h'.S ⊓ normalizer (B₂ : Set X)) := by
    rw [hScount]
    exact Subgroup.card_le_of_le inf_le_left
  have hMC' : M ≤ centralizer ({h'.subQ y ⟨g, hgH⟩} : Set (h'.subQuot y)) := by
    rw [hgt]; exact hMC
  have hMcomp' : IsComponent (M.subgroupOf
      (centralizer ({h'.subQ y ⟨g, hgH⟩} : Set (h'.subQuot y)))) := by rw [hgt]; exact hMcomp
  have hMa' : conjugate M (h'.subQ y ⟨h'.a, hc.a_mem_secSub⟩) ≠ M := by
    rw [← hka]; exact hMa
  have hJM' : ((h'.secJ0 y).subgroupOf (h'.secSub y)).map (h'.subQ y) ≤
      M ⊔ conjugate M (h'.subQ y ⟨h'.a, hc.a_mem_secSub⟩) := by
    rw [← hka, ← hkJ]; exact hJM
  have ht' : orderOf (h'.subQ y ⟨g, hgH⟩) = 2 := by rw [hgt]; exact ht2
  have hbad : ∀ L : Subgroup X, ¬ IsoCorrSub h'.a h'.J B₂ L :=
    not_isoCorrSub_B2_sub hc hLB hZJ' hgH hgP hg1 hg2 ht' hMC' hMcomp' hMa' hJM'
  have hle : Nat.card ↥(h'.S ⊓ normalizer (B₂ : Set X)) ≤ Nat.card ↥h'.Q := by
    by_contra hlt
    push Not at hlt
    obtain ⟨L, hL⟩ := h'.isoCorr_of_lt B₂ hB₂P (Or.inr ⟨hB₂card, hlt⟩)
    exact hbad L hL
  exact ⟨h', ha', hJ', hmax', B₂, hB₂ne, hB₂P, hB₂card, le_antisymm hle hge, hbad,
    fun h₂ ha hJ hB => conjugate_K_ne_of_B2_sub hc hLB hZJ' hgH hgP hg1 hg2 ht' hMC' hMcomp'
      hMa' hJM' h₂ ha hJ hB⟩

theorem lemma71_step3_sub
    (hS : SchreierFor Blueprint.Catalog) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexReduced) (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hDC : CFDoubleCover)
    (hheld : KProperRelativeB.HeldInput) (hCTI : LayerGeneratedUniversalComponentStandard)
    (hRS : RestrictedStandardInput) (hB7 : EmbedsTQuotStatement) (hST : SuzukiTausskyInput)
    (hRec : CFSp4RecognitionStd) (hTwo : CFSp4TwoCentral)
    (hW : ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW)
    (hCov : CFSp4CoverInv)
    [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h : Hyp52 X)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J)
    (hiso : GSIsoAt h.a h.J)
    (hnB1 : ¬ ConclusionB1 h.J) (hnB2a : ¬ ConclusionB2a h.a h.J) (hTab : h.Table517)
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (h5 : 5 ≤ p ^ f)
    (hJL : Blueprint.LieModel (OddBar h.J) .PSL 2 p f) (hKa : conjugate h.K h.a = h.K)
    (hKL : Blueprint.LieModel (OddBar h.K) .PSL 2 p (2 * f)) :
    ∃ h₂ : Hyp52 X, h₂.a = h.a ∧ h₂.J = h.J ∧ GSMaximalUnbalancingTriple h₂.a h₂.x h₂.J ∧
      conjugate h₂.K h₂.a ≠ h₂.K := by
  obtain ⟨h', ha', hJ', hmax', B₂, hB₂, hB₂P, hcard, hQ, hbad, hK₂⟩ :=
    exists_B2_of_eq_sub hS hB1 hB6 hCF23 hCF24 hCFc hCFi hCI hUc hDC hheld hRS hB7 hST hRec hTwo
      hW hCov hnonab hK hz hU h hmax hiso hnB1 hnB2a hTab hp hp2 hf h5 hJL hKa hKL
  have hiso' : GSIsoAt h'.a h'.J := by
    rw [ha', hJ']
    exact hiso
  have hnB2a' : ¬ ConclusionB2a h'.a h'.J := by
    rw [ha', hJ']
    exact hnB2a
  obtain ⟨h₂, ha₂, hx₂, hJ₂, -, hB₂'⟩ := Hyp52.exists_of_sameLex hS hUc hheld hCTI hRS hnonab hK
    h' hmax' hiso' hnB2a' hB₂ hB₂P hcard hQ hbad
  refine ⟨h₂, ha₂.trans ha', hJ₂.trans hJ', ?_, hK₂ h₂ ha₂ hJ₂ hB₂'⟩
  rw [ha₂, hx₂, hJ₂]
  exact hmax'

end Seven

end CFSG.ComponentClassification.GSThmB
