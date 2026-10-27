module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Pre
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Hyp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82ReSXChoice
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4NoFus71

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace Hyp52

variable {X : Type} [Group X] [Finite X]

theorem L82Hyp.of_inputs (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center)
    (hCFi : CFProp23IndexReduced) {h : Hyp52 X} (hset : Sec8Setting X h)
    (hP : Nat.card h.P ≠ 4) : h.L82Hyp where
  setting := hset
  card_P := hP
  NP_eq := h.normalizer_P_eq hCFi (h.sec8Case_table517 hset.2.2.2.2.2.2.2.2.2.2)
  C_eq := h.centralizer_P_eq hB1 hCF23 hCFc
  J_normal := h.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
  S_sylow_C := (h.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc).2

end Hyp52

namespace Eight2

variable {X : Type} [Group X] [Finite X]

structure Setting0 (X : Type) [Group X] [Finite X] where
  h : Hyp52 X
  y : X
  isSimpleGroup : IsSimpleGroup X
  nonab : ∃ u v : X, u * v ≠ v * u
  kProper : Assembly.KProper Blueprint.Catalog X
  unbal : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥
  notU : ¬ OutcomeLocal.UOutcome X
  case8 : h.Sec8Case
  NP_eq : h.T = h.B ⊔ zpowers h.a ∧ h.B ⊓ zpowers h.a = ⊥ ∧ ∀ b ∈ h.B, b * h.a = h.a * b
  C_eq : h.P ⊓ centralizer (h.S : Set X) = zpowers h.a
  J_normal : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X)
  S_sylow : Seven.IsSylowIn h.S (centralizer ({h.a} : Set X))
  center_J : center (h.J ⧸ pPrimeCore 2 h.J) = ⊥
  secCond : h.SecCond y
  hr : Hyp52 X
  hr_a : hr.a = h.a
  hr_J : hr.J = h.J
  hr_B : hr.B = h.B
  hr_conj : ∃ c ∈ centralizer ({h.a} : Set X) ⊓ normalizer (h.J : Set X),
    hr.S = conjugate h.S c ∧ hr.x = c⁻¹ * h.x * c
  S0_le_hr : h.S ⊓ h.secG0 y ≤ hr.S
  hr_T : (h.reChooseSX hr hr_a hr_J hr_B).T = h.T
  secCondR : (h.reChooseSX hr hr_a hr_J hr_B).SecCond y
  sylowR : Seven.IsSylowIn ((h.reChooseSX hr hr_a hr_J hr_B).S ⊓ h.secG0 y)
    (centralizer ({h.a} : Set X) ⊓ h.secG0 y)
  lemma61 : h.Lemma61Shape y
  S0_le : h.S ⊓ normalizer (h.secB0 y : Set X) ≤ centralizer (Seven.E h y : Set X)
  S0_sylow : ∃ R : Sylow 2 ↥(normalizer (h.secB0 y : Set X) ⊓ centralizer (Seven.E h y : Set X)),
    (R : Subgroup _) = (h.S ⊓ normalizer (h.secB0 y : Set X)).subgroupOf
      (normalizer (h.secB0 y : Set X) ⊓ centralizer (Seven.E h y : Set X))
  eight_le_card_P : 8 ≤ Nat.card h.P
  relIndex_B0 : (h.secB0 y).relIndex h.B = 2
  unbalTriple : GSUnbalancingTriple h.a h.x h.J
  isoAt : GSIsoAt h.a h.J
  maxTriple : GSMaximalUnbalancingTriple h.a h.x h.J
  notB1 : ¬ ConclusionB1 h.J
  notB2a : ¬ ConclusionB2a h.a h.J

abbrev Setting0.hsec (s : Setting0 X) : Hyp52 X := s.h.reChooseSX s.hr s.hr_a s.hr_J s.hr_B

@[expose] def Setting0.KappaAt (s : Setting0 X) : Prop :=
  ∀ l ∈ layerIn (centralizer (s.h.secB0 s.y : Set X)),
    l ∈ normalizer ((s.h.secJ0 s.y ⊔ s.h.secB0 s.y : Subgroup X) : Set X) →
    l * s.h.a * l⁻¹ * s.h.a⁻¹ ∈ s.h.secB0 s.y → l * s.h.a = s.h.a * l

theorem Setting0.mem_hsec_P (s : Setting0 X) {w : X} (hwP : w ∈ s.h.P)
    (hwG : w ∈ s.h.secG0 s.y) : w ∈ s.hsec.P :=
  Hyp52.reChooseSX_P_of_le s.S0_le_hr (mem_inf.mpr ⟨hwP, hwG⟩)

theorem card_P_of_prop62Output {h h' : Hyp52 X} {y : X} (hrel : Seven.Prop62Output h h' y) :
    Nat.card h'.P = Nat.card h.P := by
  obtain ⟨-, hJ', -, -, ⟨c, hc, hS', -⟩, -⟩ := hrel
  have hcJ : c ∈ normalizer (h.J : Set X) := (mem_inf.mp hc).2
  have hP' : h'.P = conjugate h.P c := by
    show h'.S ⊓ coreActionKernel h'.J = conjugate (h.S ⊓ coreActionKernel h.J) c
    rw [hS', hJ', conjugate_inf, Six.conjugate_coreActionKernel hcJ]
  rw [hP', card_conjugate_eq]

theorem exists_setting0_of_reChoice (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center)
    (hCFi : CFProp23IndexReduced)
    {h : Hyp52 X} (hset : Sec8Setting X h) (hP : Nat.card h.P ≠ 4) {y : X}
    {h' : Hyp52 X} (hrel : Seven.Prop62Output h h' y) {hr : Hyp52 X} (ha : hr.a = h'.a)
    (hJ : hr.J = h'.J) (hB : hr.B = h'.B)
    (hconj : ∃ c ∈ centralizer ({h'.a} : Set X) ⊓ normalizer (h'.J : Set X),
      hr.S = conjugate h'.S c ∧ hr.x = c⁻¹ * h'.x * c)
    (hS0 : h'.S ⊓ h'.secG0 y ≤ hr.S) (hT : (h'.reChooseSX hr ha hJ hB).T = h'.T)
    (hcR : (h'.reChooseSX hr ha hJ hB).SecCond y)
    (hsylR : Seven.IsSylowIn (hr.S ⊓ h'.secG0 y) (centralizer ({h'.a} : Set X) ⊓ h'.secG0 y)) :
    ∃ s : Setting0 X, s.h = h' ∧ s.y = y ∧ s.hr = hr := by
  have H := Hyp52.L82Hyp.of_inputs hB1 hB6 hCF23 hCF24 hCFc hCFi hset hP
  have hset0 := hset
  obtain ⟨hsimple, hnonab, hK, hz, hU, hmax, -, hiso, hnB1, hnB2a, hcase⟩ := hset0
  have := hsimple
  have hrel0 := hrel
  obtain ⟨ha', hJ', hB', hK', -, hQ', hQ0, hyQ, hyP, hyT, hy2, ⟨hS0E, hS0syl⟩, h61⟩ := hrel
  have hcase' : h'.Sec8Case := by
    show (Nonempty (h'.J ⧸ pPrimeCore 2 h'.J ≃* alternatingGroup (Fin 6)) ∧
        conjugate h'.K h'.a = h'.K ∧
        Nonempty (h'.K ⧸ pPrimeCore 2 h'.K ≃* alternatingGroup (Fin 8))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
        Blueprint.LieModel (h'.J ⧸ pPrimeCore 2 h'.J) .PSL 2 p (2 * f) ∧
        conjugate h'.K h'.a = h'.K ∧ Blueprint.LieModel (h'.K ⧸ pPrimeCore 2 h'.K) .PSp 2 p f
    rw [hJ', hK', ha']
    exact hcase
  have hT' : h'.T = h.T := by
    have hQS' : h.Q ≤ h'.S := hQ' ▸ (inf_le_left : h'.Q ≤ h'.S)
    have hQS : h.Q ≤ h.S := inf_le_left
    show h'.Q ⊓ (h'.S ⊓ coreActionKernel h'.J) = h.Q ⊓ (h.S ⊓ coreActionKernel h.J)
    rw [hJ', hQ']
    apply le_antisymm
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hQS) (inf_le_right.trans inf_le_right))
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hQS') (inf_le_right.trans inf_le_right))
  have hNP' : h'.T = h'.B ⊔ zpowers h'.a ∧ h'.B ⊓ zpowers h'.a = ⊥ ∧
      ∀ b ∈ h'.B, b * h'.a = h'.a * b := by
    rw [hT', hB', ha']
    exact H.NP_eq
  have hyNT : y ∈ normalizer (h'.T : Set X) := Seven.mem_normalizer_T_of hyP hyQ
  have hyNB : y ∉ normalizer (h'.B : Set X) := fun hyB =>
    hyT (mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hyP).1, hyB⟩, hyP⟩)
  have hidx := h'.relIndex_inf_conjugate hNP' hyNT hyNB
  have hQ0' : h'.Q ≤ h'.secG0 y := by
    show h'.Q ≤ normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X)
    rw [hB']
    exact hQ0
  have hc : h'.SecCond y := ⟨hyP, hyT, hy2, hQ0', hyQ⟩
  have hS0E' : h'.S ⊓ normalizer (h'.secB0 y : Set X) ≤ centralizer (Seven.E h' y : Set X) := by
    show h'.S ⊓ normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X) ≤
      centralizer ((zpowers h'.a ⊔ ⁅h'.B, zpowers y⁆ : Subgroup X) : Set X)
    rw [hB', ha']
    exact hS0E.trans inf_le_right
  have hS0syl' : ∃ R : Sylow 2 ↥(normalizer (h'.secB0 y : Set X) ⊓
      centralizer (Seven.E h' y : Set X)),
      (R : Subgroup _) = (h'.S ⊓ normalizer (h'.secB0 y : Set X)).subgroupOf
        (normalizer (h'.secB0 y : Set X) ⊓ centralizer (Seven.E h' y : Set X)) := by
    show ∃ R : Sylow 2 ↥(normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X) ⊓
        centralizer ((zpowers h'.a ⊔ ⁅h'.B, zpowers y⁆ : Subgroup X) : Set X)),
      (R : Subgroup _) = (h'.S ⊓ normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) :
        Set X)).subgroupOf (normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X) ⊓
          centralizer ((zpowers h'.a ⊔ ⁅h'.B, zpowers y⁆ : Subgroup X) : Set X))
    rw [hB', ha']
    exact hS0syl
  have hP8 : 8 ≤ Nat.card h'.P := by
    rw [card_P_of_prop62Output hrel0]
    exact H.eight_le_card_P
  have hUnb' : GSUnbalancingTriple h'.a h'.x h'.J := by
    obtain ⟨ha'', hJ'', -, -, ⟨c, hcmem, -, hx'c⟩, -⟩ := hrel0
    rw [ha'', hx'c, hJ'']
    exact gsUnbalancingTriple_conj hmax.1 (mem_inf.mp hcmem).1 (mem_inf.mp hcmem).2
  have hiso' : GSIsoAt h'.a h'.J := by
    rw [ha', hJ']
    exact hiso
  have hnB1' : ¬ ConclusionB1 h'.J := by
    rw [hJ']
    exact hnB1
  have hnB2a' : ¬ ConclusionB2a h'.a h'.J := by
    rw [ha', hJ']
    exact hnB2a
  exact ⟨
    { h := h'
      y := y
      isSimpleGroup := hsimple
      nonab := hnonab
      kProper := hK
      unbal := hz
      notU := hU
      case8 := hcase'
      NP_eq := hNP'
      C_eq := h'.centralizer_P_eq hB1 hCF23 hCFc
      J_normal := h'.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
      S_sylow := h'.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
      center_J := h'.center_eq_bot hB1 hB6 hCF23 hCF24
      secCond := hc
      hr := hr
      hr_a := ha
      hr_J := hJ
      hr_B := hB
      hr_conj := hconj
      S0_le_hr := hS0
      hr_T := hT
      secCondR := hcR
      sylowR := hsylR
      lemma61 := h61
      S0_le := hS0E'
      S0_sylow := hS0syl'
      eight_le_card_P := hP8
      relIndex_B0 := hidx
      unbalTriple := hUnb'
      isoAt := hiso'
      maxTriple := Seven.Prop62Output.maximal hrel0 hmax
      notB1 := hnB1'
      notB2a := hnB2a' }, rfl, rfl, rfl⟩

theorem exists_setting0_of_prop62Output (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center)
    (hCFi : CFProp23IndexReduced) (hS : SchreierFor Blueprint.Catalog)
    {h : Hyp52 X} (hset : Sec8Setting X h) (hP : Nat.card h.P ≠ 4) {y : X}
    {h' : Hyp52 X} (hrel : Seven.Prop62Output h h' y) : ∃ s : Setting0 X, s.h = h' ∧ s.y = y := by
  have hset0 := hset
  obtain ⟨hsimple, hnonab, hK, -, -, hmax, -, hiso, -, -, -⟩ := hset0
  have := hsimple
  have ha' : h'.a = h.a := hrel.1
  have hJ' : h'.J = h.J := hrel.2.1
  have hiso' : GSIsoAt h'.a h'.J := by
    rw [ha', hJ']
    exact hiso
  obtain ⟨hr, ha, hJ, hB, hconj, hS0, -, hT, hcR, hsylR⟩ :=
    h'.exists_reChooseSX hS hnonab hK (Seven.Prop62Output.maximal hrel hmax) hiso'
      (h'.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc)
      (h'.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc).2 (Seven.Prop62Output.secCond hrel)
  obtain ⟨s, hs, hsy, -⟩ := exists_setting0_of_reChoice hB1 hB6 hCF23 hCF24 hCFc hCFi hset hP hrel
    ha hJ hB hconj hS0 hT hcR hsylR
  exact ⟨s, hs, hsy⟩

theorem exists_setting0_of_schreier (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center)
    (hCFi : CFProp23IndexReduced) (hS : SchreierFor Blueprint.Catalog)
    {h : Hyp52 X} (hset : Sec8Setting X h) (hP : Nat.card h.P ≠ 4) :
    ∃ s : Setting0 X, h.IsX0Min s.y ∧ Seven.Prop62Output h s.h s.y := by
  have H := Hyp52.L82Hyp.of_inputs hB1 hB6 hCF23 hCF24 hCFc hCFi hset hP
  obtain ⟨y, hy, h', hrel⟩ := H.exists_prop62 hS
  obtain ⟨s, rfl, rfl⟩ :=
    exists_setting0_of_prop62Output hB1 hB6 hCF23 hCF24 hCFc hCFi hS hset hP hrel
  exact ⟨s, hy, hrel⟩

namespace Setting0

variable (s : Setting0 X)

theorem exists_commutator_eq : ∃ b' ∈ s.h.B, ∃ b₀ ∈ s.h.secB0 s.y, ⁅b', s.y⁆ = s.h.a * b₀ := by
  have hyP := s.secCond.mem_P
  have hyT := s.secCond.not_mem_T
  have hnorm : ¬ ∀ b' ∈ s.h.B, ⁅b', s.y⁆ ∈ s.h.B := by
    intro hall
    apply hyT
    have hyN : s.y ∈ normalizer (s.h.B : Set X) := by
      refine mem_normalizer_of_conj_mem_fin fun w hw => ?_
      have h1 := hall w⁻¹ (inv_mem hw)
      have h2 : s.y * w * s.y⁻¹ = w * ⁅w⁻¹, s.y⁆ := by
        rw [commutatorElement_def]; group
      rw [h2]
      exact mul_mem hw h1
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hyP).1, hyN⟩, hyP⟩
  push Not at hnorm
  obtain ⟨b', hb', hnot⟩ := hnorm
  have hmem : ⁅b', s.y⁆ ∈ ⁅s.h.B, zpowers s.y⁆ :=
    commutator_mem_commutator hb' (mem_zpowers _)
  have hB0B := s.h.secB0_le_B s.y
  rcases s.lemma61 with h1 | ⟨b, hb2, -, -, hbB0, -, hle, -⟩
  · rw [h1] at hmem
    rcases eq_one_or_of_mem_zpowers_sq (Six.a_mul_a_self s.h) hmem with h2 | h2
    · exact absurd (h2 ▸ one_mem _) hnot
    · exact ⟨b', hb', 1, one_mem _, by rw [h2, mul_one]⟩
  · have hb : b * b = 1 := by rw [← pow_two, ← hb2, pow_orderOf_eq_one]
    have hbB : b ∈ s.h.B := hB0B hbB0
    have hab : b * s.h.a = s.h.a * b := s.NP_eq.2.2 b hbB
    rcases Six.mem_closure_pair_cases (Six.a_mul_a_self s.h) hb hab (hle hmem) with
      h2 | h2 | h2 | h2
    · exact absurd (h2 ▸ one_mem _) hnot
    · exact ⟨b', hb', 1, one_mem _, by rw [h2, mul_one]⟩
    · exact absurd (h2 ▸ hbB) hnot
    · exact ⟨b', hb', b, hbB0, h2⟩

end Setting0

end Eight2

end CFSG.ComponentClassification.GSThmB
