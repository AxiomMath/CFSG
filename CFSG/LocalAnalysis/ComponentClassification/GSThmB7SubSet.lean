module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7SubL

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem exists_setting_sub (hS : SchreierFor Blueprint.Catalog) (hB1 : ConjFixStatement)
    (hB6 : SylowKernelStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (hCFi : CFProp23IndexReduced) (hCI : GSLit.ClassicalInvolutionInput)
    (hUc : CatalogueU.CatalogAlmostSimpleUnbalancedOutcome) (hDC : CFDoubleCover)
    (hRec : CFSp4RecognitionCI) (hCov : CFSp4CoverInv)
    (hW : ∀ (X : Type) [Group X] [Finite X] (h : Hyp52 X), NF58Setting X h → h.NoFusionW)
    [IsSimpleGroup X] (hnonab : ∃ u v : X, u * v ≠ v * u)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) (h : Hyp52 X)
    (hmax : GSMaximalUnbalancingTriple h.a h.x h.J)
    (hiso : GSIsoAt h.a h.J)
    (hnB1 : ¬ ConclusionB1 h.J) (hnB2a : ¬ ConclusionB2a h.a h.J) (hTab : h.Table517)
    (hKa : conjugate h.K h.a ≠ h.K) :
    ∃ s : Setting X, h.IsX0Min s.y ∧ Prop62Output h s.h s.y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hZK, htype⟩ := h.table517_of_ne hTab hKa
  have hNP := h.normalizer_P_eq hCFi hTab
  have hC := h.centralizer_P_eq hB1 hCF23 hCFc
  have hCN := h.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
  obtain ⟨-, hSa⟩ := h.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
  have hZJ := h.center_eq_bot hB1 hB6 hCF23 hCF24
  have hB2 : 2 < Nat.card h.B := by
    have hne : Nat.card h.B ≠ 2 := fun hB => hnB1
      (lemma71_step1_of_doubleCover hCI hUc hDC hnonab hz hU h hB (hB6 X h)
        (.inr ⟨hKa, hZK, htype⟩))
    have h1 : Nat.card h.B ≠ 1 := fun h1 => h.B_ne_bot (Subgroup.eq_bot_of_card_eq _ h1)
    have h0 : 0 < Nat.card h.B := Nat.card_pos
    omega
  obtain ⟨hBP, -⟩ := h.lemma71_step2a hNP hB2
  obtain ⟨y, hy⟩ := h.exists_isX0Min hBP
  obtain ⟨h', hrel⟩ : ∃ h' : Hyp52 X, Prop62Output h h' y :=
    prop62 hS hnonab hK h hmax hiso hNP.1 hC
      ((normal_subgroupOf_iff_le_normalizer h.J_le).mpr hCN) hSa hBP hy
  have hrel0 := hrel
  obtain ⟨ha', hJ', hB', hK', hc0, hQ', hQ0, hyQ, hyP, hyT, hy2, ⟨hS0E, hS0syl⟩, h61⟩ := hrel
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
    exact hNP
  have hC' := h'.centralizer_P_eq hB1 hCF23 hCFc
  have hCN' := h'.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc
  have hSa' := h'.S_sylow_centralizer hB1 hB6 hCF23 hCF24 hCFc
  have hZJ' := h'.center_eq_bot hB1 hB6 hCF23 hCF24
  have hB2' : 2 < Nat.card h'.B := by rw [hB']; exact hB2
  obtain ⟨-, h2a⟩ := h'.lemma71_step2a hNP' hB2'
  have hyNT : y ∈ normalizer (h'.T : Set X) := mem_normalizer_T_of hyP hyQ
  have hyNB : y ∉ normalizer (h'.B : Set X) := fun hyB =>
    hyT (mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hyP).1, hyB⟩, hyP⟩)
  obtain ⟨hrel2, hB0ne⟩ := h2a y hyNT hyNB
  have hidx : Nat.card h'.B = 2 * Nat.card (B0 h' y) := by
    have h2 := relIndex_mul_card (H := h'.B ⊓ conjugate h'.B y) (K := h'.B)
    rw [hrel2, inf_eq_left.mpr inf_le_left] at h2
    exact h2.symm
  have hQ0' : h'.Q ≤ normalizer (B0 h' y : Set X) := by
    show h'.Q ≤ normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X)
    rw [hB']
    exact hQ0
  have hKa' : conjugate h'.K h'.a ≠ h'.K := by
    rw [hK', ha']
    exact hKa
  have hcy : h.SecCond y :=
    ⟨(mem_inf.mp hy.1).2, hy.2.1, hy.2.2, hy.Q_le_normalizer_B0, hy.mem_normalizer_Q⟩
  have hWh : h.NoFusionW := hW X h ⟨inferInstance, hnonab, hK, hz, hU, hmax, hiso, hnB1, hnB2a⟩
  have hidxh : Nat.card h.B = 2 * Nat.card (B0 h y) := by
    show Nat.card h.B = 2 * Nat.card ↥(h.B ⊓ conjugate h.B y)
    rw [← hB']
    exact hidx
  obtain ⟨⟨p', f', hp', hp2', hf', hLLie⟩, p, f, hp, hp2, hf, h5, hJLie⟩ :=
    lieModel_Lay_sub hB1 hCF23 hCI hDC hRec hCov hcy hCN hSa hNP.1 hWh hidxh hKa hZJ
  have hLay : Lay h y = Lay h' y := by
    show layerIn (centralizer ((h.B ⊓ conjugate h.B y : Subgroup X) : Set X)) =
      layerIn (centralizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X))
    rw [hB']
  rw [hLay] at hLLie
  rw [← hJ'] at hJLie
  have hS0E' : h'.S ⊓ normalizer (B0 h' y : Set X) ≤ centralizer (E h' y : Set X) := by
    show h'.S ⊓ normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X) ≤
      centralizer ((zpowers h'.a ⊔ ⁅h'.B, zpowers y⁆ : Subgroup X) : Set X)
    rw [hB', ha']
    exact hS0E.trans inf_le_right
  have hS0syl' : ∃ R : Sylow 2 ↥(normalizer (B0 h' y : Set X) ⊓ centralizer (E h' y : Set X)),
      (R : Subgroup _) = (h'.S ⊓ normalizer (B0 h' y : Set X)).subgroupOf
        (normalizer (B0 h' y : Set X) ⊓ centralizer (E h' y : Set X)) := by
    show ∃ R : Sylow 2 ↥(normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X) ⊓
        centralizer ((zpowers h'.a ⊔ ⁅h'.B, zpowers y⁆ : Subgroup X) : Set X)),
      (R : Subgroup _) = (h'.S ⊓ normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) :
        Set X)).subgroupOf (normalizer ((h'.B ⊓ conjugate h'.B y : Subgroup X) : Set X) ⊓
          centralizer ((zpowers h'.a ⊔ ⁅h'.B, zpowers y⁆ : Subgroup X) : Set X))
    rw [hB', ha']
    exact hS0syl
  have hZK' : Nat.card (center (h'.K ⧸ pPrimeCore 2 h'.K)) = 2 := by
    rw [hK']
    exact hZK
  exact ⟨
    { h := h', y := y, hT := hNP'.1, hC := hC', hJn := hCN', hSa := hSa', hZJ := hZJ',
      hyP := hyP, hyT := hyT, hy2 := hy2, hyQ := hyQ, hQ := hQ0', h61 := h61, hS0E := hS0E',
      hS0syl := hS0syl', hKa := hKa', hZK := hZK', hVL := V_le_Lay hS hnonab hK h' y hB0ne,
      hB0 := hB0ne,
      p := p, f := f, hp := hp, hp2 := hp2, hf := hf, h5 := h5, hJLie := hJLie, p' := p',
      f' := f', hp' := hp', hp2' := hp2', hf' := hf', hLLie := hLLie }, hy, hrel0⟩

end Seven

end CFSG.ComponentClassification.GSThmB
