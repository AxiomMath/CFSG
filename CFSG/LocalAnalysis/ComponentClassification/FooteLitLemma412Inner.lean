module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412Pair
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma411

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem mem_coreActionKernel_conjugate_iff {J : Subgroup G} {g x : G} :
    x ∈ coreActionKernel (conjugate J g) ↔ g * x * g⁻¹ ∈ coreActionKernel J := by
  refine ⟨fun hx => ?_, CFSG.ComponentClassification.FooteLit.mem_coreActionKernel_conjugate⟩
  have h1 : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ coreActionKernel (conjugate J g) := by
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group]
  have h2 := CFSG.ComponentClassification.FooteLit.mem_coreActionKernel_conjugate h1
  rwa [UnbalancedLayer.conjugate_conjugate_inv] at h2

theorem exists_isSylowOf_centralizer_le_normalizer (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) {M : Subgroup G} (hM : IsFooteM L M) {w : G}
    (hw : orderOf w = 2) (hwC : w ∈ coreActionKernel M) :
    ∃ S : Subgroup G, IsSylowOf 2 S (centralizer ({w} : Set G)) ∧
      S ≤ normalizer (M : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hCw : centralizer ({w} : Set G) ≤ normalizer (M : Set G)
  · obtain ⟨S, hS⟩ := exists_isSylowOf 2 (centralizer ({w} : Set G))
    exact ⟨S, hS, hS.le.trans hCw⟩
  obtain ⟨hBN, -, hBw, -, Q, hQB, hQC, F, hFQ, hF2, hF8⟩ :=
    foote_lemma_4_9_core h h47 hST hM hw hwC hCw
  have hQw : Q ≤ centralizer ({w} : Set G) := hQB.le.trans hBw
  obtain ⟨S, hS, hQS⟩ := exists_isSylowOf_ge_of_le hQw hQB.isPGroup
  refine ⟨S, hS, ?_⟩
  have hSB : S ⊓ footeB L w = Q :=
    (hQB.eq_of_le (le_inf hQS hQB.le) inf_le_right (hS.isPGroup.to_le inf_le_left))
  obtain ⟨W, hW, hWF⟩ := exists_isKleinFour_le hF2 (by omega)
  have hNQ : normalizer (Q : Set G) ≤ normalizer (M : Set G) :=
    foote_cor_4_8_iv h h47 hST hM hQC hW (hWF.trans hFQ)
  intro s hs
  apply hNQ
  rw [mem_normalizer_iff]
  intro x
  rw [← hSB, mem_inf, mem_inf]
  have h1 := mem_normalizer_iff.mp (le_normalizer hs) x
  have h2 := mem_normalizer_iff.mp (hBN (hS.le hs)) x
  rw [h1, h2]

theorem FooteBadPair.false_of_inner (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) {M : Subgroup G} (hM : IsFooteM L M)
    (hH : ∀ t : G, FooteInCC M t → ∀ u ∈ footeK L t, FooteInCC M u → u = t)
    (hPE : FooteEvenOrNormalizes M) {z g : G} (hp : FooteBadPair M z g) {w : G}
    (hw : orderOf w = 2) (hwC : w ∈ coreActionKernel M)
    (hwu : w * (g⁻¹ * z * g) = (g⁻¹ * z * g) * w)
    (hwin : w ∈ conjugate M g ⊔ coreActionKernel (conjugate M g)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM' := isFooteM_conjugate h hM g
  obtain ⟨E', hE', hE'2, hE'8⟩ := exists_card_eight_le_inf_centralizer h h47 hM' hw hwin
  obtain ⟨S, hS, hSN⟩ := exists_isSylowOf_centralizer_le_normalizer h h47 hST hM hw hwC
  have hE'p : IsPGroup 2 E' := IsPGroup.of_card (n := 3) (by rw [hE'8]; norm_num)
  obtain ⟨c', hc', hkc'⟩ := exists_conj_le_of_isSylowOf hS (hE'.trans inf_le_right) hE'p
  set E := conjugate E' g⁻¹ with hEdef
  have hEC : E ≤ coreActionKernel M := by
    intro x hx
    rw [hEdef, mem_conjugate_iff] at hx
    have h1 := (mem_inf.mp (hE' hx)).1
    rw [mem_coreActionKernel_conjugate_iff] at h1
    rwa [show g * (g⁻¹ * x * g⁻¹⁻¹) * g⁻¹ = x by group] at h1
  obtain ⟨z₁, hz₁E, hz₁1, hCz₁⟩ := foote_lemma_4_11 h h47 hST hAsc h2An hM hH hEC
    (sq_eq_one_of_mem_conjugate hE'2 g⁻¹) (by rw [card_conjugate_eq_card, hE'8]; norm_num)
  have hgc' : g * c' ∈ normalizer (M : Set G) := by
    by_contra hgc'
    have hz₁ : orderOf z₁ = 2 := orderOf_eq_prime (sq_eq_one_of_mem_conjugate hE'2 g⁻¹ z₁ hz₁E)
      hz₁1
    have hp₁ : FooteBadPair M z₁ (g * c') := by
      refine ⟨hz₁, hEC hz₁E, hCz₁, ?_, hgc'⟩
      rw [hEdef, mem_conjugate_iff] at hz₁E
      have h1 := hSN (hkc' _ hz₁E)
      rwa [show c'⁻¹ * (g⁻¹ * z₁ * g⁻¹⁻¹) * c' = (g * c')⁻¹ * z₁ * (g * c') by group] at h1
    refine hp₁.false_of_card_eight h h47 hST hA5 hE8 hK hcalc hM hPE (E := conjugate E' c') ?_
      (sq_eq_one_of_mem_conjugate hE'2 c') (by rw [card_conjugate_eq_card, hE'8])
    intro x hx
    rw [mem_conjugate_iff] at hx
    refine mem_inf.mpr ⟨?_, hSN (by
      have h0 := hkc' _ hx
      rwa [show c'⁻¹ * (c' * x * c'⁻¹) * c' = x by group] at h0)⟩
    have h1 := (mem_inf.mp (hE' hx)).1
    rw [mem_coreActionKernel_conjugate_iff] at h1 ⊢
    simpa [mul_assoc] using h1
  set n := g * c' with hn
  have hgnc : g = n * c'⁻¹ := by rw [hn]; group
  have hp₂ : FooteBadPair M (n⁻¹ * z * n) c'⁻¹ := by
    obtain ⟨hz, hzC, hCz, huN, hgN⟩ := hp
    refine ⟨?_, ?_, ?_, ?_, fun hc => hgN (hgnc ▸ mul_mem hgc' hc)⟩
    · rw [show n⁻¹ * z * n = MulAut.conj n⁻¹ z by rw [MulAut.conj_apply, inv_inv],
        MulEquiv.orderOf_eq, hz]
    · exact (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M
        (inv_mem hgc')) z).mp hzC |> fun h1 => by simpa using h1
    · intro x hx
      have hx' : n * x * n⁻¹ ∈ centralizer ({z} : Set G) := by
        rw [mem_centralizer_singleton_iff] at hx ⊢
        calc n * x * n⁻¹ * z = n * (x * (n⁻¹ * z * n)) * n⁻¹ := by group
          _ = n * ((n⁻¹ * z * n) * x) * n⁻¹ := by rw [hx]
          _ = z * (n * x * n⁻¹) := by group
      have h1 := hCz hx'
      rw [show x = n⁻¹ * (n * x * n⁻¹) * n by group]
      exact mul_mem (mul_mem (inv_mem hgc') h1) hgc'
    · rw [show c'⁻¹⁻¹ * (n⁻¹ * z * n) * c'⁻¹ = g⁻¹ * z * g by rw [hgnc]; group]
      exact huN
  have hwc' : c' * w = w * c' := mem_centralizer_singleton_iff.mp hc'
  refine hp₂.false_of_involution h h47 hST hM hw hwC ?_ ?_
  · rw [mem_coreActionKernel_conjugate_iff]
    rw [show c'⁻¹ * w * c'⁻¹⁻¹ = w by rw [inv_inv, mul_assoc, ← hwc']; group]
    exact hwC
  · rw [show c'⁻¹⁻¹ * (n⁻¹ * z * n) * c'⁻¹ = g⁻¹ * z * g by rw [hgnc]; group]
    exact hwu

end CFSG.ComponentClassification.FooteLit
