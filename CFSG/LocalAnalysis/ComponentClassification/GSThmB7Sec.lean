module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7KBeta
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog71Cover
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7Rec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bTable
public import CFSG.ClassicalInvolution.OrderForm
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bBasic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem table54_of_ne (hT : h.Table54) (hKa : conjugate h.K h.a ≠ h.K) :
    Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2 ∧
      ((∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
          Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin n)) ∧
          Nonempty (h.K ⧸ Open.fusionZStar h.K ≃* alternatingGroup (Fin n))) ∨
        ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
          Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f ∧
          Blueprint.LieModel (h.K ⧸ Open.fusionZStar h.K) .PSL 2 p f) := by
  rcases hT with ⟨n, hn, hJ, hK⟩ | hT | hT | hT | hT | hT | hT
  · rcases hK with ⟨hKa', -⟩ | ⟨-, hZ, hK⟩
    · exact absurd hKa' hKa
    · exact ⟨hZ, .inl ⟨n, hn, hJ, hK⟩⟩
  · exact absurd hT.2.1 hKa
  · exact absurd hT.2.1 hKa
  · obtain ⟨-, -, -, -, -, -, hKa', -⟩ := hT
    exact absurd hKa' hKa
  · obtain ⟨-, -, -, -, -, -, -, hKa', -⟩ := hT
    exact absurd hKa' hKa
  · obtain ⟨p, f, hp, hp2, hf, h5, hJ, -, hZ, hK⟩ := hT
    exact ⟨hZ, .inr ⟨p, f, hp, hp2, hf, h5, hJ, hK⟩⟩
  · obtain ⟨-, -, -, -, -, -, hKa', -⟩ := hT
    exact absurd hKa' hKa

end Hyp52

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem exists_b_mem_K (hB : Nat.card h.B = 2) (hKa : conjugate h.K h.a ≠ h.K)
    (hZK : Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2) :
    ∃ b : H, orderOf b = 2 ∧ h.B = zpowers b ∧ b ∈ h.K := by
  obtain ⟨b, hb, hBb⟩ := exists_eq_zpowers_of_card_two hB
  obtain ⟨β, hβB, hβK, hβ1⟩ := h.toHyp52.exists_mem_B_inf_K hKa hZK
  rw [hBb] at hβB
  have hβ2 : orderOf β = 2 := by
    have hdvd : orderOf β ∣ 2 := by
      have := Subgroup.orderOf_dvd_natCard (zpowers b) hβB
      rwa [Nat.card_zpowers, hb] at this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hβ1
    · exact h1
  exact ⟨b, hb, hBb, eq_of_mem_zpowers_involution hb hβB hβ2 ▸ hβK⟩

include h in
theorem exists_ne_commute_generalizedFitting :
    ∃ u v : ↥(generalizedFitting H), u * v ≠ v * u := by
  obtain ⟨hF, -, -, ⟨⟨-, -, a, b, hab⟩, -⟩, -⟩ := h.generalizedFitting_simple
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨⟨a', by rw [hF]; exact a'.2⟩, ⟨b', by rw [hF]; exact b'.2⟩, fun hc => hab ?_⟩
  have hc' : a' * b' = b' * a' := Subtype.ext (by
    have := congrArg Subtype.val hc
    simpa using this)
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc']

include h in
theorem genFittingFStar_eq : Open.genFittingFStar H = generalizedFitting H := by
  obtain ⟨hF, hsimple, hC, -, -⟩ := h.generalizedFitting_simple
  have : (generalizedFitting H).Normal := LocalCores.generalized_fitting_characteristic.2
  refine ClassicalInvolution.genFittingFStar_eq_of_normal_simple _
    h.exists_ne_commute_generalizedFitting ?_
  rw [hF]
  exact hC

theorem oddLieType_or_M11 (hCI : GSLit.ClassicalInvolutionInput) (hDC : CFDoubleCover)
    (hB : Nat.card h.B = 2) (hKa : conjugate h.K h.a ≠ h.K)
    (hZK : Nat.card (center (h.K ⧸ pPrimeCore 2 h.K)) = 2)
    (htype : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
        Nonempty (h.K ⧸ Open.fusionZStar h.K ≃* alternatingGroup (Fin n))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (h.K ⧸ Open.fusionZStar h.K) .PSL 2 p f) :
    Blueprint.OddLieType ↥(generalizedFitting H) ∨
      Blueprint.NativeSporadic.IsSporadic ↥(generalizedFitting H) .M11 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨b, hb, hBb, hbK⟩ := h.exists_b_mem_K hB hKa hZK
  have hWb : normalizer (h.B : Set H) = centralizer ({b} : Set H) := by
    rw [hBb]
    exact UnbalancedCorr.normalizer_zpowers_eq_centralizer hb
  obtain ⟨hKW, hKpc⟩ := h.isPComponent_K
  rw [hWb] at hKW hKpc
  obtain ⟨hrank, hwit⟩ := rankOne_witness_of_doubleCover hDC h.K h.toHyp52.isQuasisimple_K hZK
    htype
  have hrankK : CFSG.pRank 2 h.K ≤ 1 := by
    have hnd : ¬ 2 ∣ Nat.card (pPrimeCore 2 h.K) := fun hd =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl hd (pPrimeCore_coprime_card (p := 2))
    rwa [GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_two _ hnd]
      at hrank
  have hA : IsQuasisimple (h.K ⧸ CFSG.oddCore h.K) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (GSLit.oddCore_eq_pPrimeCore_two h.K)).symm
      h.toHyp52.isQuasisimple_K
  obtain ⟨-, -, -, -, -, -, r, hr, hSK, -⟩ :=
    UnbalancedGS.rank_one_quasisimple_odd_core_quotient_central_cover.{0, 0} hrankK hA
  obtain ⟨S⟩ : Nonempty (Sylow 2 h.K) := inferInstance
  obtain ⟨eS⟩ := hSK S
  have heq := h.genFittingFStar_eq
  obtain ⟨-, hsimple, -, -, -⟩ := h.generalizedFitting_simple
  have : IsSimpleGroup ↥(Open.genFittingFStar H) := by rw [heq]; exact hsimple
  have hFnonab : ∃ u v : ↥(Open.genFittingFStar H), u * v ≠ v * u := by
    rw [heq]
    exact h.exists_ne_commute_generalizedFitting
  have hout := (hCI H hFnonab b hb h.K hbK (open_isSubnormal_of_isPComponent' hKW hKpc) S
    ⟨r, hr, ⟨eS⟩⟩).1 hwit
  rwa [heq] at hout

theorem lieModel_psp (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCI : GSLit.ClassicalInvolutionInput) (hDC : CFDoubleCover) (hRec : CFSp4RecognitionCI)
    (hB : Nat.card h.B = 2) (hKa : conjugate h.K h.a ≠ h.K) :
    ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧
      Blueprint.LieModel ↥(generalizedFitting H) .PSp 2 p f ∧
      Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f := by
  obtain ⟨hZK, htype⟩ := h.toHyp52.table54_of_ne (h.toHyp52.table hB1 hCF23) hKa
  have hK : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
        Nonempty (h.K ⧸ Open.fusionZStar h.K ≃* alternatingGroup (Fin n))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (h.K ⧸ Open.fusionZStar h.K) .PSL 2 p f := by
    rcases htype with ⟨n, hn, -, hKn⟩ | ⟨p, f, hp, hp2, hf, h5, -, hKL⟩
    · exact .inl ⟨n, hn, hKn⟩
    · exact .inr ⟨p, f, hp, hp2, hf, h5, hKL⟩
  have hJ : (∃ n : ℕ, (n = 5 ∨ n = 6 ∨ n = 7) ∧
        Nonempty (h.J ⧸ pPrimeCore 2 h.J ≃* alternatingGroup (Fin n))) ∨
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (h.J ⧸ pPrimeCore 2 h.J) .PSL 2 p f := by
    rcases htype with ⟨n, hn, hJn, -⟩ | ⟨p, f, hp, hp2, hf, h5, hJL, -⟩
    · exact .inl ⟨n, hn, hJn⟩
    · exact .inr ⟨p, f, hp, hp2, hf, h5, hJL⟩
  exact hRec H h (h.oddLieType_or_M11 hCI hDC hB hKa hZK hK) hB hKa hZK hJ

end Hyp59

end CFSG.ComponentClassification.GSThmB
