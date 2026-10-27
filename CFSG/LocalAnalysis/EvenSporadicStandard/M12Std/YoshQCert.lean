module

public import Certificates.Certificate450002

public section

namespace CFSG.EvenSporadicStandard.M12Std.Yosh

open CFSG.CosetTable

section Parts


theorem yoshQ_check : yoshQCheck = true := Certificates.certificate450002

theorem lemma4_parts :
    relPOK = true ∧
      (∀ α, α < 2 → stepOK α = true ∧ xOK α = true ∧ ∀ β, β < 2 → zOK α β = true) ∧
      xDetermined = true ∧ ∀ α β, α < 2 → β < 2 → qCheck α β = true := by
  have h : lemma4Check = true := by
    have h0 := yoshQ_check
    simp only [yoshQCheck, Bool.and_eq_true] at h0
    exact h0.1.1.1
  unfold lemma4Check at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, fun α hα => ?_, h3, fun α β hα hβ => h4 α ?_ β ?_⟩
  · obtain ⟨h5, h6, h7⟩ := h2 α (by omega)
    exact ⟨h5, h6, fun β hβ => h7 β (by omega)⟩
  · omega
  · omega

theorem lemma5_parts :
    sActOK = true ∧ kCheck = true ∧ rCheck = true ∧ wMemCheck = true ∧ cvCheck = true ∧
      eCheck = true ∧
      (∀ α β, α < 2 → β < 2 →
        relNQCheck α β = true ∧ compFixV α β = true ∧ compInnerV α β = true) ∧
      ∀ α k, α < 2 → k < 2 → nCheck α k = true := by
  have h : lemma5Check = true := by
    have h0 := yoshQ_check
    simp only [yoshQCheck, Bool.and_eq_true] at h0
    exact h0.1.1.2
  unfold lemma5Check at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, fun α β hα hβ => ?_, fun α k hα hk => ?_⟩
  · have := h7 α (by omega) β (by omega)
    exact ⟨this.1.1, this.1.2, this.2⟩
  · exact h8 α (by omega) k (by omega)

theorem lemma5_model_parts :
    eModelCheck = true ∧ ∀ α k, α < 2 → k < 2 → nModelCheck α k = true := by
  have h : lemma5ModelCheck = true := by
    have h0 := yoshQ_check
    simp only [yoshQCheck, Bool.and_eq_true] at h0
    exact h0.1.2
  unfold lemma5ModelCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at h
  obtain ⟨h1, h2⟩ := h
  exact ⟨h1, fun α k hα hk => h2 α (by omega) k (by omega)⟩

theorem qModelOK (α β : ℕ) (hα : α < 2) (hβ : β < 2) :
    ModelOK 24 24 8 (qGens α β) (rel4 α β) 1536 :=
  ⟨lemma4_parts.2.2.2 α β hα hβ, (Certificates.certificate450002.rel4_card α β hα hβ).1,
    (Certificates.certificate450002.rel4_card α β hα hβ).2⟩

theorem eModelOK : ModelOK 16 16 6 eGens relE 128 :=
  ⟨lemma5_parts.2.2.2.2.2.1, Certificates.certificate450002.relE_card.1,
    Certificates.certificate450002.relE_card.2⟩

theorem nModelOK (α k : ℕ) (hα : α < 2) (hk : k < 2) :
    ModelOK 16 16 9 (nGens α k) (relN α α k) 3072 :=
  ⟨lemma5_parts.2.2.2.2.2.2.2 α k hα hk, (Certificates.certificate450002.relN_card α k hα hk).1,
    (Certificates.certificate450002.relN_card α k hα hk).2⟩

end Parts

end CFSG.EvenSporadicStandard.M12Std.Yosh
