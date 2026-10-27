module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubCPrimeA
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubHypWQuot

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

theorem SecCond.exists_hyp59W_of_sub (hc : h.SecCond y) (h₁ : Hyp52W ↥(h.secSubImg y))
    (hS₁ : IsPGroup 2 h₁.S) (ha₁ : h₁.a = hc.subA) (hJ₁ : h₁.J = h.subJ y)
    (hB₁ : h₁.B = h.subB y) (hK₁ : h₁.K = h.subK y) (hx₁ : h₁.x = hc.subX)
    (hSS : h.subS y ≤ h₁.S) (hxP₁ : hc.subX ∈ h₁.P)
    (hQ₁ : h₁.Q = (h.secImage y h.Q).subgroupOf (h.secSubImg y))
    (hT₁ : h₁.T = (h.secImage y h.T).subgroupOf (h.secSubImg y)) :
    ∃ h' : Hyp59W (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y)),
      h'.a = QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) hc.subA ∧
      h'.J = (h.subJ y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.B = (h.subB y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.K = (h.subK y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.x = QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) hc.subX ∧
      (h.subS y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ≤ h'.S ∧
      Nonempty (↥h'.toHyp52W.T ⧸ h'.B.subgroupOf h'.toHyp52W.T ≃*
        ↥h.T ⧸ h.B.subgroupOf h.T) := by
  obtain ⟨h', ha', hJ', hS'', hB', hK', hx'⟩ := h₁.quotient_oddCore
  obtain ⟨hP', hQ'', hT'⟩ := Hyp52W.quotient_PQT h₁ hS₁ h' hJ' hS'' hB'
  have hQH : h.secImage y h.Q ≤ h.secSubImg y :=
    (secImage_mono (inf_le_left : h.Q ≤ h.S)).trans (h.secImage_S_le y)
  have hxQ₁ : h₁.x ∈ normalizer (h₁.Q : Set ↥(h.secSubImg y)) := by
    rw [hQ₁, hx₁, ← subgroupOf_normalizer_eq hQH, mem_subgroupOf]
    exact secMk_mem_normalizer hc.y_mem_G0 hc.mem_normalizer_Q
  have hxP' : h'.x ∈ h'.P := by
    rw [hP', hx', hx₁]
    exact mem_map_of_mem _ hxP₁
  have hxQ' : h'.x ∈ normalizer (h'.Q : Set _) := by
    rw [hQ'', hx']
    exact le_normalizer_map _ (mem_map_of_mem _ hxQ₁)
  obtain ⟨e1⟩ := Hyp52W.nonempty_quotient_T_equiv h₁ hS₁ h' hB' hT'
  obtain ⟨e2⟩ := hc.nonempty_quot_equiv_T hB₁ hT₁
  exact ⟨⟨h', pPrimeCore_quotient_pPrimeCore_eq_bot 2, Or.inl (mem_inf.mpr ⟨hxP', hxQ'⟩)⟩,
    by rw [ha', ha₁], by rw [hJ', hJ₁], by rw [hB', hB₁], by rw [hK', hK₁], by rw [hx', hx₁],
    by rw [hS'']; exact map_mono hSS, ⟨e1.trans e2⟩⟩

theorem SecCond.exists_hyp59W_subsection (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    (hW : h.NoFusionW) :
    ∃ h' : Hyp59W (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y)),
      h'.a = QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) hc.subA ∧
      h'.J = (h.subJ y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.B = (h.subB y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.K = (h.subK y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.x = QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) hc.subX ∧
      (h.subS y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ≤ h'.S ∧
      Nonempty (↥h'.toHyp52W.T ⧸ h'.B.subgroupOf h'.toHyp52W.T ≃*
        ↥h.T ⧸ h.B.subgroupOf h.T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
    normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) with hC
  have hSC : h.subS y ≤ C := hc.subS_le
  have hS2 : IsPGroup 2 (h.subS y) :=
    (((B5a.isPGroup_S h).comap_subtype (K := h.secG0 y)).map (h.secMk y)).comap_subtype
  obtain ⟨R, hR⟩ := (hS2.comap_subtype (K := C)).exists_le_sylow
  set S' := (R : Subgroup ↥C).map C.subtype with hS'
  have hS'le : S' ≤ C := map_subtype_le _
  have hS'syl : ∃ R' : Sylow 2 ↥C, (R' : Subgroup ↥C) = S'.subgroupOf C :=
    ⟨R, (comap_map_eq_self_of_injective C.subtype_injective _).symm⟩
  have hSS' : h.subS y ≤ S' := fun z hz =>
    ⟨⟨z, hSC hz⟩, hR (show (⟨z, hSC hz⟩ : ↥C) ∈ (h.subS y).subgroupOf C from hz), rfl⟩
  have hS'2 : IsPGroup 2 S' := R.isPGroup'.map _
  have hQ' := hc.inf_normalizer_subB_eq hCN hSa hW hS'2 (hS'le.trans inf_le_left) hSS'
  have hQS : (h.secImage y h.Q).subgroupOf (h.secSubImg y) ≤ S' := by
    rw [← hc.subS_inf_normalizer]
    exact inf_le_left.trans hSS'
  have hT₁ : (S' ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) ⊓
      (S' ⊓ coreActionKernel (h.subJ y)) = (h.secImage y h.T).subgroupOf (h.secSubImg y) := by
    rw [hQ', hc.secImage_T_eq, Sub58.inf_subgroupOf, ← coreActionKernel_subJ]
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hQS) inf_le_right)
  have hxP₁ : hc.subX ∈ S' ⊓ coreActionKernel (h.subJ y) := by
    refine inf_le_inf_right _ hSS' (?_ : hc.subX ∈ h.subS y ⊓ coreActionKernel (h.subJ y))
    rw [hc.subS_inf_coreActionKernel]
    exact mem_map_of_mem _ (show (⟨y, hc.y_mem_G0⟩ : ↥(h.secG0 y)) ∈
      h.P.subgroupOf (h.secG0 y) from hc.mem_P)
  exact hc.exists_hyp59W_of_sub (h.subHyp52W hc S' hS'le hS'syl hSS'
      (hc.isoCorr_of_le_T_sub hQ') (hc.isoCorr_of_mem_sub (hS'le.trans inf_le_left) hS'2))
    hS'2 rfl rfl rfl rfl rfl hSS' hxP₁ hQ' hT₁

end Hyp52

end CFSG.ComponentClassification.GSThmB
