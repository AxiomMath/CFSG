module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubQ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubCorr
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubSec
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubStar
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubSyl

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

namespace SubQAux

theorem exists_hyp59_subQuot (hc : h.SecCond y) (h₁ : Hyp52 ↥(h.secSubImg y))
    (ha₁ : h₁.a = hc.subA) (hJ₁ : h₁.J = h.subJ y) (hB₁ : h₁.B = h.subB y)
    (hK₁ : h₁.K = h.subK y) (hx₁ : h₁.x = hc.subX) (hxP₁ : hc.subX ∈ h₁.P)
    (hQ₁ : h₁.Q = (h.secImage y h.Q).subgroupOf (h.secSubImg y))
    (hT₁ : h₁.T = (h.secImage y h.T).subgroupOf (h.secSubImg y)) :
    ∃ h' : Hyp59 (h.subQuot y),
      h'.a = h.subQ y ⟨h.a, hc.a_mem_secSub⟩ ∧
      h'.J = ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.B = (h.B.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.K = (h.K.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.x = h.subQ y ⟨y, hc.y_mem_secSub⟩ ∧
      h'.S = h₁.S.map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.toHyp52.P = h₁.P.map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.toHyp52.Q = (h.Q.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.toHyp52.T = (h.T.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      Nonempty (↥h'.K ⧸ Open.fusionZStar ↥h'.K ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) ∧
      Nonempty (↥h'.J ⧸ Open.fusionZStar ↥h'.J ≃* ↥h.J ⧸ Open.fusionZStar ↥h.J) ∧
      (center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥ →
        Nonempty (↥h'.J ⧸ pPrimeCore 2 ↥h'.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J)) ∧
      (center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥ →
        Nonempty (↥h'.K ⧸ pPrimeCore 2 ↥h'.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K)) ∧
      (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
      (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) ∧
      Nonempty (↥h'.toHyp52.T ⧸ h'.B.subgroupOf h'.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) ∧
      Nat.card h'.B * Nat.card (h.secB0 y) = Nat.card h.B := by
  obtain ⟨h', ha', hJ', hS'', hB', hK', hx'⟩ := h₁.quotient_oddCore
  obtain ⟨hP', hQ'', hT'⟩ := quotient_PQT h₁ h' hJ' hS'' hB'
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
  have hK'' := hK₁ ▸ hK'
  have hJ'' := hJ₁ ▸ hJ'
  have hB'' : h'.B = (h.B.subgroupOf (h.secSub y)).map (h.subQ y) := by
    rw [hB', hB₁, hc.map_subQ_B]
  obtain ⟨hconj, hinner⟩ := hc.conj_K_of_sub h₁ ha₁ hK₁ ha' hK'
  refine ⟨⟨h', pPrimeCore_quotient_pPrimeCore_eq_bot 2, Or.inl (mem_inf.mpr ⟨hxP', hxQ'⟩)⟩, ?_⟩
  dsimp only
  refine ⟨by rw [ha', ha₁, hc.subQ_a], by rw [hJ'', map_subQ_secJ0], hB'',
    by rw [hK'', hc.map_subQ_K], by rw [hx', hx₁, hc.subQ_y], hS'', hP',
    by rw [hQ'', hQ₁, hc.map_subQ_Q], by rw [hT', hT₁, hc.map_subQ_T],
    hc.fusionZStar_K_of_sub hK'', fusionZStar_J_of_sub hJ'', pPrimeCore_J_of_sub hJ'',
    hc.pPrimeCore_K_of_sub hK'', hconj, hinner, hc.T_of_sub h₁ hB₁ hT₁ hB' hT', ?_⟩
  rw [hB'']
  exact card_map_subQ_mul (B5a.isPGroup_B h) (h.secB0_le_B y) hc.B_le_secSub

theorem exists_hyp59_subQuot_of_sylow (hc : h.SecCond y) (S' : Subgroup ↥(h.secSubImg y))
    (hS'le : S' ≤ centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
      normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)))
    (hS'syl : ∃ R : Sylow 2 ↥(centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))),
      (R : Subgroup _) = S'.subgroupOf (centralizer ({hc.subA} : Set ↥(h.secSubImg y)) ⊓
        normalizer ((h.subJ y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))))
    (hSS' : h.subS y ≤ S')
    (h7 : ∀ E : Subgroup ↥(h.secSubImg y), E ≤ S' ⊓ coreActionKernel (h.subJ y) →
      (Nat.card (h.subB y) < Nat.card E ∨ (Nat.card E = Nat.card (h.subB y) ∧
        Nat.card ↥(S' ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) :
          Set ↥(h.secSubImg y))) < Nat.card ↥(S' ⊓ normalizer (E : Set ↥(h.secSubImg y))))) →
      ∃ L : Subgroup ↥(h.secSubImg y), IsoCorrSub hc.subA (h.subJ y) E L)
    (hQ' : S' ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y)) =
      (h.secImage y h.Q).subgroupOf (h.secSubImg y)) :
    ∃ h' : Hyp59 (h.subQuot y),
      h'.a = h.subQ y ⟨h.a, hc.a_mem_secSub⟩ ∧
      h'.J = ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.B = (h.B.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.K = (h.K.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.x = h.subQ y ⟨y, hc.y_mem_secSub⟩ ∧
      h'.S = S'.map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.toHyp52.P = (S' ⊓ coreActionKernel (h.subJ y)).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) ∧
      h'.toHyp52.Q = (h.Q.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.toHyp52.T = (h.T.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      Nonempty (↥h'.K ⧸ Open.fusionZStar ↥h'.K ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) ∧
      Nonempty (↥h'.J ⧸ Open.fusionZStar ↥h'.J ≃* ↥h.J ⧸ Open.fusionZStar ↥h.J) ∧
      (center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥ →
        Nonempty (↥h'.J ⧸ pPrimeCore 2 ↥h'.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J)) ∧
      (center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥ →
        Nonempty (↥h'.K ⧸ pPrimeCore 2 ↥h'.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K)) ∧
      (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
      (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) ∧
      Nonempty (↥h'.toHyp52.T ⧸ h'.B.subgroupOf h'.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) ∧
      Nat.card h'.B * Nat.card (h.secB0 y) = Nat.card h.B := by
  have hQS : (h.secImage y h.Q).subgroupOf (h.secSubImg y) ≤ S' := by
    rw [← hc.subS_inf_normalizer]
    exact inf_le_left.trans hSS'
  have hT₁ : (h.subHyp52 hc S' hS'le hS'syl hSS' h7).T =
      (h.secImage y h.T).subgroupOf (h.secSubImg y) := by
    show (S' ⊓ normalizer ((h.subB y : Subgroup ↥(h.secSubImg y)) : Set ↥(h.secSubImg y))) ⊓
      (S' ⊓ coreActionKernel (h.subJ y)) = _
    rw [hQ', hc.secImage_T_eq, Sub58.inf_subgroupOf, ← coreActionKernel_subJ]
    apply le_antisymm
    · exact inf_le_inf_left _ inf_le_right
    · exact le_inf inf_le_left (le_inf (inf_le_left.trans hQS) inf_le_right)
  have hxP₁ : hc.subX ∈ S' ⊓ coreActionKernel (h.subJ y) := by
    refine inf_le_inf_right _ hSS' (?_ : hc.subX ∈ h.subS y ⊓ coreActionKernel (h.subJ y))
    rw [hc.subS_inf_coreActionKernel]
    exact mem_map_of_mem _ (show (⟨y, hc.y_mem_G0⟩ : ↥(h.secG0 y)) ∈
      h.P.subgroupOf (h.secG0 y) from hc.mem_P)
  exact exists_hyp59_subQuot hc (h.subHyp52 hc S' hS'le hS'syl hSS' h7) rfl rfl rfl rfl rfl
    hxP₁ hQ' hT₁

end SubQAux

theorem SecCond.exists_hyp59_subQuot_of_T_eq (hc : h.SecCond y)
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hSa : ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set X)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set X)))
    (hT : h.T = h.B ⊔ zpowers h.a) (hW : h.NoFusionW) :
    ∃ h' : Hyp59 (h.subQuot y),
      h'.a = h.subQ y ⟨h.a, hc.a_mem_secSub⟩ ∧
      h'.J = ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.B = (h.B.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.K = (h.K.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.x = h.subQ y ⟨y, hc.y_mem_secSub⟩ ∧
      ((h.S ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) ≤ h'.S ∧
      ((h.P ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) ≤ h'.toHyp52.P ∧
      h'.toHyp52.Q = (h.Q.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.toHyp52.T = (h.T.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      Nonempty (↥h'.K ⧸ Open.fusionZStar ↥h'.K ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) ∧
      Nonempty (↥h'.J ⧸ Open.fusionZStar ↥h'.J ≃* ↥h.J ⧸ Open.fusionZStar ↥h.J) ∧
      (center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥ →
        Nonempty (↥h'.J ⧸ pPrimeCore 2 ↥h'.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J)) ∧
      (center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥ →
        Nonempty (↥h'.K ⧸ pPrimeCore 2 ↥h'.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K)) ∧
      (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
      (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) ∧
      Nonempty (↥h'.toHyp52.T ⧸ h'.B.subgroupOf h'.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) ∧
      Nat.card h'.B * Nat.card (h.secB0 y) = Nat.card h.B := by
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
  obtain ⟨h', ha', hJ', hB', hK', hx', hS'', hP'', hQ'', hT'', eK, eJ, hOJ, hOK, hconj, hinner,
    eT, hcard⟩ := SubQAux.exists_hyp59_subQuot_of_sylow hc S' hS'le hS'syl hSS'
      (fun E hE hEc => hc.isoCorr_subStar hCN hSa hW hT hS'le hS'2 hSS' E hE hEc)
      (hc.inf_normalizer_subB_eq hCN hSa hW hS'2 (hS'le.trans inf_le_left) hSS')
  refine ⟨h', ha', hJ', hB', hK', hx', ?_, ?_, hQ'', hT'', eK, eJ, hOJ, hOK, hconj, hinner, eT,
    hcard⟩
  · rw [hS'', map_subQ_S]
    exact map_mono hSS'
  · rw [hP'', map_subQ_P, ← hc.subS_inf_coreActionKernel]
    exact map_mono (inf_le_inf_right _ hSS')

theorem SecCond.exists_hyp59_subQuot_of_kappa (hc : h.SecCond y)
    (hB : Seven.IsSylowIn (h.S ⊓ h.secG0 y) (centralizer ({h.a} : Set X) ⊓ h.secG0 y))
    (hCN : centralizer ({h.a} : Set X) ≤ normalizer (h.J : Set X))
    (hκ : ∀ l ∈ layerIn (centralizer (h.secB0 y : Set X)),
      l ∈ normalizer ((h.secJ0 y ⊔ h.secB0 y : Subgroup X) : Set X) →
      l * h.a * l⁻¹ * h.a⁻¹ ∈ h.secB0 y → l * h.a = h.a * l) :
    ∃ h' : Hyp59 (h.subQuot y),
      h'.a = h.subQ y ⟨h.a, hc.a_mem_secSub⟩ ∧
      h'.J = ((h.secJ0 y).subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.B = (h.B.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.K = (h.K.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.x = h.subQ y ⟨y, hc.y_mem_secSub⟩ ∧
      h'.S = ((h.S ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.toHyp52.P = ((h.P ⊓ h.secG0 y).subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.toHyp52.Q = (h.Q.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      h'.toHyp52.T = (h.T.subgroupOf (h.secSub y)).map (h.subQ y) ∧
      Nonempty (↥h'.K ⧸ Open.fusionZStar ↥h'.K ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) ∧
      Nonempty (↥h'.J ⧸ Open.fusionZStar ↥h'.J ≃* ↥h.J ⧸ Open.fusionZStar ↥h.J) ∧
      (center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥ →
        Nonempty (↥h'.J ⧸ pPrimeCore 2 ↥h'.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J)) ∧
      (center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥ →
        Nonempty (↥h'.K ⧸ pPrimeCore 2 ↥h'.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K)) ∧
      (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
      (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) ∧
      Nonempty (↥h'.toHyp52.T ⧸ h'.B.subgroupOf h'.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) ∧
      Nat.card h'.B * Nat.card (h.secB0 y) = Nat.card h.B := by
  obtain ⟨h', ha', hJ', hB', hK', hx', hS'', hP'', hQ'', hT'', eK, eJ, hOJ, hOK, hconj, hinner,
    eT, hcard⟩ := SubQAux.exists_hyp59_subQuot_of_sylow hc (h.subS y) hc.subS_le
      (hc.subS_sylow hB hCN hκ) le_rfl (fun E hE hEc => hc.isoCorr_subBar E hE hEc)
      hc.subS_inf_normalizer
  refine ⟨h', ha', hJ', hB', hK', hx', ?_, ?_, hQ'', hT'', eK, eJ, hOJ, hOK, hconj, hinner, eT,
    hcard⟩
  · rw [hS'', map_subQ_S]
  · rw [hP'', hc.subS_inf_coreActionKernel, map_subQ_P]

end Hyp52

end CFSG.ComponentClassification.GSThmB
