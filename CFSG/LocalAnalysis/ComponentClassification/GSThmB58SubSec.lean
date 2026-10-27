module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubHyp
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecData

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

namespace SecCond

variable (hc : h.SecCond y)
include hc

theorem subA_mem_sup_iff :
    hc.subA ∈ h.subK y ⊔ coreActionKernel (h.subK y) ↔ h.a ∈ h.K ⊔ coreActionKernel h.K := by
  have hKH := secImage_K_le hc
  have hCK : coreActionKernel (h.subK y) =
      (coreActionKernel (h.secImage y h.K)).subgroupOf (h.secSubImg y) :=
    B5a.coreActionKernel_subgroupOf hKH
  rw [← hc.secA_mem_sup_iff]
  constructor
  · intro ha
    obtain ⟨k, hk, c, hck, hkc⟩ := B5a.exists_mul_of_mem_sup_coreActionKernel ha
    rw [hCK] at hck
    have h1 : hc.secA = (k : h.secBar y) * (c : h.secBar y) := by
      rw [← coe_mul, hkc]
    rw [h1]
    exact mul_mem (mem_sup_left (show (k : h.secBar y) ∈ h.secImage y h.K from hk))
      (mem_sup_right (show (c : h.secBar y) ∈ coreActionKernel (h.secImage y h.K) from hck))
  · intro ha
    obtain ⟨k, hk, c, hck, hkc⟩ := B5a.exists_mul_of_mem_sup_coreActionKernel ha
    have hkH : k ∈ h.secSubImg y := hKH hk
    have hcH : c ∈ h.secSubImg y := by
      have h1 : c = k⁻¹ * hc.secA := by rw [← hkc]; group
      rw [h1]
      exact mul_mem (inv_mem hkH) hc.secA_mem_secSubImg
    have h1 : hc.subA = (⟨k, hkH⟩ : ↥(h.secSubImg y)) * ⟨c, hcH⟩ := Subtype.ext hkc.symm
    rw [h1]
    refine mul_mem (mem_sup_left (show (⟨k, hkH⟩ : ↥(h.secSubImg y)) ∈ h.subK y from hk))
      (mem_sup_right ?_)
    rw [hCK]
    exact hck

theorem conjugate_subK_eq_iff :
    conjugate (h.subK y) hc.subA = h.subK y ↔ conjugate h.K h.a = h.K := by
  have hKH := secImage_K_le hc
  rw [← conjugate_secK_eq_iff hc, conjugate_subgroupOf_eq]
  constructor
  · intro heq
    have hKaH : conjugate (h.secImage y h.K) hc.secA ≤ h.secSubImg y := by
      rw [← secImage_conjugate h.K hc.a_mem_G0]
      exact secImage_mono (conjugate_K_le_secSub hc)
    exact Sub58.subgroupOf_injective_of_le hKaH hKH heq
  · intro heq
    show (conjugate (h.secImage y h.K) hc.secA).subgroupOf (h.secSubImg y) = h.subK y
    rw [heq]

end SecCond

theorem SecCond.nonempty_subT_equiv (hc : h.SecCond y) (h₁ : Hyp52 ↥(h.secSubImg y))
    (hB₁ : h₁.B = h.subB y) (hT₁ : h₁.T = (h.secImage y h.T).subgroupOf (h.secSubImg y)) :
    Nonempty (↥h₁.T ⧸ h₁.B.subgroupOf h₁.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) := by
  have hTH : h.secImage y h.T ≤ h.secSubImg y :=
    (secImage_mono (inf_le_left.trans inf_le_left : h.T ≤ h.S)).trans (h.secImage_S_le y)
  have hTG : h.T ≤ h.secG0 y := hc.T_le_G0
  have hmem : ∀ t : ↥h.T, h.secMk y (inclusion hTG t) ∈ h.secImage y h.T := fun t =>
    mem_map_of_mem _ (show inclusion hTG t ∈ h.T.subgroupOf (h.secG0 y) from t.2)
  let f₀ : ↥h.T →* ↥(h.secSubImg y) :=
    ((h.secMk y).comp (inclusion hTG)).codRestrict _ fun t => hTH (hmem t)
  have hf₀ : ∀ t, f₀ t ∈ h₁.T := fun t => by
    rw [hT₁, mem_subgroupOf]
    exact hmem t
  let f : ↥h.T →* ↥h₁.T := f₀.codRestrict _ hf₀
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    rw [hT₁, mem_subgroupOf] at hz
    obtain ⟨t, ht, htz⟩ := mem_map.mp hz
    exact ⟨⟨t, ht⟩, Subtype.ext (Subtype.ext htz)⟩
  refine B5a.nonempty_quotient_equiv_of_surjective f hf fun t => ?_
  rw [hB₁, mem_subgroupOf]
  exact secMk_mem_secImage_iff (h.secB0_le_B y) _

section Invariants

variable {h' : Hyp52 (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y))}

theorem SecCond.fusionZStar_K_of_sub (hc : h.SecCond y)
    (hK' : h'.K = (h.subK y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))) :
    Nonempty (↥h'.K ⧸ Open.fusionZStar ↥h'.K ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) := by
  rw [hK']
  obtain ⟨e1⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv _ OddQuot.not_two_dvd_card_ker
    (h.subK y)
  obtain ⟨e2⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe (secImage_K_le hc)))
  obtain ⟨e3⟩ := nonempty_secK_fusionZStar_equiv (h := h) (y := y)
  exact ⟨e1.symm.trans (e2.trans e3)⟩

theorem fusionZStar_J_of_sub
    (hJ' : h'.J = (h.subJ y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))) :
    Nonempty (↥h'.J ⧸ Open.fusionZStar ↥h'.J ≃* ↥h.J ⧸ Open.fusionZStar ↥h.J) := by
  rw [hJ']
  obtain ⟨e1⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv _ OddQuot.not_two_dvd_card_ker
    (h.subJ y)
  obtain ⟨e2⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
      (subgroupOfEquivOfLe (h.secImage_secJ0_le y)))
  obtain ⟨e3⟩ := nonempty_secJ_fusionZStar_equiv (h := h) (y := y)
  exact ⟨e1.symm.trans (e2.trans e3)⟩

theorem pPrimeCore_J_of_sub
    (hJ' : h'.J = (h.subJ y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))))
    (hZ : center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥) :
    Nonempty (↥h'.J ⧸ pPrimeCore 2 ↥h'.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J) := by
  rw [hJ']
  obtain ⟨e1⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv _ OddQuot.not_two_dvd_card_ker
    (h.subJ y)
  obtain ⟨e3⟩ := nonempty_secJ_pPrimeCore_equiv (y := y) hZ
  exact ⟨e1.symm.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (subgroupOfEquivOfLe (h.secImage_secJ0_le y))).trans e3)⟩

theorem SecCond.pPrimeCore_K_of_sub (hc : h.SecCond y)
    (hK' : h'.K = (h.subK y).map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))))
    (hZ : center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥) :
    Nonempty (↥h'.K ⧸ pPrimeCore 2 ↥h'.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K) := by
  rw [hK']
  obtain ⟨e1⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv _ OddQuot.not_two_dvd_card_ker
    (h.subK y)
  obtain ⟨e3⟩ := nonempty_secK_pPrimeCore_equiv (y := y) hZ
  exact ⟨e1.symm.trans ((UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (subgroupOfEquivOfLe (secImage_K_le hc))).trans e3)⟩

theorem SecCond.conj_K_of_sub (hc : h.SecCond y) (h₁ : Hyp52 ↥(h.secSubImg y))
    (ha₁ : h₁.a = hc.subA) (hK₁ : h₁.K = h.subK y)
    (ha' : h'.a = QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)) h₁.a)
    (hK' : h'.K = h₁.K.map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))) :
    (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
      (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) := by
  rw [hK', ha']
  refine ⟨(map_conjugate_K_eq_iff h₁).trans ?_, (map_mem_sup_coreActionKernel_iff h₁).trans ?_⟩
  · rw [hK₁, ha₁]
    exact hc.conjugate_subK_eq_iff
  · rw [hK₁, ha₁]
    exact hc.subA_mem_sup_iff

theorem SecCond.T_of_sub (hc : h.SecCond y) (h₁ : Hyp52 ↥(h.secSubImg y))
    (hB₁ : h₁.B = h.subB y) (hT₁ : h₁.T = (h.secImage y h.T).subgroupOf (h.secSubImg y))
    (hB' : h'.B = h₁.B.map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))))
    (hT' : h'.T = h₁.T.map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))) :
    Nonempty (↥h'.T ⧸ h'.B.subgroupOf h'.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) := by
  obtain ⟨e1⟩ := nonempty_quotient_T_equiv h₁ h' hB' hT'
  obtain ⟨e2⟩ := hc.nonempty_subT_equiv h₁ hB₁ hT₁
  exact ⟨e1.trans e2⟩

end Invariants

theorem SecCond.exists_hyp59_of_sub (hc : h.SecCond y) (h₁ : Hyp52 ↥(h.secSubImg y))
    (ha₁ : h₁.a = hc.subA) (hJ₁ : h₁.J = h.subJ y) (hB₁ : h₁.B = h.subB y)
    (hK₁ : h₁.K = h.subK y) (hx₁ : h₁.x = hc.subX) (hxP₁ : hc.subX ∈ h₁.P)
    (hQ₁ : h₁.Q = (h.secImage y h.Q).subgroupOf (h.secSubImg y))
    (hT₁ : h₁.T = (h.secImage y h.T).subgroupOf (h.secSubImg y)) :
    ∃ h' : Hyp59 (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y)),
      Nonempty (↥h'.K ⧸ Open.fusionZStar ↥h'.K ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) ∧
      Nonempty (↥h'.J ⧸ Open.fusionZStar ↥h'.J ≃* ↥h.J ⧸ Open.fusionZStar ↥h.J) ∧
      (center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥ →
        Nonempty (↥h'.J ⧸ pPrimeCore 2 ↥h'.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J)) ∧
      (center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥ →
        Nonempty (↥h'.K ⧸ pPrimeCore 2 ↥h'.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K)) ∧
      (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
      (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) ∧
      Nonempty (↥h'.toHyp52.T ⧸ h'.B.subgroupOf h'.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) := by
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
  obtain ⟨hconj, hinner⟩ := hc.conj_K_of_sub h₁ ha₁ hK₁ ha' hK'
  exact ⟨⟨h', pPrimeCore_quotient_pPrimeCore_eq_bot 2, Or.inl (mem_inf.mpr ⟨hxP', hxQ'⟩)⟩,
    hc.fusionZStar_K_of_sub hK'', fusionZStar_J_of_sub hJ'', pPrimeCore_J_of_sub hJ'',
    hc.pPrimeCore_K_of_sub hK'', hconj, hinner, hc.T_of_sub h₁ hB₁ hT₁ hB' hT'⟩

theorem SecCond.exists_isPComponent_centralizer_of_sub (hc : h.SecCond y)
    (h' : Hyp59 (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y))) {G' : Type*} [Group G']
    (e : ↥(generalizedFitting (↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y))) ≃* G') :
    ∃ M : Subgroup X, M ≤ centralizer (h.secB0 y : Set X) ∧
      IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X))) ∧
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* G') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨M, hMC, hM⟩ := exists_isPComponent_centralizer_secB0 (h := h) (y := y)
  refine ⟨M, hMC, hM, ?_⟩
  have hMG : M ≤ h.secG0 y := hMC.trans (h.centralizer_le_G0 y)
  have hML : M ≤ h.secL0 y := by
    have h1 := map_mono (f := (centralizer (h.secB0 y : Set X)).subtype)
      (show M.subgroupOf (centralizer (h.secB0 y : Set X)) ≤ pLayer _ 2 from le_sSup hM)
    rwa [map_subgroupOf_eq_of_le hMC] at h1
  have hMH : h.secImage y M ≤ h.secSubImg y :=
    secImage_mono (hML.trans (h.secL0_le_secSub y))
  have hq : IsQuasisimple (↥M ⧸ pPrimeCore 2 ↥M) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 M _ hMC).mp hM).2.2
  obtain ⟨e₁⟩ := nonempty_secImage_fusionZStar_equiv hMG hMC hq
  have h1 : IsPComponent 2 (M.subgroupOf (h.secG0 y)) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hMC (h.centralizer_le_G0 y)
      (Subgroup.Normal.isSubnormal (Subgroup.normal_subgroupOf_centralizer_normalizer _)) hM
  have h2 := secImage_isPComponent hMG le_rfl hMC h1
  have htop : h.secImage y (h.secG0 y) = ⊤ := by
    show ((h.secG0 y).subgroupOf (h.secG0 y)).map (h.secMk y) = ⊤
    rw [subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  rw [htop] at h2
  have h3 : IsPComponent 2 ((h.secImage y M).subgroupOf (h.secSubImg y)) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hMH le_top h2
  set M' := (h.secImage y M).subgroupOf (h.secSubImg y) with hM'
  have h4 := OddQuot.isPComponent_map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))
    OddQuot.not_two_dvd_card_ker le_top
    (show IsPComponent 2 (M'.subgroupOf ⊤) from B5a.isPComponent_subgroupOf_top_iff.mpr h3)
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
    B5a.isPComponent_subgroupOf_top_iff] at h4
  obtain ⟨e₂⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv
    (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y))) OddQuot.not_two_dvd_card_ker M'
  obtain ⟨e₃⟩ := h'.nonempty_fusionZStar_equiv_of_isPComponent h4 e
  obtain ⟨e₄⟩ := TwoQuot.nonempty_fusionZStar_equiv_of_pPrimeCore_equiv
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hMH))
  exact ⟨e₁.symm.trans (e₄.symm.trans (e₂.trans e₃))⟩

theorem SecCond.sectionData_of_sub (hc : h.SecCond y) (S' : Subgroup ↥(h.secSubImg y))
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
    h.SectionData := by
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
  obtain ⟨h', eK, eJ, hOJ, hOK, hconj, hinner, eT⟩ :=
    hc.exists_hyp59_of_sub (h.subHyp52 hc S' hS'le hS'syl hSS' h7) rfl rfl rfl rfl rfl hxP₁ hQ'
      hT₁
  refine ⟨↥(h.secSubImg y) ⧸ pPrimeCore 2 ↥(h.secSubImg y), inferInstance, inferInstance, h',
    eT, eK, eJ, hOK, hOJ, hconj, hinner, fun ⟨e⟩ => ?_, fun hKP =>
      HSFLit.HS7.kProper_quotient_catalog (HSFLit.HS7.kProper_subgroup_catalog
        (HSFLit.HS7.kProper_quotient_catalog (HSFLit.HS7.kProper_subgroup_catalog hKP _) _) _) _⟩
  obtain ⟨M, hMC, hM, eM⟩ := hc.exists_isPComponent_centralizer_of_sub h' e
  exact ⟨h.secB0 y, M, h.isPGroup_secB0 y, hMC, hM, eM⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
