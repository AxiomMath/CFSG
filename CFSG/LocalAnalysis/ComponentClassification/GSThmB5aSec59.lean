module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecHyp
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalKProper

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.LocalCores CFSG.ComponentClassification.UnbalancedLayer
open scoped commutatorElement

namespace Hyp52

section OddQuotient

variable {H : Type} [Group H] [Finite H]

local notation "π" => QuotientGroup.mk' (pPrimeCore 2 H)

theorem quotient_PQT (h : Hyp52 H) (h' : Hyp52 (H ⧸ pPrimeCore 2 H)) (hJ : h'.J = h.J.map π)
    (hS : h'.S = h.S.map π) (hB : h'.B = h.B.map π) :
    h'.P = h.P.map π ∧ h'.Q = h.Q.map π ∧ h'.T = h.T.map π := by
  have hS2 := B5a.isPGroup_S h
  have hBS : h.B ≤ h.S := h.B_le.trans inf_le_left
  have hP : h'.P = h.P.map π := by
    show h'.S ⊓ coreActionKernel h'.J = (h.S ⊓ coreActionKernel h.J).map π
    rw [hS, hJ, OddQuot.map_inf_coreActionKernel (h.S_le.trans inf_le_right)]
  have hQ : h'.Q = h.Q.map π := by
    show h'.S ⊓ normalizer (h'.B : Set (H ⧸ pPrimeCore 2 H)) =
      (h.S ⊓ normalizer (h.B : Set H)).map π
    rw [hS, hB, OddQuot.map_inf_normalizer hS2 hBS]
  refine ⟨hP, hQ, ?_⟩
  show h'.Q ⊓ h'.P = (h.Q ⊓ h.P).map π
  rw [hP, hQ, OddQuot.map_inf_of_le hS2 inf_le_left inf_le_left]

theorem map_conjugate_K_eq_iff (h : Hyp52 H) :
    conjugate (h.K.map π) (π h.a) = h.K.map π ↔ conjugate h.K h.a = h.K := by
  have hO := OddQuot.not_two_dvd_card_ker (H := H)
  rw [← map_conjugate]
  constructor
  · intro heq
    obtain ⟨haX, hac⟩ := OddQuot.isPComponent_conjugate_subgroupOf h.a_mem_normalizer
      h.isPComponent_K.1 h.isPComponent_K.2
    exact OddQuot.eq_of_map_eq π hO haX h.isPComponent_K.1 hac h.isPComponent_K.2 heq
  · intro heq
    rw [heq]

theorem map_mem_sup_coreActionKernel_iff (h : Hyp52 H) :
    π h.a ∈ h.K.map π ⊔ coreActionKernel (h.K.map π) ↔ h.a ∈ h.K ⊔ coreActionKernel h.K := by
  have hO := OddQuot.not_two_dvd_card_ker (H := H)
  have hmap := OddQuot.map_inf_coreActionKernel (le_refl (normalizer (h.K : Set H)))
  have hKW := h.isPComponent_K.1
  constructor
  · intro ha
    obtain ⟨k', hk', c', hc', hkc⟩ := B5a.exists_mul_of_mem_sup_coreActionKernel ha
    obtain ⟨k, hk, rfl⟩ := mem_map.mp hk'
    have hcc : π (k⁻¹ * h.a) = c' := by
      rw [map_mul, map_inv, eq_inv_mul_of_mul_eq hkc]
    have hcW : k⁻¹ * h.a ∈ normalizer (h.B : Set H) :=
      mul_mem (inv_mem (hKW hk)) h.a_mem_normalizer
    have hcN : k⁻¹ * h.a ∈ normalizer (h.K : Set H) := by
      obtain ⟨hcX, hcc'⟩ := OddQuot.isPComponent_conjugate_subgroupOf hcW hKW h.isPComponent_K.2
      have heq : conjugate h.K (k⁻¹ * h.a) = h.K :=
        OddQuot.eq_of_map_eq π hO hcX hKW hcc' h.isPComponent_K.2 (by
          rw [map_conjugate, hcc]
          exact conjugate_eq_of_mem_normalizer (mem_coreActionKernel.mp hc').1)
      exact mem_normalizer_of_conjugate_eq heq
    have h1 : π (k⁻¹ * h.a) ∈ (normalizer (h.K : Set H) ⊓ coreActionKernel h.K).map π := by
      rw [hmap, hcc]
      exact mem_inf.mpr ⟨hcc ▸ mem_map_of_mem π hcN, hc'⟩
    obtain ⟨d, hd, hdc⟩ := mem_map.mp h1
    have ho : d⁻¹ * (k⁻¹ * h.a) ∈ pPrimeCore 2 H := by
      rw [← QuotientGroup.ker_mk' (pPrimeCore 2 H), MonoidHom.mem_ker, map_mul, map_inv, hdc,
        inv_mul_cancel]
    have hoN : d⁻¹ * (k⁻¹ * h.a) ∈ normalizer (h.K : Set H) :=
      mul_mem (inv_mem (mem_inf.mp hd).1) hcN
    have hoK : d⁻¹ * (k⁻¹ * h.a) ∈ coreActionKernel h.K := by
      refine mem_coreActionKernel.mpr ⟨hoN, fun t ht => ?_⟩
      apply OddQuot.inf_pPrimeCore_le_oddCoreIn h.K
      set o := d⁻¹ * (k⁻¹ * h.a) with hodef
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h2 := (mem_normalizer_iff.mp (inv_mem hoN) t).mp ht
        rw [inv_inv] at h2
        rw [show t⁻¹ * o⁻¹ * t * o = t⁻¹ * (o⁻¹ * t * o) by group]
        exact mul_mem (inv_mem ht) h2
      · have h2 : t⁻¹ * o⁻¹ * t⁻¹⁻¹ ∈ pPrimeCore 2 H :=
          (inferInstance : (pPrimeCore 2 H).Normal).conj_mem _ (inv_mem ho) t⁻¹
        rw [inv_inv] at h2
        exact mul_mem h2 ho
    have hcK : k⁻¹ * h.a ∈ coreActionKernel h.K := by
      rw [show k⁻¹ * h.a = d * (d⁻¹ * (k⁻¹ * h.a)) by group]
      exact mul_mem (mem_inf.mp hd).2 hoK
    rw [show h.a = k * (k⁻¹ * h.a) by group]
    exact mul_mem (mem_sup_left hk) (mem_sup_right hcK)
  · intro ha
    obtain ⟨k, hk, c, hcK, hkc⟩ := B5a.exists_mul_of_mem_sup_coreActionKernel ha
    rw [← hkc, map_mul]
    refine mul_mem (mem_sup_left (mem_map_of_mem π hk)) (mem_sup_right ?_)
    have h1 : π c ∈ (normalizer (h.K : Set H) ⊓ coreActionKernel h.K).map π :=
      mem_map_of_mem π (mem_inf.mpr ⟨(mem_coreActionKernel.mp hcK).1, hcK⟩)
    rw [hmap] at h1
    exact (mem_inf.mp h1).2

theorem nonempty_quotient_T_equiv (h : Hyp52 H) (h' : Hyp52 (H ⧸ pPrimeCore 2 H))
    (hB : h'.B = h.B.map π) (hT : h'.T = h.T.map π) :
    Nonempty (↥h'.T ⧸ h'.B.subgroupOf h'.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) := by
  have hS2 := B5a.isPGroup_S h
  have hTS : h.T ≤ h.S := inf_le_left.trans inf_le_left
  have hmem : ∀ t : ↥h.T, π t ∈ h'.T := fun t => by
    rw [hT]
    exact mem_map_of_mem π t.2
  let f : ↥h.T →* ↥h'.T :=
    ((QuotientGroup.mk' (pPrimeCore 2 H)).comp h.T.subtype).codRestrict _ hmem
  refine B5a.nonempty_quotient_equiv_of_surjective f ?_ fun t => ?_
  · rintro ⟨z, hz⟩
    rw [hT] at hz
    obtain ⟨t, ht, rfl⟩ := mem_map.mp hz
    exact ⟨⟨t, ht⟩, rfl⟩
  · show π t ∈ h'.B ↔ _
    rw [hB]
    constructor
    · intro hb
      obtain ⟨b, hb, hbt⟩ := mem_map.mp hb
      have heq : b = t :=
        OddQuot.injOn_of_isPGroup hS2 (h.B_le.trans inf_le_left hb) (hTS t.2) hbt
      rw [← heq]
      exact hb
    · exact fun ht => mem_map_of_mem π ht

theorem exists_hyp59_of_normal (h : Hyp52 H) (hBP : h.P ≤ normalizer (h.B : Set H))
    (hx2 : h.x ^ 2 = 1) :
    ∃ h' : Hyp59 (H ⧸ pPrimeCore 2 H),
      h'.a = π h.a ∧ h'.J = h.J.map π ∧ h'.S = h.S.map π ∧ h'.B = h.B.map π ∧
      h'.K = h.K.map π ∧ h'.x = π h.x ∧
      Nonempty (↥h'.toHyp52.T ⧸ h'.B.subgroupOf h'.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) ∧
      Nonempty (↥h'.K ⧸ Open.fusionZStar ↥h'.K ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) ∧
      Nonempty (↥h'.J ⧸ Open.fusionZStar ↥h'.J ≃* ↥h.J ⧸ Open.fusionZStar ↥h.J) ∧
      Nonempty (↥h'.K ⧸ pPrimeCore 2 ↥h'.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K) ∧
      Nonempty (↥h'.J ⧸ pPrimeCore 2 ↥h'.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J) ∧
      (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
      (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO := OddQuot.not_two_dvd_card_ker (H := H)
  obtain ⟨h', ha', hJ', hS', hB', hK', hx'⟩ := h.quotient_oddCore
  obtain ⟨hP', hQ', hT'⟩ := quotient_PQT h h' hJ' hS' hB'
  refine ⟨⟨h', pPrimeCore_quotient_pPrimeCore_eq_bot 2, Or.inr ⟨?_, ?_⟩⟩, ?_⟩
  · rw [hP', hQ']
    exact map_mono (le_inf inf_le_left hBP)
  · rw [hx', ← map_pow, hx2, map_one]
  dsimp only
  obtain ⟨eK⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv π hO h.K
  obtain ⟨eJ⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv π hO h.J
  obtain ⟨eK'⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hO h.K
  obtain ⟨eJ'⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv π hO h.J
  refine ⟨ha', hJ', hS', hB', hK', hx', nonempty_quotient_T_equiv h h' hB' hT', ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [hK']
    exact ⟨eK.symm⟩
  · rw [hJ']
    exact ⟨eJ.symm⟩
  · rw [hK']
    exact ⟨eK'.symm⟩
  · rw [hJ']
    exact ⟨eJ'.symm⟩
  · rw [hK', ha']
    exact map_conjugate_K_eq_iff h
  · rw [hK', ha']
    exact map_mem_sup_coreActionKernel_iff h

end OddQuotient

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

theorem map_secImage (Y : Subgroup X) :
    (h.secImage y Y).map (QuotientGroup.mk' (pPrimeCore 2 (h.secBar y))) =
      (Y.subgroupOf (h.secG0 y)).map (h.secQ y) :=
  Subgroup.map_map _ _ _

theorem exists_hyp59_section (hyP : y ∈ h.P) (hyT : y ∉ h.T) (hy2 : y ^ 2 ∈ h.T)
    (hQ : h.Q ≤ h.secG0 y) (hyQ : y ∈ normalizer (h.Q : Set X)) (hSyl : h.SecSylow y) :
    ∃ h' : Hyp59 (h.secQuot y),
      h'.a = h.secQ y ⟨h.a, a_mem_secG0 hQ⟩ ∧ h'.x = h.secQ y ⟨y, mem_secG0_of_sq_mem hy2⟩ ∧
      h'.J = ((GSLit.fixedLayer h.J (h.secB0 y)).subgroupOf (h.secG0 y)).map (h.secQ y) ∧
      h'.S = (h.S.subgroupOf (h.secG0 y)).map (h.secQ y) ∧
      h'.B = (h.B.subgroupOf (h.secG0 y)).map (h.secQ y) ∧
      h'.K = (h.K.subgroupOf (h.secG0 y)).map (h.secQ y) ∧
      Nonempty (↥h'.K ⧸ Open.fusionZStar ↥h'.K ≃* ↥h.K ⧸ Open.fusionZStar ↥h.K) ∧
      Nonempty (↥h'.J ⧸ Open.fusionZStar ↥h'.J ≃* ↥h.J ⧸ Open.fusionZStar ↥h.J) ∧
      (center (↥h.J ⧸ pPrimeCore 2 ↥h.J) = ⊥ →
        Nonempty (↥h'.J ⧸ pPrimeCore 2 ↥h'.J ≃* ↥h.J ⧸ pPrimeCore 2 ↥h.J)) ∧
      (center (↥h.K ⧸ pPrimeCore 2 ↥h.K) = ⊥ →
        Nonempty (↥h'.K ⧸ pPrimeCore 2 ↥h'.K ≃* ↥h.K ⧸ pPrimeCore 2 ↥h.K)) ∧
      (conjugate h'.K h'.a = h'.K ↔ conjugate h.K h.a = h.K) ∧
      (h'.a ∈ h'.K ⊔ coreActionKernel h'.K ↔ h.a ∈ h.K ⊔ coreActionKernel h.K) ∧
      Nat.card h'.B * Nat.card (h.secB0 y) = Nat.card h.B ∧
      Nonempty (↥h'.toHyp52.T ⧸ h'.B.subgroupOf h'.toHyp52.T ≃* ↥h.T ⧸ h.B.subgroupOf h.T) ∧
      Nonempty (↥h'.toHyp52.P ≃* ↥(h.S ⊓ h.secG0 y ⊓ h.P) ⧸
        (h.secB0 y).subgroupOf (h.S ⊓ h.secG0 y ⊓ h.P)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : h.SecCond y := ⟨hyP, hyT, hy2, hQ, hyQ⟩
  have hO := OddQuot.not_two_dvd_card_ker (H := h.secBar y)
  have hyG : y ∈ h.secG0 y := hc.y_mem_G0
  have hS1 : IsPGroup 2 (h.secHyp52 hc hSyl).S := B5a.isPGroup_S _
  obtain ⟨h', ha', hJ', hS', hB', hK', hx'⟩ := (h.secHyp52 hc hSyl).quotient_oddCore
  obtain ⟨hP', hQ', hT'⟩ := quotient_PQT (h.secHyp52 hc hSyl) h' hJ' hS' hB'
  have hx1P : (h.secHyp52 hc hSyl).x ∈ (h.secHyp52 hc hSyl).P := by
    rw [secHyp52_P]
    exact mem_map_of_mem _ (show (⟨y, hyG⟩ : ↥(h.secG0 y)) ∈ h.P.subgroupOf (h.secG0 y) from hyP)
  have hx1Q : (h.secHyp52 hc hSyl).x ∈
      normalizer ((h.secHyp52 hc hSyl).Q : Set (h.secBar y)) := by
    rw [secHyp52_Q]
    exact secMk_mem_normalizer hyG hyQ
  refine ⟨⟨h', pPrimeCore_quotient_pPrimeCore_eq_bot 2, Or.inl (mem_inf.mpr ⟨?_, ?_⟩)⟩, ?_⟩
  · rw [hP', hx']
    exact mem_map_of_mem _ hx1P
  · rw [hQ', hx']
    exact le_normalizer_map _ (mem_map_of_mem _ hx1Q)
  dsimp only
  refine ⟨by rw [ha']; rfl, by rw [hx']; rfl, by rw [hJ', secHyp52_J, map_secImage],
    by rw [hS', secHyp52_S, map_secImage], by rw [hB', secHyp52_B, map_secImage],
    by rw [hK', secHyp52_K, map_secImage], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK']
    obtain ⟨e1⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv _ hO (h.secHyp52 hc hSyl).K
    obtain ⟨e2⟩ := nonempty_secK_fusionZStar_equiv (h := h) (y := y)
    exact ⟨e1.symm.trans e2⟩
  · rw [hJ']
    obtain ⟨e1⟩ := OddQuot.nonempty_quotient_fusionZStar_equiv _ hO (h.secHyp52 hc hSyl).J
    obtain ⟨e2⟩ := nonempty_secJ_fusionZStar_equiv (h := h) (y := y)
    exact ⟨e1.symm.trans e2⟩
  · intro hZ
    rw [hJ']
    obtain ⟨e1⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv _ hO (h.secHyp52 hc hSyl).J
    obtain ⟨e2⟩ := nonempty_secJ_pPrimeCore_equiv (y := y) hZ
    exact ⟨e1.symm.trans e2⟩
  · intro hZ
    rw [hK']
    obtain ⟨e1⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv _ hO (h.secHyp52 hc hSyl).K
    obtain ⟨e2⟩ := nonempty_secK_pPrimeCore_equiv (y := y) hZ
    exact ⟨e1.symm.trans e2⟩
  · rw [hK', ha']
    exact (map_conjugate_K_eq_iff _).trans (conjugate_secK_eq_iff hc)
  · rw [hK', ha']
    exact (map_mem_sup_coreActionKernel_iff _).trans hc.secA_mem_sup_iff
  · rw [hB', OddQuot.card_map_of_isPGroup (B5a.isPGroup_B _)]
    exact card_secImage (h.secB0_le_B y) hc.B_le_G0
  ·
    have hT1 : h'.T = (h.T.subgroupOf (h.secG0 y)).map (h.secQ y) := by
      rw [hT', secHyp52_T, map_secImage]
    have hTG : h.T ≤ h.secG0 y := hc.T_le_G0
    have hmem : ∀ t : ↥h.T, h.secQ y (inclusion hTG t) ∈ h'.T := fun t => by
      rw [hT1]
      exact mem_map_of_mem _ (show inclusion hTG t ∈ h.T.subgroupOf (h.secG0 y) from t.2)
    let f : ↥h.T →* ↥h'.T := ((h.secQ y).comp (inclusion hTG)).codRestrict _ hmem
    refine B5a.nonempty_quotient_equiv_of_surjective f ?_ fun t => ?_
    · rintro ⟨z, hz⟩
      rw [hT1] at hz
      obtain ⟨t, ht, rfl⟩ := mem_map.mp hz
      exact ⟨⟨t, ht⟩, rfl⟩
    · have htG : (t : X) ∈ h.secG0 y := hTG t.2
      show h.secQ y ⟨t, htG⟩ ∈ h'.B ↔ _
      rw [hB', secHyp52_B]
      constructor
      · intro hb
        obtain ⟨b, hb, hbt⟩ := mem_map.mp hb
        have hbS : b ∈ h.secImage y h.S := secImage_mono (h.B_le.trans inf_le_left) hb
        have htS : h.secMk y ⟨t, htG⟩ ∈ h.secImage y h.S := mem_map_of_mem _
          (show (⟨t, htG⟩ : ↥(h.secG0 y)) ∈ h.S.subgroupOf (h.secG0 y) from
            (mem_inf.mp (mem_inf.mp t.2).1).1)
        have heq : b = h.secMk y ⟨t, htG⟩ := OddQuot.injOn_of_isPGroup hS1 hbS htS hbt
        rw [heq] at hb
        exact (secMk_mem_secImage_iff (h.secB0_le_B y) _).mp hb
      · intro htB
        exact mem_map_of_mem _ (mem_map_of_mem _
          (show (⟨t, htG⟩ : ↥(h.secG0 y)) ∈ h.B.subgroupOf (h.secG0 y) from htB))
  ·
    have hP1 : h'.P = (h.P.subgroupOf (h.secG0 y)).map (h.secQ y) := by
      rw [hP', secHyp52_P, map_secImage]
    have hPG : h.S ⊓ h.secG0 y ⊓ h.P ≤ h.secG0 y := inf_le_left.trans inf_le_right
    have hmem : ∀ p : ↥(h.S ⊓ h.secG0 y ⊓ h.P), h.secQ y (inclusion hPG p) ∈ h'.P := fun p => by
      rw [hP1]
      exact mem_map_of_mem _
        (show inclusion hPG p ∈ h.P.subgroupOf (h.secG0 y) from (mem_inf.mp p.2).2)
    let f : ↥(h.S ⊓ h.secG0 y ⊓ h.P) →* ↥h'.P :=
      ((h.secQ y).comp (inclusion hPG)).codRestrict _ hmem
    have hf : Function.Surjective f := by
      rintro ⟨z, hz⟩
      rw [hP1] at hz
      obtain ⟨p, hp, rfl⟩ := mem_map.mp hz
      have hpP : (p : X) ∈ h.P := hp
      exact ⟨⟨p, mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp hpP).1, p.2⟩, hpP⟩⟩, rfl⟩
    have hker : f.ker = (h.secB0 y).subgroupOf (h.S ⊓ h.secG0 y ⊓ h.P) := by
      ext p
      have hpG : (p : X) ∈ h.secG0 y := hPG p.2
      have hpS : h.secMk y ⟨p, hpG⟩ ∈ h.secImage y h.S := mem_map_of_mem _
        (show (⟨p, hpG⟩ : ↥(h.secG0 y)) ∈ h.S.subgroupOf (h.secG0 y) from
          (mem_inf.mp (mem_inf.mp p.2).1).1)
      rw [MonoidHom.mem_ker, mem_subgroupOf]
      constructor
      · intro hp1
        have h1 : ((f p : ↥h'.P) : h.secQuot y) = 1 := congrArg Subtype.val hp1
        have h2 : h.secMk y ⟨p, hpG⟩ = 1 :=
          OddQuot.injOn_of_isPGroup hS1 hpS (one_mem _) (by rw [map_one]; exact h1)
        have h3 : (⟨p, hpG⟩ : ↥(h.secG0 y)) ∈ (h.secMk y).ker := h2
        rw [ker_secMk] at h3
        exact h3
      · intro hp1
        have h3 : (⟨p, hpG⟩ : ↥(h.secG0 y)) ∈ (h.secMk y).ker := by
          rw [ker_secMk]
          exact hp1
        apply Subtype.ext
        show (QuotientGroup.mk' (pPrimeCore 2 (h.secBar y))) (h.secMk y ⟨p, hpG⟩) = 1
        rw [MonoidHom.mem_ker.mp h3, map_one]
    exact ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
