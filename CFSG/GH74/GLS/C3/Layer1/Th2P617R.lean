module

public import CFSG.GH74.GLS.C3.Layer1.Th2P617F
public import CFSG.GH74.GLS.C3.Layer1.Th2P64I
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransfer

public section

namespace CFSG.GH74.GLS.Th2.Obs

open Equiv Equiv.Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.Th2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T S : Subgroup G}

theorem eight_dvd_card_K_inf_centralizer (hG : C3Hyp G) (hs : Th2Std x y K T S)
    (h7 : Nonempty (kBar K ≃* alternatingGroup (Fin 7))) {u e : G} (huK : u ∈ K) (hu2 : u * u = 1)
    (he : e ∈ CxK x K) (he2 : e * e = 1) (hue : u * e = e * u) :
    8 ∣ Nat.card ↥(K ⊓ centralizer ({u * e} : Set G)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eK⟩ := h7
  have hKN := hs.K_normal_A7 hG ⟨eK⟩
  have hbC : u * e ∈ centralizer ({x} : Set G) :=
    (centralizer ({x} : Set G)).mul_mem (hs.K_le_C huK) he.1
  have hbN : u * e ∈ normalizer (K : Set G) :=
    C3.Layer1.P34.mem_normalizer_of_conj_le (fun a ha => by
      have := hKN (u * e)⁻¹ ((centralizer ({x} : Set G)).inv_mem hbC) a ha
      simpa using this)
  have hb2 : (u * e) * (u * e) = 1 := by
    calc (u * e) * (u * e) = u * (e * u) * e := by group
      _ = u * (u * e) * e := by rw [← hue]
      _ = (u * u) * (e * e) := by group
      _ = 1 := by rw [hu2, he2, one_mul]
  by_cases hb1 : u * e = 1
  · rw [hb1]
    have h8 := Th2.card_sylow_A7 hs.sylow_P ⟨eK⟩
    have hdvd : Nat.card ↥(T ⊓ K) ∣ Nat.card ↥K := Subgroup.card_dvd_of_le inf_le_right
    rw [h8] at hdvd
    have hC : centralizer ({1} : Set G) = ⊤ :=
      Subgroup.centralizer_eq_top_iff_subset.2 (Set.singleton_subset_iff.2 (one_mem _))
    rw [hC, inf_top_eq]
    exact hdvd
  · set b : G := u * e with hb
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    set ū : kBar K := QuotientGroup.mk (⟨u, huK⟩ : ↥K) with hū
    have hρb : barAct K ⟨b, hbN⟩ = MulAut.conj ū := by
      have h1 : (⟨b, hbN⟩ : ↥(normalizer (K : Set G))) =
          ⟨u, Subgroup.le_normalizer huK⟩ * ⟨e, he.2.1⟩ := Subtype.ext rfl
      rw [h1, map_mul, barAct_of_mem huK, (barAct_eq_one_iff ⟨e, he.2.1⟩).2 he.2, mul_one]
    have hmk : ∀ j : ↥K, (QuotientGroup.mk (⟨b * j * b⁻¹, normalizer_conj_mem b hbN j j.2⟩ : ↥K) :
        kBar K) = ū * QuotientGroup.mk j * ū⁻¹ := by
      intro j
      calc (QuotientGroup.mk (⟨b * j * b⁻¹, normalizer_conj_mem b hbN j j.2⟩ : ↥K) : kBar K)
          = barAct K ⟨b, hbN⟩ (QuotientGroup.mk j) := rfl
        _ = (MulAut.conj ū) (QuotientGroup.mk j) := by rw [hρb]
        _ = ū * QuotientGroup.mk j * ū⁻¹ := MulAut.conj_apply _ _
    set σ : Perm (Fin 7) := ((eK ū : alternatingGroup (Fin 7)) : Perm (Fin 7)) with hσ
    let ι : ↥(K ⊓ centralizer ({b} : Set G)) →* Perm (Fin 7) :=
      (a7Act K eK).comp (Subgroup.inclusion
        (fun y hy => Subgroup.le_normalizer hy.1 : K ⊓ centralizer ({b} : Set G) ≤ normalizer (K : Set G)))
    have hrange : ι.range = centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := by
      ext τ
      constructor
      · rintro ⟨⟨y, hyK, hyC⟩, rfl⟩
        have hya : ι ⟨y, hyK, hyC⟩ =
            ((eK (QuotientGroup.mk (⟨y, hyK⟩ : ↥K)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) :=
          a7Act_of_mem eK hyK
        refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
        · rw [hya]
          have hyb : y * b = b * y := mem_centralizer_singleton_iff.1 hyC
          have h1 : (QuotientGroup.mk (⟨b * y * b⁻¹, normalizer_conj_mem b hbN y hyK⟩ : ↥K) :
              kBar K) = QuotientGroup.mk (⟨y, hyK⟩ : ↥K) := by
            congr 1
            apply Subtype.ext
            show b * y * b⁻¹ = y
            calc b * y * b⁻¹ = (b * y) * b⁻¹ := by group
              _ = (y * b) * b⁻¹ := by rw [hyb]
              _ = y := by group
          have h2 := hmk ⟨y, hyK⟩
          rw [h1] at h2
          have h3 : QuotientGroup.mk (⟨y, hyK⟩ : ↥K) * ū = ū * QuotientGroup.mk (⟨y, hyK⟩ : ↥K) := by
            calc QuotientGroup.mk (⟨y, hyK⟩ : ↥K) * ū
                = (ū * QuotientGroup.mk (⟨y, hyK⟩ : ↥K) * ū⁻¹) * ū := by rw [← h2]
              _ = ū * QuotientGroup.mk (⟨y, hyK⟩ : ↥K) := by group
          have h4 := congrArg (fun z : kBar K => ((eK z : alternatingGroup (Fin 7)) : Perm (Fin 7))) h3
          simpa [map_mul, hσ] using h4
        · rw [hya]
          exact (eK _).2
      · rintro ⟨hτC, hτA⟩
        obtain ⟨kb, hkb⟩ := eK.surjective ⟨τ, hτA⟩
        induction kb using QuotientGroup.induction_on with | H j => ?_
        have hτσ : τ * σ = σ * τ := mem_centralizer_singleton_iff.1 hτC
        have hjū : QuotientGroup.mk j * ū = ū * QuotientGroup.mk j := by
          apply eK.injective
          apply Subtype.ext
          rw [map_mul, map_mul, hkb]
          exact hτσ
        have hcl : (QuotientGroup.mk (⟨b * j * b⁻¹, normalizer_conj_mem b hbN j j.2⟩ : ↥K) :
            kBar K) = QuotientGroup.mk j := by
          rw [hmk j]
          calc ū * QuotientGroup.mk j * ū⁻¹ = (ū * QuotientGroup.mk j) * ū⁻¹ := by group
            _ = (QuotientGroup.mk j * ū) * ū⁻¹ := by rw [hjū]
            _ = QuotientGroup.mk j := by group
        have hcO : b⁻¹ * ((j : G) * b * (j : G)⁻¹) ∈ pPrimeCoreOf 2 K := by
          have h1 : (QuotientGroup.mk
              ((⟨b * j * b⁻¹, normalizer_conj_mem b hbN j j.2⟩ : ↥K) * j⁻¹) : kBar K) = 1 := by
            rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcl]
            group
          have h2 : (⟨b * j * b⁻¹, normalizer_conj_mem b hbN j j.2⟩ : ↥K) * j⁻¹ ∈ pPrimeCore 2 ↥K :=
            (QuotientGroup.eq_one_iff _).1 h1
          have h3 : b * (j : G) * b⁻¹ * (j : G)⁻¹ ∈ pPrimeCoreOf 2 K :=
            C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.mul_mem (normalizer_conj_mem b hbN j j.2)
              (K.inv_mem j.2), h2⟩
          have h4 : b⁻¹ * ((j : G) * b * (j : G)⁻¹) = b * (j : G) * b⁻¹ * (j : G)⁻¹ := by
            rw [hbinv]; group
          rw [h4]
          exact h3
        obtain ⟨y, hyK, hyb, hjy⟩ := exists_centralizer_lift hbN hb2 hb1 j.2 hcO
        refine ⟨⟨y, hyK, mem_centralizer_singleton_iff.2 hyb.symm⟩, ?_⟩
        have hya : ι ⟨y, hyK, mem_centralizer_singleton_iff.2 hyb.symm⟩ =
            ((eK (QuotientGroup.mk (⟨y, hyK⟩ : ↥K)) : alternatingGroup (Fin 7)) : Perm (Fin 7)) :=
          a7Act_of_mem eK hyK
        rw [hya]
        have hmkeq : (QuotientGroup.mk (⟨y, hyK⟩ : ↥K) : kBar K) = QuotientGroup.mk j := by
          have h1 : (QuotientGroup.mk ((j : ↥K) * (⟨y, hyK⟩ : ↥K)⁻¹) : kBar K) = 1 :=
            (QuotientGroup.eq_one_iff _).2 (C3.Layer1.Back.Setup91.mem_pPrimeCoreOf_iff.1 hjy).2
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
          exact (mul_inv_eq_one.1 h1).symm
        rw [hmkeq, hkb]
    have hdvd1 := Subgroup.card_range_dvd ι
    rw [hrange] at hdvd1
    refine dvd_trans ?_ hdvd1
    by_cases hσ1 : σ = 1
    · have hC : centralizer ({σ} : Set (Perm (Fin 7))) = ⊤ := by
        rw [hσ1]
        exact Subgroup.centralizer_eq_top_iff_subset.2 (Set.singleton_subset_iff.2 (one_mem _))
      rw [hC, top_inf_eq, card_alt7]
      norm_num
    · have hσ2 : σ * σ = 1 := by
        have h1 : ū * ū = 1 := by
          rw [hū, ← QuotientGroup.mk_mul]
          have : (⟨u, huK⟩ * ⟨u, huK⟩ : ↥K) = 1 := Subtype.ext hu2
          rw [this]
          exact QuotientGroup.mk_one _
        have h2 : (eK ū) * (eK ū) = 1 := by rw [← map_mul, h1, map_one]
        have h3 := congrArg Subtype.val h2
        simpa [hσ] using h3
      exact eight_dvd_card_centralizer_alt hσ2 hσ1

end CFSG.GH74.GLS.Th2.Obs
