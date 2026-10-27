module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3CaseA
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3Out
public import CFSG.LocalAnalysis.GLTheoremA.PartI.KDSU3

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag Matrix

variable {n : ℕ} {K : Type} [Field K]

theorem card_le_three_of_normalizes (h : UnitaryFieldData 2 n K) (hodd : n % 2 = 1) (h1 : 1 < n)
    (h3 : n % 3 ≠ 0) (E T : Subgroup (MulAut (pI h))) (hE : IsPGroup 3 E) (hT : IsPGroup 2 T)
    (hT0 : T ≠ ⊥) (hnorm : E ≤ Subgroup.normalizer (T : Set (MulAut (pI h)))) :
    Nat.card E ≤ 3 := by
  classical
  by_cases hTD : T ⊓ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = ⊥
  ·
    have : Finite K := h.finite
    have hq := hq_aux h1
    have hED := le_primeFormD_of_isPGroup_three h h1 h3 E hE
    haveI : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).2 hT0
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hdvd : 2 ∣ Nat.card T := by
      obtain ⟨m, hm⟩ := hT.exists_card_eq
      have h1lt : 1 < Nat.card T := Finite.one_lt_card
      rw [hm] at h1lt ⊢
      have : m ≠ 0 := by
        rintro rfl
        simp at h1lt
      exact dvd_pow_self 2 this
    obtain ⟨τ', hτ'⟩ := exists_prime_orderOf_dvd_card' (G := T) 2 hdvd
    set τ : MulAut (pI h) := (τ' : MulAut (pI h)) with hτdef
    have hτT : τ ∈ T := τ'.2
    have hτord : orderOf τ = 2 := by
      rw [hτdef, Subgroup.orderOf_coe]
      exact hτ'
    have hτD : τ ∉ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      intro hD
      have : τ ∈ T ⊓ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨hτT, hD⟩
      rw [hTD, Subgroup.mem_bot] at this
      rw [this, orderOf_one] at hτord
      omega
    have hcommE : ∀ e ∈ E, e * τ = τ * e := by
      intro e he
      have hker : (primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq).ker =
          primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
        ker_primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq
      have heT : e * τ * e⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 (hnorm he) τ).1 hτT
      have hxT : (e * τ * e⁻¹)⁻¹ * τ ∈ T := T.mul_mem (T.inv_mem heT) hτT
      have hx : (e * τ * e⁻¹)⁻¹ * τ ∈ T ⊓ primeFormD h
          ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        refine Subgroup.mem_inf.2 ⟨hxT, ?_⟩
        rw [← hker, MonoidHom.mem_ker]
        have hee : primeFormFieldFactor h isPrimeFormGram_one (by norm_num) hq e = 1 := by
          have := hED he
          rw [← hker, MonoidHom.mem_ker] at this
          exact this
        simp only [map_mul, map_inv, hee, one_mul, inv_one, mul_one, inv_mul_cancel]
      rw [hTD, Subgroup.mem_bot] at hx
      have : e * τ * e⁻¹ = τ := by
        have := inv_mul_eq_one.mp hx
        exact this
      calc e * τ = (e * τ * e⁻¹) * e := by group
        _ = τ * e := by rw [this]
    have hτout : τ ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner (pI h) := by
      intro hin
      rw [CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.mem_inner_primeFormP] at hin
      obtain ⟨s, hs⟩ := hin
      exact hτD ⟨_, hs.symm⟩
    have hmodel : CFSG.Open.StatedClassicalModel (pI h) CFSG.Open.StatedLieTag.PSU 3 2 n := by
      refine ⟨⟨Nat.prime_two, by omega, by norm_num, ?_⟩, K, inferInstance, h.finite, ?_, ?_⟩
      · intro hc
        exact hq_aux h1 ⟨rfl, (Prod.mk.inj hc).2⟩
      · rw [h.card, ← pow_mul, mul_comm]
      · exact ⟨(CFSG.LocalAnalysis.unitaryPSUEquivPrimeFormOne h 3).symm.trans
          (unitaryPSUEquiv h (by norm_num))⟩
    obtain ⟨K', _, _, h', ζ, hζ⟩ :=
      CFSG.LocalAnalysis.even_unitary_three_outer_involution_bar_conjugate
        (by omega) hmodel τ hτord hτout
    set cζ := MulAut.congr ζ.symm with hcζ
    have hfb : cζ τ = primeFormFieldAut h' isPrimeFormGram_one
        (CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.fieldDataHermitianForm h').conj := by
      ext x
      simp only [hcζ, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_symm]
      rw [hζ x]
      simp
    have hinj : Function.Injective cζ := cζ.injective
    have hE' : IsPGroup 3 (E.map cζ.toMonoidHom) := hE.map cζ.toMonoidHom
    have hcomm' : ∀ e' ∈ E.map cζ.toMonoidHom,
        e' * primeFormFieldAut h' isPrimeFormGram_one
          (CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.fieldDataHermitianForm h').conj =
        primeFormFieldAut h' isPrimeFormGram_one
          (CFSG.ShultStronglyClosedTI.UnitaryRootAutomorphism.fieldDataHermitianForm h').conj *
            e' := by
      rintro _ ⟨e, he, rfl⟩
      rw [← hfb]
      change cζ e * cζ τ = cζ τ * cζ e
      rw [← map_mul, ← map_mul, hcommE e he]
    have := caseB_core h' hodd h1 h3 _ hE' hcomm'
    rwa [Subgroup.card_map_of_injective hinj] at this
  · exact caseA_core h hodd h1 h3 E T hE hT hTD hnorm



theorem isPGroup_of_isElemAbelian' {p : ℕ} {G : Type*} [Group G] {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) : IsPGroup p E := fun g => ⟨1, by
  rw [pow_one]
  exact Subtype.ext (by simpa using hE.2 g g.2)⟩

theorem kdSU3_holds : KDSU3 := by
  intro L _ _ hL E T hE hT0 hT2 hnorm
  obtain ⟨K, _, _, n, hodd, h1, h3, hcard, ⟨e⟩⟩ := hL
  have h : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, by omega, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨Φ, hΦ⟩ := exists_autHom_injective h hodd h1 e
  have hE3 : IsPGroup 3 (E.map Φ) :=
    (isPGroup_of_isElemAbelian' hE).map Φ
  have hT2' : IsPGroup 2 (T.map Φ) := hT2.map Φ
  have hT0' : T.map Φ ≠ ⊥ := by
    intro hbot
    apply hT0
    rwa [Subgroup.map_eq_bot_iff_of_injective T hΦ] at hbot
  have hnorm' : E.map Φ ≤ Subgroup.normalizer ((T.map Φ : Subgroup (MulAut (pI h))) :
      Set (MulAut (pI h))) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨x * z * x⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.1 (hnorm hx) z).1 hz
    · rintro ⟨z, hz, hzy⟩
      have hxinv : x⁻¹ ∈ Subgroup.normalizer (T : Set (MulAut L)) := inv_mem (hnorm hx)
      have hmem : x⁻¹ * z * x ∈ T := by
        simpa using (Subgroup.mem_normalizer_iff.1 hxinv z).1 hz
      refine ⟨x⁻¹ * z * x, hmem, ?_⟩
      rw [map_mul, map_mul, map_inv, hzy]
      group
  have := card_le_three_of_normalizes h hodd h1 h3 (E.map Φ) (T.map Φ) hE3 hT2' hT0' hnorm'
  rwa [Subgroup.card_map_of_injective hΦ] at this


end CFSG.LocalAnalysis.GLTheoremA
