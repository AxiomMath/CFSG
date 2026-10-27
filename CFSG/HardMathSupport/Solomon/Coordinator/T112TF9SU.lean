module

public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9SUAlg
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9SUCount
public import CFSG.HardMathSupport.Solomon.Coordinator.T112TF9SULift
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.Tables112
public import CFSG.RankThree.PartTwo.KFacts.AutPSU

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.ComponentClassification.OuterAutomorphisms

theorem exists_unitaryFieldData_SU {F : Type} [Field F] [Finite F] {q : ℕ} (hq2 : 2 < q)
    (hF : Nat.card F = q ^ 2) :
    ∃ ℓ f : ℕ, UnitaryFieldData ℓ f F ∧ q = ℓ ^ f := by
  have := Fintype.ofFinite F
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card F (ringChar F)
  have hdvd : q ∣ ringChar F ^ (n : ℕ) := by
    rw [← hn, ← Nat.card_eq_fintype_card, hF]
    exact dvd_pow_self q two_ne_zero
  obtain ⟨f, -, hqf⟩ := (Nat.dvd_prime_pow hℓ).1 hdvd
  have hf1 : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [h0, pow_zero] at hqf; omega
    · exact h0
  exact ⟨ringChar F, f, ⟨hℓ, hf1, by rw [hF, hqf, ← pow_mul, mul_comm]⟩, hqf⟩

section Transport

variable {ℓ f : ℕ} {F : Type} [Field F] (h : UnitaryFieldData ℓ f F) {K : Type} [Group K]

@[expose] def psuEquivU3T :
    unitaryPSU h 3 ≃* U3T h :=
  QuotientGroup.congr _ _ (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)) (by
    ext z
    constructor
    · rintro ⟨y, ⟨c, hcN, hcn, hy⟩, rfl⟩
      exact ⟨c, hcN, hcn, hy⟩
    · rintro ⟨c, hcN, hcn, hz⟩
      exact ⟨(MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3)).symm z, ⟨c, hcN, hcn, hz⟩,
        MulEquiv.apply_symm_apply _ _⟩)

@[expose] noncomputable def quotEquivU3T (hq2 : 2 < ℓ ^ f) (eK : K ≃* ↥(unitarySU ℓ f F 3)) :
    (K ⧸ Subgroup.center K) ≃* U3T h :=
  ((QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.RankThree.PartTwo.KFacts.center_unitarySU_three (h := h) hq2))).trans
    (psuEquivU3T h)

@[expose] def toGramSU (eK : K ≃* ↥(unitarySU ℓ f F 3)) :
    K ≃* ↥(gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :=
  eK.trans (MulEquiv.subgroupCongr (unitarySU_eq_gramSU h 3))

theorem quotEquivU3T_mk (hq2 : 2 < ℓ ^ f) (eK : K ≃* ↥(unitarySU ℓ f F 3)) (x : K) :
    quotEquivU3T h hq2 eK (QuotientGroup.mk x) = QuotientGroup.mk (toGramSU h eK x) := rfl

theorem fieldFactor_eq_one_of_inner [Finite F] (hq3 : ¬(3 = 3 ∧ ℓ ^ f = 2)) (α : MulAut (U3T h))
    (hα : α ∈ inner (U3T h)) :
    primeFormFieldFactor h (isPrimeFormGram_one (n := 3)) (le_refl 3) hq3 α = 1 := by
  obtain ⟨s, hs⟩ := (mem_inner_primeFormP h _ α).1 hα
  rw [hs]
  have := primeFormFieldFactor_apply h (isPrimeFormGram_one (n := 3)) (le_refl 3) hq3
    ⟨s, s.2.1⟩ 1
  rwa [map_one, mul_one] at this

theorem exists_fieldType_SU_aux [Finite F] [Finite K] (hq2 : 2 < ℓ ^ f)
    (hpF : 3 ∣ Nat.card Fˣ) (hF : Nat.card F = (ℓ ^ f) ^ 2) (hU : UnitaryH90 F (ℓ ^ f))
    (hqs : CFSG.Open.IsQuasisimple K) (eK : K ≃* ↥(unitarySU ℓ f F 3))
    (H : Subgroup (MulAut K)) (hH : CFSG.Open.IsElemAbelian 3 H) (h27 : Nat.card H = 27) :
    ∃ ψ ∈ H, ¬ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsInnerAut ψ ∧
      ∃ (M : U3U h) (σ : F ≃+* F), ∀ x : K,
        ((toGramSU h eK (ψ x) : gramSU h _) : GL (Fin 3) F) =
          (M : GL (Fin 3) F) * GeneralLinearGroup.map (σ : F →+* F)
            ((M : GL (Fin 3) F)⁻¹ * ((toGramSU h eK x : gramSU h _) : GL (Fin 3) F) *
              (M : GL (Fin 3) F)) * (M : GL (Fin 3) F)⁻¹ := by
  have hq3 : ¬(3 = 3 ∧ ℓ ^ f = 2) := by
    rintro ⟨-, h2⟩
    omega
  have : Group.IsPerfect K := ⟨hqs.1⟩
  let ee := quotEquivU3T h hq2 eK
  let Φ : MulAut K →* MulAut (U3T h) :=
    (MulAut.congr ee).toMonoidHom.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom K)
  have hΦinj : Function.Injective Φ :=
    (MulAut.congr ee).injective.comp
      (CFSG.ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective K)
  have hΦ : ∀ ψ x, Φ ψ (ee (QuotientGroup.mk x)) = ee (QuotientGroup.mk (ψ x)) := by
    intro ψ x
    change ee (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient ψ
      (ee.symm (ee (QuotientGroup.mk x)))) = _
    rw [MulEquiv.symm_apply_apply]
    exact congrArg ee
      (CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk ψ x)
  have hH' : CFSG.Open.IsElemAbelian 3 (H.map Φ) := CFSG.SectionRank.isElemAbelian_map hH Φ
  have hcard : Nat.card (H.map Φ) = 27 := by
    rw [Subgroup.card_map_of_injective hΦinj, h27]
  obtain ⟨α, hαH, hαne⟩ := exists_fieldFactor_ne_one h hq3 hpF (H.map Φ) hH' hcard
  obtain ⟨ψ, hψH, rfl⟩ := Subgroup.mem_map.1 hαH
  have hα3 : Φ ψ ^ 3 = 1 := by rw [← map_pow, hH.2 ψ hψH, map_one]
  obtain ⟨M, hM⟩ := exists_conj_realization h hF hU hq3 (Φ ψ) hα3 hαne
  refine ⟨ψ, hψH, ?_, M,
    primeFormFieldFactor h (isPrimeFormGram_one (n := 3)) (le_refl 3) hq3 (Φ ψ), ?_⟩
  · rintro ⟨g, hg⟩
    apply hαne
    apply fieldFactor_eq_one_of_inner h hq3
    refine ⟨ee (QuotientGroup.mk g), MulEquiv.ext fun y => ?_⟩
    obtain ⟨z, rfl⟩ := ee.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hΦ, hg]
    change ee (QuotientGroup.mk g) * ee (QuotientGroup.mk x) * (ee (QuotientGroup.mk g))⁻¹ = _
    rw [← map_inv, ← map_mul, ← map_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
  · exact lift_eq_suTwist h M _ (toGramSU h eK) ψ (Φ ψ) hM fun x => by
      rw [← quotEquivU3T_mk h hq2 eK, ← quotEquivU3T_mk h hq2 eK]
      exact (hΦ ψ x).symm

end Transport

theorem exists_fieldType_SU {F : Type} [Field F] [Finite F] {q : ℕ} (hF : Nat.card F = q ^ 2)
    (hq : q % 9 = 8) (hU : UnitaryH90 F q)
    {K : Type} [Group K] [Finite K] (hqs : CFSG.Open.IsQuasisimple K)
    (e : K ≃* ↥(CFSG.Open.StatedSU 3 q F)) (H : Subgroup (MulAut K))
    (hH : CFSG.Open.IsElemAbelian 3 H) (h27 : Nat.card H = 27) :
    ∃ ψ ∈ H, ¬ CFSG.HardMathSupport.Timmesfeld.ComponentBalance.IsInnerAut ψ ∧
      ∃ (M : GL (Fin 3) F) (σ : F ≃+* F),
        (∀ x ∈ CFSG.Open.StatedSU 3 q F, M * x * M⁻¹ ∈ CFSG.Open.StatedSU 3 q F) ∧
        ∀ x : K, ((e (ψ x) : ↥(CFSG.Open.StatedSU 3 q F)) : GL (Fin 3) F) =
          M * Matrix.GeneralLinearGroup.map (σ : F →+* F)
            (M⁻¹ * ((e x : ↥(CFSG.Open.StatedSU 3 q F)) : GL (Fin 3) F) * M) * M⁻¹ := by
  have hq2 : 2 < q := by omega
  obtain ⟨ℓ, f, h, rfl⟩ := exists_unitaryFieldData_SU hq2 hF
  let eK : K ≃* ↥(unitarySU ℓ f F 3) := e
  have hpF : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have h1 : (ℓ ^ f) ^ 2 % 9 = 1 := by rw [Nat.pow_mod, hq]
    have h2 : 0 < (ℓ ^ f) ^ 2 := by positivity
    omega
  obtain ⟨ψ, hψH, hni, M, σ, hMσ⟩ := exists_fieldType_SU_aux h hq2 hpF hF hU hqs eK H hH h27
  refine ⟨ψ, hψH, hni, (M : GL (Fin 3) F), σ, ?_, fun x => hMσ x⟩
  intro x hx
  have hext := SetLike.ext_iff.1 (unitarySU_eq_gramSU h 3)
  have hx' : x ∈ gramSU h ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := (hext x).1 hx
  exact (hext _).2 (conj_mem_gramSU h _ M.2 hx')

end CFSG.HardMathSupport.Solomon.Coordinator
