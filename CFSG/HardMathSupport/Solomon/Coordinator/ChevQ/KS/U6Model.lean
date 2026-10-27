module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.FourUGeneric
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.Bal209TwoInner
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KAUGen

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

namespace KSFourU

open CFSG.Open CFSG.HardMathSupport.Dickson.I271 Bal209F4Aux OuterFourInAux
open scoped commutatorElement

section U6Model

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.Burgoyne.U
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {K0 : Type} [Field K0]

theorem uFactor_eq_one_of_mem_innSub (h : UnitaryFieldData 2 3 K0)
    {α : MulAut (StatedProj (StatedSU 6 (2 ^ 3) K0))}
    (hα : α ∈ innSub (StatedProj (StatedSU 6 (2 ^ 3) K0))) :
    uFactor h (by norm_num) (by norm_num) α = 1 := by
  obtain ⟨y, rfl⟩ := hα
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective y
  have e : (MulAut.conj (QuotientGroup.mk s : StatedProj (StatedSU 6 (2 ^ 3) K0))) =
      uConjAut h (by norm_num) ⟨(s : GL (Fin 6) K0), statedSU_le_uU h s.2⟩ := by
    refine MulEquiv.ext fun z => ?_
    obtain ⟨t, rfl⟩ := QuotientGroup.mk_surjective z
    have e1 := uConjAut_proj h (by norm_num : 1 ≤ 6)
      ⟨(s : GL (Fin 6) K0), statedSU_le_uU h s.2⟩ t
    refine Eq.trans ?_ e1.symm
    rw [MulAut.conj_apply]
    rfl
  have h1 := uFactor_apply h (n := 6) (by norm_num) (by norm_num)
    ⟨(s : GL (Fin 6) K0), statedSU_le_uU h s.2⟩ 1
  rw [map_one, mul_one] at h1
  rw [e]
  exact h1

theorem uFieldAut_not_mem_innSub (h : UnitaryFieldData 2 3 K0) {σ : K0 ≃+* K0} (hσ : σ ≠ 1) :
    uFieldAut h (by norm_num) σ ∉ innSub (StatedProj (StatedSU 6 (2 ^ 3) K0)) := by
  intro hin
  apply hσ
  have h1 := uFactor_eq_one_of_mem_innSub h hin
  have h2 := uFactor_apply h (n := 6) (by norm_num) (by norm_num) 1 σ
  rw [map_one, one_mul] at h2
  rw [← h2]
  exact h1

@[expose] noncomputable def eigMult {n : ℕ} {K : Type} [Field K] (g : GL (Fin n) K) (c : K) : ℕ :=
  Module.finrank K (LinearMap.ker (Matrix.toLin' (g : Matrix (Fin n) (Fin n) K) -
    c • (LinearMap.id : (Fin n → K) →ₗ[K] (Fin n → K))))

@[expose] noncomputable def maxEig {n : ℕ} {K : Type} [Field K] [Fintype K]
    (g : GL (Fin n) K) : ℕ :=
  Finset.univ.sup (eigMult g)

@[expose] def HeisData {K : Type} [Field K] [Fintype K] (g₁ g₂ g₃ : GL (Fin 6) K) : Prop :=
  (∃ κ : Kˣ, κ ≠ 1 ∧ g₁ * g₂ * g₁⁻¹ * g₂⁻¹ = Matrix.GeneralLinearGroup.scalar (Fin 6) κ) ∧
    g₁ * g₃ = g₃ * g₁ ∧ g₂ * g₃ = g₃ * g₂ ∧ ∀ c : K, 3 ∣ eigMult g₃ c

end U6Model

namespace U6Bridge

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.ComponentClassification.Burgoyne.U
  CFSG.GH74.GLS.Stage2.Signalizer.Ivk8 CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem isEntrywiseProj_uFieldAut {K : Type} [Field K] {p f n : ℕ} (h : UnitaryFieldData p f K)
    (hn : 1 ≤ n) (σ : K ≃+* K) :
    IsEntrywiseProj (StatedSU n (p ^ f) K) σ (uFieldAut h hn σ) := by
  intro g
  exact ⟨⟨glAut σ (g : GL (Fin n) K), uFieldSU_mem h σ g⟩, Units.ext rfl,
    uFieldAut_proj h hn σ g⟩

theorem isEntrywiseProj_unique {n : ℕ} {K : Type} [Field K] (H : Subgroup (GL (Fin n) K))
    (σ : K ≃+* K) {ψ₁ ψ₂ : MulAut (StatedProj H)} (h₁ : IsEntrywiseProj H σ ψ₁)
    (h₂ : IsEntrywiseProj H σ ψ₂) : ψ₁ = ψ₂ := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H g =>
    obtain ⟨g₁, hg₁, e₁⟩ := h₁ g
    obtain ⟨g₂, hg₂, e₂⟩ := h₂ g
    have : g₁ = g₂ := Subtype.ext (hg₁.trans hg₂.symm)
    rw [e₁, e₂, this]

theorem exists_uFieldAut_of_fieldAutU6 {S : Type} [Group S] {φ : MulAut S}
    (hφ : FieldAutU 6 S φ) :
    ∃ (K : Type) (_ : Field K) (h : UnitaryFieldData 2 3 K)
      (e : S ≃* StatedProj (StatedSU 6 (2 ^ 3) K)) (σ : K ≃+* K)
      (γ : MulAut (StatedProj (StatedSU 6 (2 ^ 3) K))),
      σ ≠ 1 ∧ Odd (orderOf σ) ∧
        γ * MulAut.congr e φ * γ⁻¹ = uFieldAut h (by norm_num) σ := by
  obtain ⟨K, hK, hfin, e, σ, γ, hcard, hσ1, hodd, hent⟩ := hφ
  have h : UnitaryFieldData 2 3 K := ⟨Nat.prime_two, by norm_num, by rw [hcard]; norm_num⟩
  exact ⟨K, hK, h, e, σ, γ, hσ1, hodd,
    isEntrywiseProj_unique _ σ hent (isEntrywiseProj_uFieldAut h (by norm_num) σ)⟩

theorem conj_uFieldAut_of_order_three {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)
    (a : MulAut (StatedProj (StatedSU 6 (2 ^ 3) K))) (ha : orderOf a = 3)
    (σ : K ≃+* K) (hσ : orderOf σ = 3)
    (hfac : uFactor h (by norm_num) (by norm_num) a = σ) :
    ∃ M : uU h 6, (uConjAut h (by norm_num) M)⁻¹ * a * uConjAut h (by norm_num) M =
      uFieldAut h (by norm_num) σ := by
  have hn : 3 ≤ 6 := by norm_num
  have hq : ¬((6 : ℕ) = 3 ∧ 2 ^ 3 = 2) := by norm_num
  set E := MulAut.congr (uTransport h (by norm_num : 1 ≤ 6)) with hE
  set a' : MulAut (primeFormP h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) := E a with ha'
  have ha'3 : orderOf a' = 3 := by rw [ha', MulEquiv.orderOf_eq, ha]
  obtain ⟨-, -, -, -, -, M, hM⟩ :=
    CFSG.HardMathSupport.Lang.Coordinator.unitary_prime_semilinear_field_descent' h hn hq
      Nat.prime_three (by norm_num) a' ha'3 σ hfac hσ
  refine ⟨M, ?_⟩
  have h1 := congrArg E.symm hM
  rw [map_mul, map_mul, map_inv, ha', MulEquiv.symm_apply_apply] at h1
  exact h1

theorem exists_scalar_of_commute_field {K : Type} [Field K] {p f n : ℕ}
    (h : UnitaryFieldData p f K) (hn : 3 ≤ n) {A : uU h n} {τ σ : K ≃+* K}
    (hc : (uConjAut h (by omega) A * uFieldAut h (by omega) τ) * uFieldAut h (by omega) σ =
      uFieldAut h (by omega) σ * (uConjAut h (by omega) A * uFieldAut h (by omega) τ))
    (hcomm : Commute σ τ) :
    ∃ c : Kˣ, glAut σ (A : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.scalar (Fin n) c * (A : GL (Fin n) K) := by
  have hn1 : 1 ≤ n := by omega
  have hστ : uFieldAut h hn1 σ * uFieldAut h hn1 τ = uFieldAut h hn1 τ * uFieldAut h hn1 σ := by
    rw [← map_mul, ← map_mul, hcomm.eq]
  have e1 := uFieldAut_mul_uConjAut h hn1 σ A
  have e2 : uConjAut h hn1 A * (uFieldAut h hn1 τ * uFieldAut h hn1 σ) =
      uConjAut h hn1 (uGlAut h σ A) * (uFieldAut h hn1 τ * uFieldAut h hn1 σ) := by
    calc uConjAut h hn1 A * (uFieldAut h hn1 τ * uFieldAut h hn1 σ)
        = (uConjAut h hn1 A * uFieldAut h hn1 τ) * uFieldAut h hn1 σ := by rw [mul_assoc]
      _ = uFieldAut h hn1 σ * (uConjAut h hn1 A * uFieldAut h hn1 τ) := hc
      _ = (uFieldAut h hn1 σ * uConjAut h hn1 A) * uFieldAut h hn1 τ := by rw [mul_assoc]
      _ = (uConjAut h hn1 (uGlAut h σ A) * uFieldAut h hn1 σ) * uFieldAut h hn1 τ := by rw [e1]
      _ = uConjAut h hn1 (uGlAut h σ A) * (uFieldAut h hn1 σ * uFieldAut h hn1 τ) := by
          rw [mul_assoc]
      _ = uConjAut h hn1 (uGlAut h σ A) * (uFieldAut h hn1 τ * uFieldAut h hn1 σ) := by rw [hστ]
  have e3 : uConjAut h hn1 A = uConjAut h hn1 (uGlAut h σ A) := mul_right_cancel e2
  have e4 : uConjAut h hn1 (A⁻¹ * uGlAut h σ A) = 1 := by
    rw [map_mul, map_inv, e3, inv_mul_cancel]
  obtain ⟨c, hc'⟩ := (uConjAut_eq_one_iff h hn _).1 e4
  refine ⟨c, ?_⟩
  have h5 : (A : GL (Fin n) K)⁻¹ * glAut σ (A : GL (Fin n) K) =
      Matrix.GeneralLinearGroup.scalar (Fin n) c := hc'
  have h6 : glAut σ (A : GL (Fin n) K) =
      (A : GL (Fin n) K) * Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    rw [← h5]
    group
  rw [h6]
  exact commute_scalar c (A : GL (Fin n) K)

theorem inner_of_commute_fieldAut {K : Type} [Field K] (h : UnitaryFieldData 2 3 K)
    (A : uU h 6) (τ σ : K ≃+* K) (hσ : orderOf σ = 3)
    (hc : (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) τ) *
        uFieldAut h (by norm_num) σ =
      uFieldAut h (by norm_num) σ * (uConjAut h (by norm_num) A * uFieldAut h (by norm_num) τ)) :
    uConjAut h (by norm_num) A ∈ innSub (StatedProj (StatedSU 6 (2 ^ 3) K)) := by
  classical
  haveI := h.finite
  have hn1 : 1 ≤ 6 := by norm_num
  have hn3 : 3 ≤ 6 := by norm_num
  obtain ⟨c, hc'⟩ := exists_scalar_of_commute_field h hn3 hc
    (CFSG.RankThree.PartOne.KCUnitaryModel.ringAut_commute h σ τ)
  have hcU : Matrix.GeneralLinearGroup.scalar (Fin 6) c ∈
      primeFormUnitary h ((1 : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) := by
    have e : Matrix.GeneralLinearGroup.scalar (Fin 6) c =
        glAut σ (A : GL (Fin 6) K) * (A : GL (Fin 6) K)⁻¹ := by
      rw [hc']
      group
    rw [e]
    exact mul_mem (glAut_mem_primeFormUnitary h uGram_one σ A.2) (inv_mem A.2)
  have hcN : h.norm (c : K) = 1 := norm_eq_one_of_scalar_mem_primeFormUnitary h hn1 1 hcU
  have hc9 : (c : K) ^ 9 = 1 := by
    have := h.norm_eq_pow (c : K)
    rw [hcN] at this
    norm_num at this
    exact this.symm
  have hσ3 : σ ^ 3 = 1 := by
    rw [← hσ]
    exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hσ
    omega
  have hN1 : σ (σ (c : K)) * σ (c : K) * (c : K) = 1 := by
    have e2 : glAut σ (glAut σ (A : GL (Fin 6) K)) =
        Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.map (σ : K →* K) c) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) c * (A : GL (Fin 6) K)) := by
      rw [hc', map_mul, CFSG.RankThree.UnitaryDescent.glAut_scalar, hc']
    have e3 : glAut σ (glAut σ (glAut σ (A : GL (Fin 6) K))) =
        Matrix.GeneralLinearGroup.scalar (Fin 6)
            (Units.map (σ : K →* K) (Units.map (σ : K →* K) c)) *
          (Matrix.GeneralLinearGroup.scalar (Fin 6) (Units.map (σ : K →* K) c) *
            (Matrix.GeneralLinearGroup.scalar (Fin 6) c * (A : GL (Fin 6) K))) := by
      rw [e2, map_mul, CFSG.RankThree.UnitaryDescent.glAut_scalar, map_mul,
        CFSG.RankThree.UnitaryDescent.glAut_scalar, hc']
    have e4 : glAut σ (glAut σ (glAut σ (A : GL (Fin 6) K))) = A := by
      have : (glAut (σ ^ 3)) (A : GL (Fin 6) K) =
          glAut σ (glAut σ (glAut σ (A : GL (Fin 6) K))) := by
        rw [pow_succ, pow_succ, pow_one, map_mul, map_mul]
        rfl
      rw [← this, hσ3, map_one]
      rfl
    have e5 : Matrix.GeneralLinearGroup.scalar (Fin 6)
        (Units.map (σ : K →* K) (Units.map (σ : K →* K) c) *
          (Units.map (σ : K →* K) c * c)) * (A : GL (Fin 6) K) = 1 * (A : GL (Fin 6) K) := by
      rw [one_mul, map_mul, map_mul, mul_assoc, mul_assoc, ← e3, e4]
    have e6 := mul_right_cancel e5
    have e7 := (CFSG.RankThree.PartOne.KCUnitaryModel.scalar_eq_one_iff hn1).1 e6
    have e8 := congrArg Units.val e7
    simpa [Units.val_mul, Units.coe_map, mul_assoc] using e8
  have hK : Nat.card K = 2 ^ 6 := by rw [h.card]
  obtain ⟨d, T, hd0, hd3, hT, hT3, hσT⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube Nat.prime_two (f := 6)
      (by norm_num) K hK σ hσ3 hσ1
  have hd : d = 2 := by omega
  subst hd
  have hTx : ∀ x : K, T x = x ^ 4 := fun x => by rw [hT x]; norm_num
  have hσx : (∀ x : K, σ x = x ^ 4) ∨ (∀ x : K, σ x = x ^ 16) := by
    rcases hσT with rfl | rfl
    · exact Or.inl hTx
    · refine Or.inr fun x => ?_
      have : (T ^ 2) x = T (T x) := by rw [pow_two]; rfl
      rw [this, hTx, hTx, ← pow_mul]
  have hc3 : (c : K) ^ 3 = 1 := by
    rcases hσx with hx | hx
    · rw [hx, hx] at hN1
      have h21 : (c : K) ^ 21 = 1 := by
        calc (c : K) ^ 21 = ((c : K) ^ 4) ^ 4 * (c : K) ^ 4 * (c : K) := by ring
          _ = 1 := hN1
      have := pow_gcd_eq_one.2 ⟨h21, hc9⟩
      simpa using this
    · rw [hx, hx] at hN1
      have h273 : (c : K) ^ 273 = 1 := by
        calc (c : K) ^ 273 = ((c : K) ^ 16) ^ 16 * (c : K) ^ 16 * (c : K) := by ring
          _ = 1 := hN1
      have := pow_gcd_eq_one.2 ⟨h273, hc9⟩
      simpa using this
  set Am : Matrix (Fin 6) (Fin 6) K := ((A : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) with hAm
  have hdet_σ : σ Am.det = (c : K) ^ 6 * Am.det := by
    have e1 := congrArg
      (fun g : GL (Fin 6) K => ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K)) hc'
    simp only [coe_glAut, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at e1
    have e3 : σ Am.det = (Am.map σ).det := by
      have := RingHom.map_det σ.toRingHom Am
      rw [RingHom.mapMatrix_apply] at this
      exact this
    rw [e3, e1, Matrix.det_mul]
    simp [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const]
    rfl
  have hδ0 : Am.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (A : GL (Fin 6) K).isUnit).ne_zero
  have hδN : h.norm Am.det = 1 := norm_det_eq_one h 1 A.2
  have hδ9 : Am.det ^ 9 = 1 := by
    have := h.norm_eq_pow Am.det
    rw [hδN] at this
    norm_num at this
    exact this.symm
  have hc6 : (c : K) ^ 6 = 1 := by
    calc (c : K) ^ 6 = ((c : K) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hc3]; norm_num
  have hδσ : σ Am.det = Am.det := by rw [hdet_σ, hc6, one_mul]
  have hδ3 : Am.det ^ 3 = 1 := by
    rcases hσx with hx | hx
    · rw [hx] at hδσ
      have : Am.det * Am.det ^ 3 = Am.det * 1 := by rw [← pow_succ', mul_one]; exact hδσ
      exact mul_left_cancel₀ hδ0 this
    · rw [hx] at hδσ
      have h15 : Am.det ^ 15 = 1 := by
        have : Am.det * Am.det ^ 15 = Am.det * 1 := by rw [← pow_succ', mul_one]; exact hδσ
        exact mul_left_cancel₀ hδ0 this
      have := pow_gcd_eq_one.2 ⟨h15, hδ9⟩
      simpa using this
  have hG : Nat.card (Units.map h.normHom).ker = 9 := by
    have := (unitary_field_norm h).2.2.1
    norm_num at this
    exact this
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (Units.map h.normHom).ker)
  have hord : orderOf g = 9 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, hG]
  have hδmem : (Units.mk0 Am.det hδ0) ∈ (Units.map h.normHom).ker := by
    rw [h.mem_ker_normUnits, Units.val_mk0]
    exact hδN
  set δu : (Units.map h.normHom).ker := ⟨Units.mk0 Am.det hδ0, hδmem⟩ with hδu
  have hδu3 : δu ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa [hδu] using hδ3
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1
    (mem_powers_iff_mem_zpowers.2 (hg δu))
  have hk3 : 3 ∣ k := by
    have h1 : g ^ (k * 3) = 1 := by rw [pow_mul, hk, hδu3]
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at h2
    omega
  obtain ⟨m, rfl⟩ := hk3
  set x : (Units.map h.normHom).ker := g ^ (5 * m) with hx
  have hx6 : x ^ 6 = δu := by
    rw [hx, ← pow_mul, ← hk]
    have : g ^ (5 * m * 6) = g ^ (3 * m) * (g ^ 9) ^ (3 * m) := by
      rw [← pow_mul, ← pow_add]
      congr 1
      ring
    rw [this, ← hord, pow_orderOf_eq_one, one_pow, mul_one]
  have hxN : h.norm ((x : Kˣ) : K) = 1 := (h.mem_ker_normUnits).1 x.2
  have hxdet : Am.det = ((x : Kˣ) : K) ^ 6 := by
    have := congrArg (fun y : (Units.map h.normHom).ker => ((y : Kˣ) : K)) hx6
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, hδu, Units.val_mk0] at this
    exact this.symm
  exact ka_uConjAut_inner_of_det h hn1 A (x : Kˣ) hxN hxdet

end U6Bridge

section U6FieldModel

open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.Burgoyne.U
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

variable {K0 : Type} [Field K0]

theorem eq_pow_of_cube {σ τ : K0 ≃+* K0} (hK : Nat.card K0 = 2 ^ 6) (hσ3 : σ ^ 3 = 1)
    (hσ1 : σ ≠ 1) (hτ3 : τ ^ 3 = 1) : τ = 1 ∨ τ = σ ∨ τ = σ ^ 2 := by
  by_cases hτ1 : τ = 1
  · exact Or.inl hτ1
  · right
    obtain ⟨d, T, hd0, hd3, hT, hT3, hσT⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube Nat.prime_two (f := 6)
        (by norm_num) K0 hK σ hσ3 hσ1
    obtain ⟨d', T', hd0', hd3', hT', hT3', hτT⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.exists_frobenius_of_cube Nat.prime_two (f := 6)
        (by norm_num) K0 hK τ hτ3 hτ1
    have hd : d = d' := by omega
    subst hd
    have hTT : T' = T := RingEquiv.ext fun c => by rw [hT', hT]
    subst hTT
    have hT3' : T' ^ 3 = 1 := hT3
    have hT2 : (T' ^ 2) ^ 2 = T' := by
      calc (T' ^ 2) ^ 2 = T' ^ 4 := by rw [← pow_mul]
        _ = T' ^ 3 * T' := by rw [pow_succ]
        _ = T' := by rw [hT3', one_mul]
    rcases hσT with rfl | rfl <;> rcases hτT with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inr hT2.symm
    · exact Or.inl rfl

theorem exists_pow_mul_mem_innSub (h : UnitaryFieldData 2 3 K0) {σ : K0 ≃+* K0}
    (hσ : orderOf σ = 3) {ψ : MulAut (StatedProj (StatedSU 6 (2 ^ 3) K0))} (hψ3 : ψ ^ 3 = 1)
    (hc : ψ * uFieldAut h (by norm_num) σ = uFieldAut h (by norm_num) σ * ψ) :
    ∃ i : ℕ, ψ * (uFieldAut h (by norm_num) σ) ^ i ∈
      innSub (StatedProj (StatedSU 6 (2 ^ 3) K0)) := by
  haveI := h.finite
  have hn3 : 3 ≤ 6 := by norm_num
  have hq : ¬((6 : ℕ) = 3 ∧ 2 ^ 3 = 2) := by norm_num
  obtain ⟨A, τ, rfl⟩ := exists_uConjAut_mul_uFieldAut h hn3 hq ψ
  have hinn : uConjAut h (by norm_num) A ∈ innSub (StatedProj (StatedSU 6 (2 ^ 3) K0)) :=
    U6Bridge.inner_of_commute_fieldAut h A τ σ hσ hc
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    intro h1; rw [h1, orderOf_one] at hσ; omega
  have hτ3 : τ ^ 3 = 1 := by
    have h1 := congrArg (uFactor h hn3 hq) hψ3
    rw [map_pow, uFactor_apply, map_one] at h1
    exact h1
  have hK : Nat.card K0 = 2 ^ 6 := by rw [h.card]
  rcases eq_pow_of_cube hK hσ3 hσ1 hτ3 with h1 | h1 | h1
  · refine ⟨0, ?_⟩
    rw [h1, map_one, mul_one, pow_zero, mul_one]
    exact hinn
  · refine ⟨2, ?_⟩
    have : uFieldAut (n := 6) h (by norm_num) τ * (uFieldAut (n := 6) h (by norm_num) σ) ^ 2 =
        uFieldAut (n := 6) h (by norm_num) (τ * σ ^ 2) := by rw [map_mul, map_pow]
    rw [mul_assoc, this, h1]
    have : σ * σ ^ 2 = 1 := by rw [← pow_succ']; exact hσ3
    rw [this, map_one, mul_one]
    exact hinn
  · refine ⟨1, ?_⟩
    have : uFieldAut (n := 6) h (by norm_num) τ * (uFieldAut (n := 6) h (by norm_num) σ) ^ 1 =
        uFieldAut (n := 6) h (by norm_num) (τ * σ ^ 1) := by rw [map_mul, map_pow]
    rw [mul_assoc, this, h1]
    have : σ ^ 2 * σ ^ 1 = 1 := by rw [← pow_add]; exact hσ3
    rw [this, map_one, mul_one]
    exact hinn

end U6FieldModel

section InnerAtBridge

open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open CFSG.HardMathSupport.Timmesfeld.Coordinator (autCenterQuot)
open Bal209TwoInnerAux

theorem conj_mem_innSub {G : Type} [Group G] (γ : MulAut G) {α : MulAut G}
    (hα : α ∈ innSub G) : γ * α * γ⁻¹ ∈ innSub G := by
  obtain ⟨g, rfl⟩ := hα
  refine ⟨γ g, ?_⟩
  refine MulEquiv.ext fun z => ?_
  simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]

theorem mem_innSub_iff_conj {G : Type} [Group G] (γ : MulAut G) {α : MulAut G} :
    γ * α * γ⁻¹ ∈ innSub G ↔ α ∈ innSub G := by
  refine ⟨fun h => ?_, conj_mem_innSub γ⟩
  have := conj_mem_innSub γ⁻¹ h
  simpa [mul_assoc] using this

theorem actHom_eq_autCenterQuot {X : Type} [Group X] (K : Subgroup X)
    (n : ↥(Subgroup.normalizer (K : Set X))) :
    actHom K n = autCenterQuot ↥K (K.normalizerMonoidHom n) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H k => rfl

theorem congr_conj' {G C : Type} [Group G] [Group C] (e : G ≃* C) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) := by
  refine MulEquiv.ext fun z => ?_
  simp [MulAut.congr_apply, MulAut.conj_apply, map_mul, map_inv]

theorem actHom_eq_conj_of_mul {X : Type} [Group X] {K : Subgroup X} {k c : X} (hk : k ∈ K)
    (hc : c ∈ Subgroup.centralizer (K : Set X))
    (hb : k * c ∈ Subgroup.normalizer (K : Set X)) :
    actHom K ⟨k * c, hb⟩ =
      MulAut.conj (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [actHom_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      ← QuotientGroup.mk_mul]
    congr 1
    apply Subtype.ext
    have hcy : c * (y : X) = (y : X) * c := (Subgroup.mem_centralizer_iff.1 hc (y : X) y.2).symm
    show k * c * (y : X) * (k * c)⁻¹ = k * (y : X) * k⁻¹
    calc k * c * (y : X) * (k * c)⁻¹ = k * (c * (y : X)) * c⁻¹ * k⁻¹ := by group
      _ = k * ((y : X) * c) * c⁻¹ * k⁻¹ := by rw [hcy]
      _ = k * (y : X) * k⁻¹ := by group

theorem innerAt_iff_congr_mem_innSub {X : Type} [Group X] {K : Subgroup X}
    (hperf : commutator ↥K = ⊤) {C : Type} [Group C] (e : (↥K ⧸ Subgroup.center ↥K) ≃* C)
    {b : X} (hb : b ∈ Subgroup.normalizer (K : Set X)) :
    InnerAt K b ↔ MulAut.congr e (actHom K ⟨b, hb⟩) ∈ innSub C := by
  constructor
  · intro hin
    obtain ⟨k, hk, c, hc, hbkc⟩ := innerAt_iff.1 hin
    subst hbkc
    rw [actHom_eq_conj_of_mul hk hc hb, congr_conj']
    exact ⟨_, rfl⟩
  · intro h
    rw [actHom_eq_autCenterQuot] at h
    exact innerAt_of_congr_mem_inner hperf e hb h

end InnerAtBridge

section U6Field

open CFSG.ComponentClassification.Burgoyne.U CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem u6FourUField : FourUField IsU6EightIndex (FieldAutU 6) := by
  intro X _ _ K B hK hBSC hBN hLie hF
  have hperf : commutator ↥K = ⊤ := hK.2.2.1
  have hBel : IsElemAbelian 3 B := hBSC.2.1
  obtain ⟨φ, hφB, hφF⟩ := hF
  obtain ⟨x, hxN, hxB, rfl⟩ := mem_autImage.1 hφB
  obtain ⟨K0, fK0, h, e, σ, γ, hσ1, hodd, hγ⟩ := U6Bridge.exists_uFieldAut_of_fieldAutU6 hφF
  haveI := h.finite
  let Ψ : ↥(Subgroup.normalizer (K : Set X)) →*
      MulAut (StatedProj (StatedSU 6 (2 ^ 3) K0)) :=
    ((MulAut.conj γ).toMonoidHom).comp ((MulAut.congr e).toMonoidHom.comp (actHom K))
  have hΨ : ∀ n, Ψ n = γ * MulAut.congr e (actHom K n) * γ⁻¹ := fun n => by
    simp [Ψ, MulAut.conj_apply]
  have hΨx : Ψ ⟨x, hxN⟩ = uFieldAut h (by norm_num) σ := by rw [hΨ]; exact hγ
  have hinner : ∀ (b : X) (hb : b ∈ B), InnerAt K b ↔
      Ψ ⟨b, hBN hb⟩ ∈ innSub (StatedProj (StatedSU 6 (2 ^ 3) K0)) := by
    intro b hb
    rw [innerAt_iff_congr_mem_innSub hperf e (hBN hb), hΨ, mem_innSub_iff_conj]
  have hcomm : ∀ (b b' : X) (hb : b ∈ B) (hb' : b' ∈ B),
      Ψ ⟨b, hBN hb⟩ * Ψ ⟨b', hBN hb'⟩ = Ψ ⟨b', hBN hb'⟩ * Ψ ⟨b, hBN hb⟩ := by
    intro b b' hb hb'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_of_elemAbelian hBel hb hb').eq
  have hcube : ∀ (b : X) (hb : b ∈ B), Ψ ⟨b, hBN hb⟩ ^ 3 = 1 := by
    intro b hb
    rw [← map_pow]
    have : (⟨b, hBN hb⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (hBel.2 b hb)
    rw [this, map_one]
  have hn3 : 3 ≤ 6 := by norm_num
  have hq : ¬((6 : ℕ) = 3 ∧ 2 ^ 3 = 2) := by norm_num
  have hσ3 : σ ^ 3 = 1 := by
    have h1 := hcube x hxB
    rw [hΨx] at h1
    have h2 := congrArg (uFactor h hn3 hq) h1
    have h3 := uFactor_apply h (n := 6) hn3 hq 1 σ
    rw [map_one, one_mul] at h3
    rw [map_pow, h3, map_one] at h2
    exact h2
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hK64 : Nat.card K0 = 2 ^ 6 := by rw [h.card]
  have hxnot : ¬ InnerAt K x := by
    intro hin
    have := (hinner x hxB).1 hin
    rw [hΨx] at this
    exact uFieldAut_not_mem_innSub h hσ1 this
  refine ⟨x, hxB, hxnot, ?_, ?_⟩
  · intro b hb
    obtain ⟨i, hi⟩ := exists_pow_mul_mem_innSub h hσord (hcube b hb)
      (by rw [← hΨx]; exact hcomm b x hb hxB)
    refine ⟨i, (hinner _ (B.mul_mem (B.pow_mem hxB i) hb)).2 ?_⟩
    have e1 : Ψ ⟨x ^ i * b, hBN (B.mul_mem (B.pow_mem hxB i) hb)⟩ =
        Ψ ⟨x, hxN⟩ ^ i * Ψ ⟨b, hBN hb⟩ := by
      rw [← map_pow, ← map_mul]
      rfl
    rw [e1, hΨx]
    have e2 : (uFieldAut h (by norm_num) σ) ^ i * Ψ ⟨b, hBN hb⟩ =
        Ψ ⟨b, hBN hb⟩ * (uFieldAut h (by norm_num) σ) ^ i := by
      refine (Commute.pow_left ?_ i).eq
      rw [← hΨx]
      exact (hcomm x b hxB hb)
    rw [e2]
    exact hi
  · intro a ha hanot
    have hψa : Ψ ⟨a, hBN ha⟩ ∉ innSub (StatedProj (StatedSU 6 (2 ^ 3) K0)) :=
      fun hmem => hanot ((hinner a ha).2 hmem)
    obtain ⟨A, τ, hAτ⟩ := exists_uConjAut_mul_uFieldAut h hn3 hq (Ψ ⟨a, hBN ha⟩)
    have hcσ : Ψ ⟨a, hBN ha⟩ * uFieldAut h (by norm_num) σ =
        uFieldAut h (by norm_num) σ * Ψ ⟨a, hBN ha⟩ := by
      rw [← hΨx]; exact hcomm a x ha hxB
    have hAinn : uConjAut h (by norm_num) A ∈ innSub (StatedProj (StatedSU 6 (2 ^ 3) K0)) := by
      refine U6Bridge.inner_of_commute_fieldAut h A τ σ hσord ?_
      rw [← hAτ]; exact hcσ
    have hτ1 : τ ≠ 1 := by
      intro h1
      apply hψa
      rw [hAτ, h1, map_one, mul_one]
      exact hAinn
    have hτ3 : τ ^ 3 = 1 := by
      have h1 := congrArg (uFactor h hn3 hq) (hcube a ha)
      rw [hAτ, map_pow, uFactor_apply, map_one] at h1
      exact h1
    have hτord : orderOf τ = 3 := orderOf_eq_prime hτ3 hτ1
    have hψa1 : Ψ ⟨a, hBN ha⟩ ≠ 1 := fun h1 => hψa (h1 ▸ (innSub _).one_mem)
    have hψaord : orderOf (Ψ ⟨a, hBN ha⟩) = 3 := orderOf_eq_prime (hcube a ha) hψa1
    have hfac : uFactor h hn3 hq (Ψ ⟨a, hBN ha⟩) = τ := by rw [hAτ, uFactor_apply]
    obtain ⟨M, hM⟩ := U6Bridge.conj_uFieldAut_of_order_three h (Ψ ⟨a, hBN ha⟩) hψaord τ hτord hfac
    refine ⟨K0, fK0, h.finite, e, τ, (uConjAut h (by norm_num) M)⁻¹ * γ, h.card, hτ1,
      ?_, ?_⟩
    · rw [hτord]; decide
    · have e3 : (uConjAut h (by norm_num) M)⁻¹ * γ * MulAut.congr e (actHom K ⟨a, hBN ha⟩) *
          ((uConjAut h (by norm_num) M)⁻¹ * γ)⁻¹ = uFieldAut h (by norm_num) τ := by
        rw [← hM, hΨ]
        simp only [mul_inv_rev, inv_inv, mul_assoc]
      rw [e3]
      exact U6Bridge.isEntrywiseProj_uFieldAut h (by norm_num) τ

end U6Field

section U6Defs

open CFSG.ComponentClassification.Burgoyne.Proj

variable {K0 : Type} [Field K0]

@[expose] def IsU6BigCompIndex (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, IsTwoPow q 3 ∧ (d = .A 1 q ∨ d = .twistedA 3 q ∨ d = .twistedA 4 q)

@[expose] def ActsAs {X : Type} [Group X] (K : Subgroup X) (e : (↥K ⧸ Subgroup.center ↥K) ≃*
    StatedProj (StatedSU 6 (2 ^ 3) K0)) (y : X) (g : StatedSU 6 (2 ^ 3) K0) : Prop :=
  ∃ hy : y ∈ Subgroup.normalizer (K : Set X),
    MulAut.congr e (actHom K ⟨y, hy⟩) = MulAut.conj (projH _ g)

end U6Defs

section SelHelpers

theorem center_quot_eq_bot {Y : Type} [Group Y] (hY : CFSG.Open.IsQuasisimple Y) :
    Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := by
  haveI := hY.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (Y ⧸ Subgroup.center Y)) with h | h
  · exact h
  · exfalso
    have hcommS : ∀ a b : Y ⧸ Subgroup.center Y, a * b = b * a := fun a b =>
      (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b)) a
    have hcomm : ∀ a b : Y, ⁅a, b⁆ ∈ Subgroup.center Y := by
      intro a b
      rw [← QuotientGroup.eq_one_iff]
      have e := map_commutatorElement (QuotientGroup.mk' (Subgroup.center Y)) a b
      change (QuotientGroup.mk' (Subgroup.center Y)) ⁅a, b⁆ = 1
      rw [e]
      exact commutatorElement_eq_one_iff_mul_comm.2 (hcommS _ _)
    have hZ : Subgroup.center Y = ⊤ := by
      rw [eq_top_iff, ← hY.1, _root_.commutator_def]
      exact Subgroup.commutator_le.2 (fun a _ b _ => hcomm a b)
    obtain ⟨q, hq⟩ := exists_ne (1 : Y ⧸ Subgroup.center Y)
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    apply hq
    rw [QuotientGroup.eq_one_iff, hZ]
    trivial

theorem conj_inj_of_center_bot {G : Type} [Group G] (hZ : Subgroup.center G = ⊥) :
    Function.Injective (MulAut.conj : G →* MulAut G) := by
  intro g g' hgg
  have hc : g'⁻¹ * g ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun x => by
    have hx := congrArg (fun φ : MulAut G => φ x) hgg
    simp only [MulAut.conj_apply] at hx
    calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
      _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [← hx]
      _ = g'⁻¹ * g * x := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact (inv_mul_eq_one.1 hc).symm

@[expose] def IsU6Bal207CompIndex (d : TauCeti.LieTypeIndex) : Prop :=
  ∃ q : TauCeti.PrimePower, IsTwoPow q 3 ∧ (d = .twistedA 3 q ∨ d = .twistedA 4 q)

theorem isU6Bal207Comp_bal207 : ∀ d, IsU6Bal207CompIndex d →
    Bal207Index 3 d ∧ ¬ CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex d := by
  rintro d ⟨q, hq, rfl | rfl⟩
  · refine ⟨?_, by simp [CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex]⟩
    show 3 = 3 ∧ (((IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ ¬ 3 ∣ 3 + 1) ∨ (IsTwoPow q 1 ∧ 3 = 5))
    exact ⟨rfl, Or.inl ⟨Or.inr hq, by decide⟩⟩
  · refine ⟨?_, by simp [CFSG.HardMathSupport.Dickson.Bal207.IsG2EightIndex]⟩
    show 3 = 3 ∧ (((IsTwoPow q 1 ∨ IsTwoPow q 3) ∧ ¬ 3 ∣ 4 + 1) ∨ (IsTwoPow q 1 ∧ 4 = 5))
    exact ⟨rfl, Or.inl ⟨Or.inr hq, by decide⟩⟩

theorem normalizer_of_card_le_two_comps {X : Type} [Group X] [Finite X] {K B : Subgroup X} {y : X}
    (hBel : IsElemAbelian 3 B) (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hyB : y ∈ B)
    (h3 : ∀ J₁ J₂ J₃ : Subgroup X,
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₁ →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₂ →
      GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J₃ →
        J₁ = J₂ ∨ J₁ = J₃ ∨ J₂ = J₃) {J : Subgroup X}
    (hJ : GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J) :
    B ≤ Subgroup.normalizer (J : Set X) := fun b hb =>
  KSF4Kit.mem_normalizer_of_card_le_two hBel
    (𝒥 := {J' | GLAPComponent 3 (K ⊓ Subgroup.centralizer ({y} : Set X)) J'})
    (fun J₁ hJ₁ J₂ hJ₂ J₃ hJ₃ => h3 J₁ J₂ J₃ hJ₁ hJ₂ hJ₃)
    (fun b' hb' J' hJ' => KSF4Kit.glaPComponent_gLBConj_centralizer (hBN hb')
      (commute_of_elemAbelian hBel hb' hyB).eq hJ') hb hJ

end SelHelpers

end KSFourU

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

end
