module

public import CFSG.HardMathSupport.Dickson.Bal207.OrthEightBasic

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.OrthEight

open Module CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonalAut CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {K : Type} [Field K] [Finite K]

theorem ringEquiv_pow_three_eq_one_of_card_eight (hK : Nat.card K = 8) (σ : K ≃+* K) :
    σ ^ 3 = 1 := by
  have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K
    (by rw [hK]; norm_num : Nat.card K = 2 ^ 3)).1
  have h1 : σ ^ Nat.card (RingAut K) = 1 := pow_card_eq_one'
  rwa [h] at h1

theorem exists_isometry_of_mem_matrixProjectiveImage (hK : Nat.card K = 8) {d : ℕ} (hd : 0 < d)
    {Q : QuadraticForm K (Fin d → K)} (α : MulAut (ProjOrthDerived Q))
    (hα : MulAut.congr (coordBridge Q hd).symm α ∈ matrixProjectiveImage Q)
    (hco : Nat.Coprime 3 (orderOf α)) :
    ∃ G ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ y : orthDerived Q,
      ∃ hy : G * (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) * G⁻¹ ∈ orthDerived Q,
        α (QuotientGroup.mk y) = QuotientGroup.mk ⟨G * y * G⁻¹, hy⟩ := by
  classical
  have : Finite ((Fin d → K) ≃ₗ[K] (Fin d → K)) := Finite.of_injective
    (fun e : (Fin d → K) ≃ₗ[K] (Fin d → K) => (e : (Fin d → K) → (Fin d → K)))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have : Finite (ProjOrthDerived Q) := Finite.of_surjective
    (QuotientGroup.mk : orthDerived Q → ProjOrthDerived Q) QuotientGroup.mk_surjective
  have : Finite (MulAut (ProjOrthDerived Q)) := Finite.of_injective
    (fun e : MulAut (ProjOrthDerived Q) => (e : ProjOrthDerived Q → ProjOrthDerived Q))
    fun e₁ e₂ h => MulEquiv.ext (congrFun h)
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff Q _).mp hα
  set n := 3 ^ Nat.totient (orderOf α) with hn
  have hαn : α ^ n = α := by
    have hmod : n % orderOf α = 1 % orderOf α := Nat.ModEq.pow_totient hco
    rw [← pow_mod_orderOf, hmod, pow_mod_orderOf, pow_one]
  have h3n : 3 ∣ n := dvd_pow_self 3 (Nat.totient_pos.mpr (orderOf_pos α)).ne'
  have hσn : (g ^ n : similarityPairs Q).val.right = 1 := by
    obtain ⟨m, hm⟩ := h3n
    have h1 : (g ^ n : similarityPairs Q).val.right = (g.val.right) ^ n :=
      map_pow SemidirectProduct.rightHom g.val n
    rw [h1, hm, pow_mul, ringEquiv_pow_three_eq_one_of_card_eight hK, one_pow]
  obtain ⟨L, hLv, hLs⟩ : ∃ L : (Fin d → K) ≃ₗ[K] (Fin d → K),
      (∀ v, L v = coordinateSemilinearMap (g ^ n : similarityPairs Q).val v) ∧
      ∀ v, L.symm v = (coordinateSemilinearMap (g ^ n : similarityPairs Q).val).symm v :=
    ⟨(coordinateSemilinearMap (g ^ n : similarityPairs Q).val).toLinearEquiv fun c v => by
      rw [coordinateSemilinearMap_smul, hσn]
      rfl, fun v => rfl, fun v => rfl⟩
  obtain ⟨μ, hμ⟩ := (mem_similarityPairs_iff Q _).mp (g ^ n).property
  have hQL : ∀ v, Q (L v) = (μ : K) * Q v := fun v => by
    rw [hLv, hμ, hσn]
    rfl
  obtain ⟨l, hl⟩ := FiniteField.isSquare_of_char_two (ringChar_eq_two hK) (μ : K)
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact μ.ne_zero (by rw [hl, mul_zero])
  obtain ⟨s, hsv⟩ : ∃ s : (Fin d → K) ≃ₗ[K] (Fin d → K), ∀ v, s v = l⁻¹ • v :=
    ⟨LinearEquiv.smulOfNeZero K (Fin d → K) l⁻¹ (inv_ne_zero hl0), fun v => rfl⟩
  have hs : ∀ f : (Fin d → K) ≃ₗ[K] (Fin d → K), s * f = f * s := fun f =>
    LinearEquiv.ext fun v => by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hsv, hsv, map_smul]
  have hG : s * L ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => ?_
    rw [LinearEquiv.mul_apply, hsv, QuadraticMap.map_smul, hQL, hl, smul_eq_mul, ← mul_assoc,
      mul_mul_mul_comm, inv_mul_cancel₀ hl0, one_mul, one_mul]
  have hconj : ∀ f : (Fin d → K) ≃ₗ[K] (Fin d → K), s * L * f * (s * L)⁻¹ = L * f * L⁻¹ := by
    intro f
    calc s * L * f * (s * L)⁻¹ = s * (L * f * L⁻¹) * s⁻¹ := by simp only [mul_inv_rev, mul_assoc]
      _ = L * f * L⁻¹ := by rw [hs, mul_inv_cancel_right]
  refine ⟨s * L, hG, fun y => ⟨conj_mem_orthDerived hG y.2, ?_⟩⟩
  have h1 := coordBridge_conjugation Q hd (g ^ n) y
    ⟨s * L * y * (s * L)⁻¹, conj_mem_orthDerived hG y.2⟩ fun v => by
      show (s * L * (y : (Fin d → K) ≃ₗ[K] (Fin d → K)) * (s * L)⁻¹) v = _
      rw [hconj]
      show L ((y : (Fin d → K) ≃ₗ[K] (Fin d → K)) (L.symm v)) = _
      rw [hLv, hLs]
  have hφ : matrixProjectiveConjugationHom Q (g ^ n) = MulAut.congr (coordBridge Q hd).symm α := by
    have h2 : matrixProjectiveConjugationHom Q g = MulAut.congr (coordBridge Q hd).symm α := hg
    rw [map_pow, h2, ← map_pow, hαn]
  rw [hφ] at h1
  have h3 : (MulAut.congr (coordBridge Q hd).symm α)
      ((coordBridge Q hd).symm (QuotientGroup.mk y)) =
      (coordBridge Q hd).symm (α (QuotientGroup.mk y)) := by
    rw [MulAut.congr_apply]
    simp
  rw [h3, MulEquiv.apply_symm_apply] at h1
  exact h1

end CFSG.HardMathSupport.Dickson.Bal207.OrthEight

end
