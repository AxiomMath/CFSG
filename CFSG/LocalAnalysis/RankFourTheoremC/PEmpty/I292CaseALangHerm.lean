module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALangBase
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherGraphFieldInvolution
public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang

open Matrix CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem isUnitaryInvolution_of_involution {F : Type} [Field F] [Finite F] {σ : F ≃+* F}
    (hσ : σ ≠ 1) (hσσ : σ * σ = 1) : IsUnitaryInvolution σ := by
  obtain ⟨p, f, hp, hf, hF⟩ := exists_card_eq_prime_pow F
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨e, he⟩, hσpow⟩ := even_and_eq_pow_of_involution_prime hp hf hF hσ hσσ
  haveI : CharP F p := by
    have := Fintype.ofFinite F
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  have hcard : Nat.card F = (p ^ e) ^ 2 := by rw [hF, he]; ring
  have hσU : σ = CFSG.LieType.BorelTits.unitaryInvolution F p e := by
    ext x
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply, hσpow]
    congr 2
    omega
  rw [hσU]
  exact isUnitaryInvolution_unitaryInvolution hcard

theorem exists_mul_conjTr_eq_of_involution {F : Type} [Field F] [Finite F] {n : ℕ}
    {σ : F ≃+* F} (hσ : σ ≠ 1) (hσσ : σ * σ = 1) {G : Matrix (Fin n) (Fin n) F}
    (hG : conjTr σ G = G) (hdet : G.det ≠ 0) :
    ∃ H : GL (Fin n) F,
      (H : Matrix (Fin n) (Fin n) F) * conjTr σ (H : Matrix (Fin n) (Fin n) F) = G := by
  have hσσx : ∀ x, σ (σ x) = x := fun x => by
    have := congrArg (fun τ : F ≃+* F => τ x) hσσ
    simpa using this
  obtain ⟨P, hP⟩ := CFSG.LieType.Steinberg.exists_conjTr_mul_mul_eq_one_of_isUnitaryInvolution
    (isUnitaryInvolution_of_involution hσ hσσ) hG hdet
  refine ⟨conjTrInvGL σ P, ?_⟩
  have hBP : G = conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
    calc G = conjTr σ ((P : Matrix (Fin n) (Fin n) F) * ((P⁻¹ : GL (Fin n) F) :
          Matrix (Fin n) (Fin n) F)) * G * ((P : Matrix (Fin n) (Fin n) F) *
            ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one, conjTr_one, Matrix.one_mul,
            Matrix.mul_one]
      _ = conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
          (conjTr σ (P : Matrix (Fin n) (Fin n) F) * G * (P : Matrix (Fin n) (Fin n) F)) *
            ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
          rw [conjTr_mul]
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  change conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
    conjTr σ (conjTr σ ((P⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) = G
  rw [conjTr_conjTr hσσx, hBP]

theorem exists_sq_fixed_ne {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    (h : Even (orderOf σ)) : ∃ x, σ (σ x) = x ∧ σ x ≠ x := by
  classical
  obtain ⟨p, f, hp, hf, hK⟩ := exists_card_eq_prime_pow K
  have : Finite (K ≃+* K) := finite_ringEquiv K
  have hfix : ∀ τ : K ≃+* K, orderOf τ ∣ f ∧
      Nat.card (semilinearFixedSubfield τ) = p ^ (f / orderOf τ) := fun τ => by
    obtain ⟨h1, h2, -⟩ := CFSG.GroupTheory.SteinbergBK.coprime_finite_field_semilinear_fixed_basis
      (V := Fin 0 → K) hp hf hK τ rfl (m := 0) (Module.finrank_fin_fun K) (AddEquiv.refl _)
      (fun _ _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
    exact ⟨h1, h2⟩
  by_contra hcon
  push Not at hcon
  have hsub : ∀ x : K, x ∈ semilinearFixedSubfield (σ ^ 2) → x ∈ semilinearFixedSubfield σ := by
    intro x hx
    have hx' : (σ ^ 2) x = x := RingHom.mem_eqLocusField.mp hx
    rw [pow_two] at hx'
    exact RingHom.mem_eqLocusField.mpr (hcon x hx')
  have : Finite (semilinearFixedSubfield σ) := Subtype.finite
  have hle : Nat.card (semilinearFixedSubfield (σ ^ 2)) ≤ Nat.card (semilinearFixedSubfield σ) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, hsub x.1 x.2⟩) fun x y hxy => ?_
    exact Subtype.ext (by simpa using congrArg Subtype.val hxy)
  obtain ⟨r, hr⟩ := h
  have hmpos : 0 < orderOf σ := orderOf_pos σ
  have hrpos : 0 < r := by omega
  have hord2 : orderOf (σ ^ 2) = r := by
    rw [orderOf_pow_of_dvd two_ne_zero ⟨r, by omega⟩]
    omega
  obtain ⟨q, hq⟩ := (hfix σ).1
  rw [(hfix σ).2, (hfix (σ ^ 2)).2, hord2] at hle
  have h1 : f / orderOf σ = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q hmpos
  have h2 : f / r = 2 * q := by
    rw [hq, hr]
    exact Nat.div_eq_of_eq_mul_left hrpos (by ring)
  rw [h1, h2] at hle
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hq0 : q = 0 := by omega
  rw [hq0, mul_zero] at hq
  omega

@[expose] def sqFixedField {K : Type} [Field K] (σ : K ≃+* K) : Subfield K :=
  RingHom.eqLocusField ((σ : K →+* K).comp (σ : K →+* K)) (RingHom.id K)

theorem mem_sqFixedField {K : Type} [Field K] {σ : K ≃+* K} {x : K} :
    x ∈ sqFixedField σ ↔ σ (σ x) = x :=
  RingHom.mem_eqLocusField

@[expose] def sqFixedAut {K : Type} [Field K] (σ : K ≃+* K) :
    sqFixedField σ ≃+* sqFixedField σ where
  toFun x := ⟨σ x, mem_sqFixedField.2 (congrArg σ (mem_sqFixedField.1 x.2))⟩
  invFun x := ⟨σ x, mem_sqFixedField.2 (congrArg σ (mem_sqFixedField.1 x.2))⟩
  left_inv x := Subtype.ext (mem_sqFixedField.1 x.2)
  right_inv x := Subtype.ext (mem_sqFixedField.1 x.2)
  map_mul' x y := Subtype.ext (map_mul σ (x : K) (y : K))
  map_add' x y := Subtype.ext (map_add σ (x : K) (y : K))

theorem exists_mul_conjTr_eq {K : Type} [Field K] [Finite K] {n : ℕ} {σ : K ≃+* K}
    (hσ : ∃ x, σ (σ x) = x ∧ σ x ≠ x) {B : Matrix (Fin n) (Fin n) K}
    (hB : conjTr σ B = B) (hdet : B.det ≠ 0) :
    ∃ H : GL (Fin n) K,
      (H : Matrix (Fin n) (Fin n) K) * conjTr σ (H : Matrix (Fin n) (Fin n) K) = B := by
  classical
  have hBe : ∀ i j, σ (B j i) = B i j := fun i j => by
    simpa [conjTr] using congrFun (congrFun hB i) j
  have hBmem : ∀ i j, B i j ∈ sqFixedField σ := fun i j => by
    rw [mem_sqFixedField, hBe j i, hBe i j]
  have hσ₁σ₁ : sqFixedAut σ * sqFixedAut σ = 1 := by
    ext x
    exact mem_sqFixedField.1 x.2
  have hσ₁ne : sqFixedAut σ ≠ 1 := by
    obtain ⟨x, hx, hxne⟩ := hσ
    intro h1
    apply hxne
    have := congrArg (fun τ : sqFixedField σ ≃+* sqFixedField σ =>
      ((τ ⟨x, mem_sqFixedField.2 hx⟩ : sqFixedField σ) : K)) h1
    exact this
  let B₁ : Matrix (Fin n) (Fin n) (sqFixedField σ) := Matrix.of fun i j => ⟨B i j, hBmem i j⟩
  have hB₁ : conjTr (sqFixedAut σ) B₁ = B₁ := by
    ext i j
    exact hBe i j
  have : Finite (sqFixedField σ) := Subtype.finite
  have e2 : B₁.map (sqFixedField σ).subtype = B := by
    ext i j
    rfl
  have hdet₁ : B₁.det ≠ 0 := by
    intro h0
    apply hdet
    have h1 := RingHom.map_det (sqFixedField σ).subtype B₁
    rw [h0, map_zero] at h1
    have h2 : (sqFixedField σ).subtype.mapMatrix B₁ = B := e2
    rw [h2] at h1
    exact h1.symm
  obtain ⟨H₁, hH₁⟩ := exists_mul_conjTr_eq_of_involution hσ₁ne hσ₁σ₁ hB₁ hdet₁
  refine ⟨Units.map (sqFixedField σ).subtype.mapMatrix.toMonoidHom H₁, ?_⟩
  have e1 : ∀ X : Matrix (Fin n) (Fin n) (sqFixedField σ),
      (conjTr (sqFixedAut σ) X).map (sqFixedField σ).subtype =
        conjTr σ (X.map (sqFixedField σ).subtype) := fun X => by
    ext i j
    rfl
  calc (((Units.map (sqFixedField σ).subtype.mapMatrix.toMonoidHom H₁ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) *
        conjTr σ ((Units.map (sqFixedField σ).subtype.mapMatrix.toMonoidHom H₁ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)
      = ((H₁ : Matrix (Fin n) (Fin n) (sqFixedField σ)) *
          conjTr (sqFixedAut σ) (H₁ : Matrix (Fin n) (Fin n) (sqFixedField σ))).map
            (sqFixedField σ).subtype := by
        rw [Matrix.map_mul, e1]
        rfl
    _ = B := by rw [hH₁, e2]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseALang
