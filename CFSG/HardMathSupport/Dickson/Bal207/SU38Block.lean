module

public import CFSG.HardMathSupport.Dickson.Bal207.FCBlock
public import CFSG.HardMathSupport.Dickson.Bal207.SU38Reduction
import CFSG.HardMathSupport.Dickson.Bal207.UniFrame
import CFSG.RankThree.PartOne.KC.UnitaryRegularUnipotentLift

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.HardMathSupport.Dickson.I271 CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Bal207.Uni

variable {ℓ f : ℕ} {E : Type} [Field E] {X : Type} [Group X]

theorem su38Toral_of_hom {J B : Subgroup X} (hJ : CFSG.Open.IsQuasisimple ↥J)
    (h : UnitaryFieldData ℓ f E) (hℓ : ℓ = 2) (hf : f = 1 ∨ f = 3) (hne : ℓ ^ f ≠ 2)
    (φ : ↥J →* primeFormP h (oneGram E 3)) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center ↥J) {D : Subgroup (GL (Fin 3) E)} (hD : IsOmegaOneTorus D)
    (hBD : ∀ A : primeFormUnitary h (oneGram E 3), (A : GL (Fin 3) E) ∈ D →
      ∃ (b : X) (hb : b ∈ Subgroup.normalizer (J : Set X)), b ∈ B ∧
        ∀ j : ↥J, φ (J.normalizerMonoidHom ⟨b, hb⟩ j) = primeFormConjHom h _ A (φ j)) :
    SU38Toral B J := by
  have hZ : Subgroup.center (primeFormP h (oneGram E 3)) = ⊥ :=
    CFSG.RankThree.PartOne.KCUnitaryRegular.center_primeFormP_eq_bot h (C := 1)
      CFSG.HardMathSupport.Timmesfeld.LinearRank.isPrimeFormGram_one le_rfl (fun hh => hne hh.2)
  have hkerZ := ker_eq_center_of_surjective φ hφ hker hZ
  refine ⟨hJ, ℓ, f, E, inferInstance, h, hℓ, hf, hne, centerQuotientEquivOfHom φ hφ hkerZ, D, hD,
    fun A hA => ?_⟩
  obtain ⟨b, hb, hbB, hc⟩ := hBD A hA
  refine ⟨b, hb, hbB, MulEquiv.ext fun y => ?_⟩
  obtain ⟨j, rfl⟩ := hφ y
  have he : (centerQuotientEquivOfHom φ hφ hkerZ).symm (φ j) = QuotientGroup.mk j :=
    (MulEquiv.symm_apply_eq _).2 rfl
  show centerQuotientEquivOfHom φ hφ hkerZ
    (actHom J ⟨b, hb⟩ ((centerQuotientEquivOfHom φ hφ hkerZ).symm (φ j))) = _
  rw [he, actHom_mk, centerQuotientEquivOfHom_mk]
  exact hc j

theorem su38Toral_of_block [Finite X] {K B J : Subgroup X} {S : Type} [Group S]
    (hB : IsSCp 3 ⊤ B) (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hJK : J ≤ K) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (h : UnitaryFieldData ℓ f E) (hℓ : ℓ = 2) (hf : f = 1 ∨ f = 3) (hne : ℓ ^ f ≠ 2)
    {ι : ↥(primeFormUnitary h (oneGram E 3)) →* S} (hι : Function.Injective ι)
    (hJι : (J.comap K.subtype).map (uniMap e) = (blockSU h 3).map ι)
    (x : ↥B → blockGamma h 3)
    (hx : ∀ (b : ↥B) (g : ↥(primeFormUnitary h (oneGram E 3))),
      uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left))
    (P : ↥(primeFormUnitary h (oneGram E 3)))
    (hP : ∀ b : ↥B, ∃ D : ↥(primeFormUnitary h (oneGram E 3)),
      ((D : GL (Fin 3) E) : Matrix (Fin 3) (Fin 3) E).IsDiag ∧ ∃ φ : E ≃+* E,
        (∀ c : E, c ^ 3 = 1 → φ c = c) ∧
          (SemidirectProduct.inl P)⁻¹ * x b * SemidirectProduct.inl P =
            SemidirectProduct.inl D * SemidirectProduct.inr φ) :
    SU38Toral B J := by
  have h3 : 3 ∣ ℓ ^ f + 1 := by
    subst hℓ
    rcases hf with rfl | rfl <;> norm_num
  obtain ⟨ω, hω, hω1, -⟩ := exists_cube_root_bar h h3
  refine su38Toral_of_hom hJ h hℓ hf hne (blockHom e h hJK hι hJι P)
    (blockHom_surjective e h hJK hι hJι P) (ker_blockHom_le_center e h hJK hι hJι hJ.1 P)
    (isOmegaOneTorus_cubeDiag hω hω1) fun A hA => ?_
  have hA3 : A ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hA.2)
  have hfix : ∀ (b : X) (hb : b ∈ B),
      uniAut e ⟨b, hBK hb⟩ (ι (P * A * P⁻¹)) = ι (P * A * P⁻¹) := by
    intro b hb
    obtain ⟨D, hD, φ, hφ, hPx⟩ := hP ⟨b, hb⟩
    rw [hx ⟨b, hb⟩, conj_inl_eq_of_frame h hD hφ hA hPx, SemidirectProduct.left_inl]
  have hs3 : (ι (P * A * P⁻¹)) ^ 3 = 1 := by
    rw [← map_pow, conj_pow, hA3, mul_one, mul_inv_cancel, map_one]
  obtain ⟨y, hyB, hyK, hyψ⟩ := uni_exists_mem_of_fixed hB hBK hZ e hs3 hfix
  refine ⟨y, hBJ hyB, hyB, fun j => ?_⟩
  rw [blockHom_conj e h hJK hι hJι P hyK hyψ (hBJ hyB) j,
    show P⁻¹ * (P * A * P⁻¹) * P = A by group]

end CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

end
