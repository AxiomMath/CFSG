module

public import CFSG.RankThree.PartOne.KE6.Phi6Layer
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public noncomputable section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KE6
open CFSG.RankThree.PartOne.KE (twistedTorus)
open scoped Matrix MatrixGroups

theorem e6Six_dvd_sq_cube_sub_one {p q : ℕ} (hq : 1 ≤ q)
    (hpq : (p : ℤ) ∣ (q : ℤ) ^ 2 - (q : ℤ) + 1) : p ∣ (q ^ 2) ^ 3 - 1 := by
  have h1 : (((q ^ 2) ^ 3 - 1 : ℕ) : ℤ) = ((q : ℤ) ^ 2 - (q : ℤ) + 1) *
      ((q : ℤ) ^ 2 + (q : ℤ) + 1) * ((q : ℤ) ^ 2 - 1) := by
    have : 1 ≤ (q ^ 2) ^ 3 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ hq)
    push_cast [Nat.cast_sub this]
    ring
  have h2 : (p : ℤ) ∣ (((q ^ 2) ^ 3 - 1 : ℕ) : ℤ) := by
    rw [h1]
    exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hpq _) _
  exact_mod_cast h2

theorem e6Six_dvd_card_SL3 {F : Type} [Field F] [Finite F] {p : ℕ} (h : p ∣ Nat.card F ^ 3 - 1) :
    p ∣ Nat.card (SL(3, F)) := by
  rw [← CFSG.Open.StatedAPI.card_statedSL, CFSG.Open.StatedAPI.card_statedSL_three]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_left h _) _

section Order



theorem e6_six_p_dvd_card_P {K : Type} [Field K] [Finite K] {Ω : Type} [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    {x : ModGL Tag.E6 Ω} (hx : x ∈ twistedTorus (phi6N Ω) Fr) (hxp : orderOf x = p)
    (hA2A2 : ∃ w : WeylGroup Tag.E6,
      (w • ·) '' torusRootKernel x = parabolicRoots Tag.E6 supportA2A2) :
    ¬ Nat.Coprime p (Nat.card ↥(phi6P Ω Fr (torusRootKernel x))) := by
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, k₂, h₁, h₂, hwker, hk₂, hlayer⟩ :=
    phi6_A2A2_layer (K := K) hℓ hf hK hFr hp hp3 hpq hx hxp hA2A2
  set n : ModGL Tag.E6 Ω := canonicalRep (coxeterSystem Tag.E6) Ω w with hn
  let φ : SL(3, k₂) →* ModGL Tag.E6 Ω :=
    (MulAut.conj n⁻¹).toMonoidHom.comp ((twoA2Mul Ω).comp
      (((MulAut.conj h₁).toMonoidHom.comp (Matrix.SpecialLinearGroup.map k₂.subtype)).prod
        ((MulAut.conj h₂).toMonoidHom.comp ((Matrix.SpecialLinearGroup.map Fr).comp
          (Matrix.SpecialLinearGroup.map k₂.subtype)))))
  have hφ : ∀ A : SL(3, k₂), φ A = n⁻¹ * twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A *
      h₁⁻¹, h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
        h₂⁻¹) * n := fun A => by
    simp [φ, MulAut.conj_apply]
  have hφP : φ.range ≤ phi6P Ω Fr (torusRootKernel x) := by
    rintro _ ⟨A, rfl⟩
    rw [hφ]
    exact hlayer A
  have hq2 : (ℓ ^ f) ^ 2 = ℓ ^ (2 * f) := by rw [← pow_mul, mul_comm]
  have hk₂2 : ∀ c : Ω, c ∈ k₂ ↔ c ^ ℓ ^ (2 * f) = c := fun c => by
    rw [hk₂ c, hq2]
  have hk₂card : Nat.card k₂ = (ℓ ^ f) ^ 2 := by
    rw [hq2, ← natCard_setOf_pow_eq_self (Ω := Ω) (ℓ := ℓ) (by omega : 2 * f ≠ 0)]
    exact Nat.card_congr (Equiv.subtypeEquivRight hk₂2)
  have : Finite k₂ := Nat.finite_of_card_ne_zero (by
    rw [hk₂card]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hdvd : p ∣ Nat.card SL(3, k₂) := by
    apply e6Six_dvd_card_SL3
    rw [hk₂card]
    exact e6Six_dvd_sq_cube_sub_one (Nat.one_le_pow _ _ hℓ.pos) hpq
  have hkerc : φ.ker ≤ Subgroup.center SL(3, k₂) := by
    intro A hA
    rw [MonoidHom.mem_ker, hφ] at hA
    have h1 : twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
        h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          h₂⁻¹) = 1 := by
      have h2 : twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
          h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
            h₂⁻¹) = n * (n⁻¹ * twoA2Mul Ω (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹,
          h₂ * Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A) *
            h₂⁻¹) * n) * n⁻¹ := by group
      rw [h2, hA]
      group
    obtain ⟨l, hl, hX, -⟩ := (twoA2Mul_eq_one_iff _ _).1 h1
    have hXc : (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹ : SL(3, Ω)) ∈
        Subgroup.center SL(3, Ω) :=
      Matrix.SpecialLinearGroup.mem_center_iff.2 ⟨l, by simpa using hl, hX.symm⟩
    have hMc : (Matrix.SpecialLinearGroup.map k₂.subtype A : SL(3, Ω)) ∈
        Subgroup.center SL(3, Ω) := by
      have h5 := (Subgroup.center SL(3, Ω)).normal_of_characteristic.conj_mem _ hXc h₁⁻¹
      have h6 : h₁⁻¹ * (h₁ * Matrix.SpecialLinearGroup.map k₂.subtype A * h₁⁻¹) * h₁⁻¹⁻¹ =
          Matrix.SpecialLinearGroup.map k₂.subtype A := by group
      rwa [h6] at h5
    rw [Subgroup.mem_center_iff]
    intro B
    apply specialLinearGroup_map_injective (ψ := k₂.subtype) k₂.subtype.injective
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.1 hMc _
  have hcenter : Nat.card (Subgroup.center SL(3, k₂)) ≤ 3 := by
    have h := Nat.card_congr
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' (n := Fin 3) (R := k₂) 0).toEquiv
    rw [h]
    simpa using card_rootsOfUnity (k := 3) (R := k₂)
  have hker3 : Nat.card φ.ker ≤ 3 := (Subgroup.card_le_of_le hkerc).trans hcenter
  have hcard : Nat.card SL(3, k₂) = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker).trans (mul_comm _ _)
  have hkerpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hdvdR : p ∣ Nat.card φ.range := by
    rw [hcard] at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · exact absurd (Nat.le_of_dvd hkerpos h) (by omega)
    · exact h
  rw [Nat.Prime.coprime_iff_not_dvd hp, not_not]
  exact hdvdR.trans (Subgroup.card_dvd_of_le hφP)

end Order

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
