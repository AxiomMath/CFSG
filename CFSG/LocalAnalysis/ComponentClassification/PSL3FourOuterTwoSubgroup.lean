module

public import CFSG.HardMathSupport.Solomon.Coordinator.LayerCentralFix
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34Model
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndL34Facts
import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedL3C
import all CFSG.LocalAnalysis.ComponentClassification.PSL3FourActionData

public section

namespace CFSG.ComponentClassification.PSL3Four

open Subgroup CFSG.HardMathSupport.Solomon.Coordinator

theorem sq_mem_S_of_pow_two_pow_eq_one
    {ρ : Equiv.Perm (Fin 42)} (hρ : ρ ∈ R) {n : ℕ}
    (hn : ρ ^ 2 ^ n = 1) : ρ ^ 2 ∈ S := by
  have hXR : Subgroup.zpowers ρ ≤ R := Subgroup.zpowers_le_of_mem hρ
  have hX : IsPGroup 2 (Subgroup.zpowers ρ) := by
    obtain ⟨k, -, hk⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hn)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers]; exact hk)
  obtain ⟨c, hcR, hc⟩ :=
    CFSG.ComponentClassification.HSFLit.AutL34.exists_conj_mem_TR hXR hX
  have hcρ : c * ρ * c⁻¹ ∈ CFSG.ComponentClassification.HSFLit.AutL34.TR :=
    hc ρ (Subgroup.mem_zpowers ρ)
  obtain ⟨t, ht, v, hv, htv⟩ :=
    (CFSG.ComponentClassification.HSFLit.AutL34.mem_TR_iff (c * ρ * c⁻¹)).1 hcρ
  have hv2 : v * v = 1 := by
    rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact CFSG.ComponentClassification.HSFLit.AutL34.r₂_mul_self'
    · exact CFSG.ComponentClassification.HSFLit.AutL34.r₃_mul_self'
    · exact CFSG.ComponentClassification.HSFLit.AutL34.r₄_mul_self'
  have hvt : v * t * v⁻¹ ∈ CFSG.ComponentClassification.GrSLit.L34Facts.T0 :=
    (Subgroup.mem_set_normalizer_iff.1
      (CFSG.ComponentClassification.HSFLit.AutL34.TR_le_normalizer
        (CFSG.ComponentClassification.HSFLit.AutL34.vSet_subset_TR hv)) t).1 ht
  have hsq : (c * ρ * c⁻¹) ^ 2 ∈ S := by
    rw [htv, pow_two,
      show t * v * (t * v) = t * (v * t * v⁻¹) * (v * v) by group, hv2]
    simp only [mul_one]
    simpa using S.mul_mem (CFSG.ComponentClassification.GrSLit.L34Facts.T0_le_S ht)
      (S.mul_mem (CFSG.ComponentClassification.GrSLit.L34Facts.T0_le_S hvt) S.one_mem)
  refine conj_mem_S' hcR ?_
  have heq : c * ρ ^ 2 * c⁻¹ = (c * ρ * c⁻¹) ^ 2 := by
    rw [← MulAut.conj_apply c (ρ ^ 2), map_pow, MulAut.conj_apply]
  rw [heq]
  exact hsq

theorem sign_r₃ : Equiv.Perm.sign r₃ = -1 := by decide +kernel

theorem sign_r₄ : Equiv.Perm.sign r₄ = -1 := by decide +kernel

private theorem p8_sign_conj (c r : Equiv.Perm (Fin 42)) :
    Equiv.Perm.sign (c * r * c⁻¹) = Equiv.Perm.sign r := by
  have hcc : Equiv.Perm.sign c * Equiv.Perm.sign c = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign c) with h | h <;> rw [h] <;> decide
  rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv]
  calc Equiv.Perm.sign c * Equiv.Perm.sign r * Equiv.Perm.sign c
      = Equiv.Perm.sign r * (Equiv.Perm.sign c * Equiv.Perm.sign c) := by ac_rfl
    _ = Equiv.Perm.sign r := by rw [hcc, mul_one]

theorem exists_field_mem_of_four_le_card
    {Y : Type} [Group Y] [Finite Y]
    (hY : CFSG.Blueprint.LieModel Y .PSL 3 2 2) {A : Subgroup (MulAut Y)}
    (hA2 : IsPGroup 2 A)
    (hinn : ∀ a ∈ A, a ∈ (MulAut.conj : Y →* MulAut Y).range → a = 1)
    (h4 : 4 ≤ Nat.card A) :
    ∃ b ∈ A, b ≠ 1 ∧ b * b = 1 ∧ IsSimpleGroup ↥(fixSubgroup b) ∧
      (∃ c d : ↥(fixSubgroup b), c * d ≠ d * c) ∧ Nat.card ↥(fixSubgroup b) = 168 ∧
      ∀ c ∈ A, (∀ y : Y, b y = y → c y = y) → c = 1 ∨ c = b := by
  obtain ⟨M⟩ := CFSG.ComponentClassification.HarrisLit.HarrisEnd.nonempty_l34Model hY
  let τ : A →* Equiv.Perm (Fin 42) :=
    R.subtype.comp (M.Φ.toMonoidHom.comp A.subtype)
  have hexp2 : ∀ a ∈ A, a * a = 1 := by
    intro a ha
    set aA : A := ⟨a, ha⟩ with haA
    obtain ⟨k, hk⟩ := hA2 aA
    have h1 : τ aA ^ 2 ^ k = 1 := by
      rw [← map_pow, hk, map_one]
    have hkS : ((M.Φ (aA * aA) : R) : Equiv.Perm (Fin 42)) ∈ S := by
      have h3 := sq_mem_S_of_pow_two_pow_eq_one (ρ := τ aA) (M.Φ aA).2 h1
      simpa [τ, map_mul, Subgroup.coe_mul, pow_two] using h3
    have hinner : ((aA * aA : A) : MulAut Y) ∈ (MulAut.conj : Y →* MulAut Y).range :=
      (CFSG.ComponentClassification.HarrisLit.HarrisEnd.PermAutModel.mem_innAut_iff M
        ((aA * aA : A) : MulAut Y)).mpr hkS
    have h1' := hinn ((aA * aA : A) : MulAut Y) (aA * aA).2 hinner
    simpa [haA] using h1'
  let σ : A →* ℤˣ :=
    (Equiv.Perm.sign : Equiv.Perm (Fin 42) →* ℤˣ).comp τ
  have hsign : ∃ bA : A, bA ≠ 1 ∧ σ bA = 1 := by
    by_contra h
    push Not at h
    have hinj : Function.Injective σ := by
      intro x y hxy
      have h1 : σ (x * y⁻¹) = 1 := by
        rw [map_mul, map_inv, hxy, mul_inv_cancel]
      have h2 : x * y⁻¹ = 1 := by
        by_contra hne
        exact h (x * y⁻¹) hne h1
      rwa [mul_inv_eq_one] at h2
    have hcard : Nat.card A ≤ Nat.card ℤˣ := Nat.card_le_card_of_injective σ hinj
    have h2 : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    omega
  obtain ⟨bA, hbA1, hbAsign⟩ := hsign
  have hbsign : Equiv.Perm.sign (((M.Φ (bA : MulAut Y) : R) :
      Equiv.Perm (Fin 42))) = 1 := hbAsign
  have hbA : (bA : MulAut Y) ∈ A := bA.2
  have hb1 : (bA : MulAut Y) ≠ 1 := fun h => hbA1 (Subtype.ext h)
  have hb2 : (bA : MulAut Y) * (bA : MulAut Y) = 1 := hexp2 _ hbA
  have hbouter : ¬ ∃ g : Y, ∀ x : Y, (bA : MulAut Y) x = g * x * g⁻¹ := by
    rintro ⟨g, hg⟩
    have hmem : (bA : MulAut Y) ∈ (MulAut.conj : Y →* MulAut Y).range :=
      ⟨g, by ext x; rw [MulAut.conj_apply]; exact (hg x).symm⟩
    exact hb1 (hinn _ hbA hmem)
  have hborder : orderOf (M.Φ (bA : MulAut Y)) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact orderOf_eq_prime (by rwa [pow_two]) hb1
  have hmain : ∃ c ∈ R, ((M.Φ (bA : MulAut Y) : R) : Equiv.Perm (Fin 42)) =
      c * (r₂R : Equiv.Perm (Fin 42)) * c⁻¹ := by
    rcases (orderOf_eq_two_iff (M.Φ (bA : MulAut Y))).mp hborder with h | h | h | h
    · exfalso
      have hS : ((M.Φ (bA : MulAut Y) : R) : Equiv.Perm (Fin 42)) ∈ S :=
        mem_S_of_isConj₁ h
      have hinner : (bA : MulAut Y) ∈ (MulAut.conj : Y →* MulAut Y).range :=
        (CFSG.ComponentClassification.HarrisLit.HarrisEnd.PermAutModel.mem_innAut_iff M
          (bA : MulAut Y)).mpr hS
      exact hb1 (hinn _ hbA hinner)
    · exact eq_conj_of_isConj h
    · exfalso
      obtain ⟨c, hc, hcxe⟩ := eq_conj_of_isConj h
      have hxsign : Equiv.Perm.sign (((M.Φ (bA : MulAut Y) : R) :
          Equiv.Perm (Fin 42))) = -1 := by
        rw [hcxe, p8_sign_conj c (r₃R : Equiv.Perm (Fin 42))]
        exact sign_r₃
      rw [hbsign] at hxsign
      exact absurd hxsign (by decide)
    · exfalso
      obtain ⟨c, hc, hcxe⟩ := eq_conj_of_isConj h
      have hxsign : Equiv.Perm.sign (((M.Φ (bA : MulAut Y) : R) :
          Equiv.Perm (Fin 42))) = -1 := by
        rw [hcxe, p8_sign_conj c (r₄R : Equiv.Perm (Fin 42))]
        exact sign_r₄
      rw [hbsign] at hxsign
      exact absurd hxsign (by decide)
  obtain ⟨c, hcR, hcxe⟩ := hmain
  obtain ⟨ψ⟩ :=
    CFSG.ComponentClassification.HarrisLit.HarrisEnd.nonempty_centralizer_conj_equiv hcR hcxe
  obtain ⟨φ⟩ := M.nonempty_fixedPoints_equiv (bA : MulAut Y)
  let e : ↥(fixSubgroup (bA : MulAut Y)) ≃* C₂ := φ.trans ψ
  have : IsSimpleGroup C₂ := isSimpleGroup_C₂
  refine ⟨(bA : MulAut Y), hbA, hb1, hb2, e.isSimpleGroup, ?_, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := exists_mul_ne_C₂
    exact ⟨e.symm x, e.symm y, fun hcontra => hxy (by simpa using congrArg e hcontra)⟩
  · rw [Nat.card_congr e.toEquiv]
    exact card_C₂
  · intro c hcA hcfix
    have hc2 : c * c = 1 := hexp2 c hcA
    have hcb : c * (bA : MulAut Y) * (c * (bA : MulAut Y)) = 1 :=
      hexp2 _ (A.mul_mem hcA hbA)
    have hcomm : c * (bA : MulAut Y) = (bA : MulAut Y) * c := by
      have hcinv : (c * (bA : MulAut Y))⁻¹ = (bA : MulAut Y) * c := by
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hc2,
          inv_eq_of_mul_eq_one_right hb2]
      calc c * (bA : MulAut Y) = (c * (bA : MulAut Y))⁻¹ :=
            eq_inv_of_mul_eq_one_right hcb
        _ = (bA : MulAut Y) * c := hcinv
    have hRigid := CFSG.LocalAnalysis.WeakClosure81.outerFixedRigid_isL3
      (M := Y) (show CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3 Y 2 from hY)
    exact hRigid (bA : MulAut Y) hb2 hbouter c hc2 hcomm hcfix

end CFSG.ComponentClassification.PSL3Four

end
