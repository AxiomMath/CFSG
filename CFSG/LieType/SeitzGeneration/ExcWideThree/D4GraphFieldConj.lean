module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4GraphFieldCentral
public import CFSG.LieType.SeitzGeneration.ExcWideThree.D4FieldCaseB

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.HardMathSupport.Lang.D4Three CFSG.HardMathSupport.Lang.E6Descent CFSG.RankThree.PartOne.CTP

section GraphFieldConj


variable {K : Type} [Field K]

theorem fixedSubgroup_inv_eq_ctp {P : Type*} [Group P] (β : MulAut P) :
    fixedSubgroup β⁻¹ = fixedSubgroup β := by
  rw [← fixedCommutingProduct_fixedSubgroup_eq, ← fixedCommutingProduct_fixedSubgroup_eq]
  exact fixedSubgroup_inv_eq β

theorem ne_inv_of_cube {T : K ≃+* K} (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1) : T ≠ T⁻¹ := by
  intro h
  apply hT1
  have h2 : T * T = 1 := by
    calc T * T = T * T⁻¹ := congrArg (T * ·) h
      _ = 1 := mul_inv_cancel T
  calc T = T * (T * T) := by rw [h2, mul_one]
    _ = T ^ 3 := (pow_three T).symm
    _ = 1 := hT3

theorem d4Twist_add_three (j : ℤ) (σ : K ≃+* K) : d4Twist (j + 3) σ = d4Twist j σ :=
  twistedEntrywiseAut_add_mul_order TwistTag.D4 j 1 σ

theorem fixedSubgroup_d4Twist_two (σ : K ≃+* K) :
    fixedSubgroup (d4Twist 2 σ) = fixedSubgroup (d4Twist 1 σ⁻¹) := by
  rw [← fixedCommutingProduct_fixedSubgroup_eq, ← fixedCommutingProduct_fixedSubgroup_eq]
  exact fixedSubgroup_twistedEntrywiseAut_D4_two σ

open scoped _root_.Classical in
@[expose] noncomputable def d4GfTwist (T σ : K ≃+* K) (ε : ℕ) : K ≃+* K :=
  by
    classical
    exact if (σ = T ∧ ε = 1) ∨ (σ = T⁻¹ ∧ ε = 2) then T else T⁻¹

theorem exists_conj_fixedSubgroup_D4_graphField {ℓ f e : ℕ} [Fact ℓ.Prime] [Finite K]
    [CharP K ℓ] (hK : Nat.card K = ℓ ^ f) (hK4 : 4 ≤ Nat.card K) (he : 1 ≤ e) (hef : e * 3 = f)
    (T σ : K ≃+* K) (hT : ∀ c, T c = c ^ (ℓ ^ e)) (hT3 : T ^ 3 = 1) (hT1 : T ≠ 1)
    (hσ : σ = T ∨ σ = T⁻¹) {ε : ℕ} (hε : ε = 1 ∨ ε = 2) (g : adjointGroup Tag.D4 K)
    (a : Fin Tag.D4.rank → Kˣ) (β : MulAut (adjointGroup Tag.D4 K)) (hβ3 : β ^ 3 = 1)
    (hβ : β = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) :
    ∃ ψ : MulAut (adjointGroup Tag.D4 K),
      fixedSubgroup (ψ * β * ψ⁻¹) = fixedSubgroup (d4Twist 1 (d4GfTwist T σ ε)) := by
  classical
  have hTinv : T ≠ T⁻¹ := ne_inv_of_cube hT3 hT1
  rcases hσ with rfl | rfl
  · obtain ⟨ψ, hψ⟩ := exists_conj_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef σ hT β hβ3
      g a ε hβ
    have hψ' : ψ * β * ψ⁻¹ = d4Twist (ε : ℤ) σ := hψ
    refine ⟨ψ, ?_⟩
    rcases hε with rfl | rfl
    · have : d4GfTwist σ σ 1 = σ := if_pos (Or.inl ⟨rfl, rfl⟩)
      rw [this, hψ', Nat.cast_one]
    · have : d4GfTwist σ σ 2 = σ⁻¹ := if_neg (by
        rintro (⟨-, h⟩ | ⟨h, -⟩)
        · exact absurd h (by decide)
        · exact hTinv h)
      rw [this, hψ', Nat.cast_ofNat]
      exact fixedSubgroup_d4Twist_two σ
  · obtain ⟨ψ, hψ⟩ := exists_conj_inv_eq_twistedEntrywiseAut_of_normalForm K hK hK4 he hef T T⁻¹
      hT (mul_inv_cancel T) β hβ3 g a ε hβ
    have hψ' : ψ * β⁻¹ * ψ⁻¹ = d4Twist (-(ε : ℤ)) T := hψ
    refine ⟨ψ, ?_⟩
    have hconj : ψ * β⁻¹ * ψ⁻¹ = (ψ * β * ψ⁻¹)⁻¹ := by group
    rw [← fixedSubgroup_inv_eq_ctp, ← hconj, hψ']
    rcases hε with rfl | rfl
    · have hshift : d4Twist (-((1 : ℕ) : ℤ)) T = d4Twist 2 T := by
        rw [← d4Twist_add_three]
        norm_num
      have : d4GfTwist T T⁻¹ 1 = T⁻¹ := if_neg (by
        rintro (⟨h, -⟩ | ⟨-, h⟩)
        · exact hTinv h.symm
        · exact absurd h (by decide))
      rw [this, hshift]
      exact fixedSubgroup_d4Twist_two T
    · have hshift : d4Twist (-((2 : ℕ) : ℤ)) T = d4Twist 1 T := by
        rw [← d4Twist_add_three]
        norm_num
      have : d4GfTwist T T⁻¹ 2 = T := if_pos (Or.inr ⟨rfl, rfl⟩)
      rw [this, hshift]

end GraphFieldConj

end CFSG.LieType.SeitzGeneration.ExcWideThree
