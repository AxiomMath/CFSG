module

public import CFSG.HardMathSupport.Lang.D4Three.PowNormalForm
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.NormalForm
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Exc.Char3D4

public noncomputable section

namespace CFSG.ComponentClassification.OuterAutomorphisms

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.HardMathSupport.Solomon.Coordinator.LieComp
open CFSG.HardMathSupport.Lang.E6Descent

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [Finite K]

theorem fieldPart_eq_one_of_mem_innAutDerived
    {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ innAutDerived (adjointGroup Tag.D4 K)) :
    fieldPart β = 1 := by
  have hinner : inner (adjointGroup Tag.D4 K) ≤ (fieldPart :
      MulAut (adjointGroup Tag.D4 K) →* (K ≃+* K)).ker := by
    rintro _ ⟨g, rfl⟩
    exact fieldPart_conj g
  have hcomm : commutator (MulAut (adjointGroup Tag.D4 K)) ≤ (fieldPart :
      MulAut (adjointGroup Tag.D4 K) →* (K ≃+* K)).ker :=
    fun η hη => fieldPart_eq_one_of_mem_commutator hη
  exact MonoidHom.mem_ker.1 (sup_le hinner hcomm hβ)

theorem exists_conj_eq_of_mem_innAutDerived_D4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) {β : MulAut (adjointGroup Tag.D4 K)}
    (hβ : β ∈ innAutDerived (adjointGroup Tag.D4 K)) (hβp : β ^ p = 1) :
    ∃ h : adjointGroup Tag.D4 K, β = MulAut.conj h := by
  obtain ⟨g, a, σ, hβeq⟩ := exists_normal_form_of_pow_eq_one β hp hp2 hp3 hβp
  have hσ : σ = 1 := by
    have h1 := fieldPart_eq_one_of_mem_innAutDerived hβ
    have hN : fieldPart (exactNormalAut Tag.D4 K a σ 0) = σ := by
      have h := fieldPart_normalForm a σ 0
      rw [d4Graph_zero, mul_one] at h
      exact h
    have hmul : fieldPart (MulAut.conj g * exactNormalAut Tag.D4 K a σ 0) =
        fieldPart (MulAut.conj g) * fieldPart (exactNormalAut Tag.D4 K a σ 0) :=
      map_mul _ _ _
    rw [hβeq, hmul, fieldPart_conj, hN, one_mul] at h1
    exact h1
  rw [hσ] at hβeq
  obtain ⟨h, hh⟩ := exists_inner_sq_conj_mul_exactNormalAut_one g a
  have hodd : 2 ∣ p + 1 := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    exact ⟨k + 1, by omega⟩
  have htwo : 2 * ((p + 1) / 2) = p + 1 := Nat.mul_div_cancel' hodd
  have hβ' : β = (β ^ 2) ^ ((p + 1) / 2) := by
    calc β = β ^ (p + 1) := by rw [pow_succ, hβp, one_mul]
      _ = β ^ (2 * ((p + 1) / 2)) := by rw [htwo]
      _ = (β ^ 2) ^ ((p + 1) / 2) := pow_mul β 2 _
  refine ⟨h ^ ((p + 1) / 2), ?_⟩
  calc β = (β ^ 2) ^ ((p + 1) / 2) := hβ'
    _ = (MulAut.conj h) ^ ((p + 1) / 2) := by rw [hβeq, hh]
    _ = MulAut.conj (h ^ ((p + 1) / 2)) := (map_pow (MulAut.conj : adjointGroup Tag.D4 K →*
        MulAut (adjointGroup Tag.D4 K)) h _).symm

theorem innAutDerived_D4_three_cases {β : MulAut (adjointGroup Tag.D4 K)}
    (hβ : β ∈ innAutDerived (adjointGroup Tag.D4 K)) (hβ3 : β ^ 3 = 1) :
    (∃ h : adjointGroup Tag.D4 K, β = MulAut.conj h) ∨
      ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (ε : ℕ),
        (ε = 1 ∨ ε = 2) ∧
          β = MulAut.conj g * (exactNormalAut Tag.D4 K a 1 0 * d4Graph K ε) := by
  obtain ⟨g, a, σ, ε, hε3, -, hβeq⟩ := exists_cube_normal_form_sigma β hβ3
  have hσ : σ = 1 := by
    have h1 := fieldPart_eq_one_of_mem_innAutDerived hβ
    have hmul : fieldPart (MulAut.conj g *
        (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε)) =
        fieldPart (MulAut.conj g) *
          fieldPart (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) :=
      map_mul _ _ _
    rw [hβeq, hmul, fieldPart_conj, fieldPart_normalForm, one_mul] at h1
    exact h1
  rw [hσ] at hβeq
  interval_cases ε
  · left
    have hα : (MulAut.conj g * exactNormalAut Tag.D4 K a 1 0) ^ 3 = 1 := by
      have h := hβ3
      rw [hβeq, d4Graph_zero, mul_one] at h
      exact h
    obtain ⟨h, hh⟩ := d4_inner_of_diag_char_free g a hα
    exact ⟨h, by rw [hβeq, d4Graph_zero, mul_one, hh]⟩
  · exact Or.inr ⟨g, a, 1, Or.inl rfl, hβeq⟩
  · exact Or.inr ⟨g, a, 2, Or.inr rfl, hβeq⟩

end CFSG.ComponentClassification.OuterAutomorphisms
