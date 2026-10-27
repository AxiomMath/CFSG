module

public import CFSG.ClassicalInvolution.RouteD.TypeCThreeBridgeFacts
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.ClassicalInvolution.RouteD.LieBridge

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open CFSG.LinearGroups (scalar_mem_statedSU_iff)
open scoped MatrixGroups

theorem sl3_center_pow_three {F : Type*} [Field F] {x : SL(3, F)}
    (hx : x ∈ Subgroup.center SL(3, F)) : x ^ 3 = 1 := by
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hx
  have h3 : r ^ 3 = 1 := by simpa using hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrx, ← map_pow, h3, map_one]
  rfl

theorem su3_center_pow_three {F : Type} [Field F] [Finite F] {p e : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ e) ^ 2) (hnq : (3, p ^ e) ≠ (3, 2))
    {x : SU (unitaryInvolution F p e) 3}
    (hx : x ∈ Subgroup.center (SU (unitaryInvolution F p e) 3)) : x ^ 3 = 1 := by
  set φ := equivStatedSU hF 3 with hφ
  have hxc : φ x ∈ Subgroup.center (StatedSU 3 (p ^ e) F) := by
    rw [← map_center_mulEquiv φ]
    exact ⟨x, hx, rfl⟩
  rw [(isQuasisimple_statedSU_of_card hF (by norm_num) hnq).2] at hxc
  obtain ⟨c, hc⟩ : ∃ c : Fˣ, Matrix.GeneralLinearGroup.scalar (Fin 3) c =
      ((φ x : StatedSU 3 (p ^ e) F) : GL (Fin 3) F) := hxc
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈ StatedSU 3 (p ^ e) F := by
    rw [hc]
    exact (φ x).2
  have hc3 : c ^ 3 = 1 := ((scalar_mem_statedSU_iff Fact.out hF (by norm_num) c).mp hmem).1
  have h1 : φ (x ^ 3) = 1 := by
    rw [map_pow]
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hc, ← map_pow, hc3, map_one]
    rfl
  exact φ.injective (by rw [h1, map_one])

theorem modelUniv_PSU_eq {n p f : ℕ} [hp : Fact p.Prime] (hf : 1 ≤ f) :
    CFSG.ClassicalInvolution.Generic.modelUniv .PSU n p f hp.out =
      ⟨SU (unitaryInvolution (GaloisField p (2 * f)) p f) n,
        CFSG.LieType.Universal.Unitary.rootDatum
          (CFSG.LieType.Universal.card_galoisField_two_mul p f hf) n⟩ := by
  simp only [CFSG.ClassicalInvolution.Generic.modelUniv, CFSG.LieType.Universal.lieUniversal, hf,
    ↓reduceDIte]

theorem centersExponentThree (p : ℕ) [Fact p.Prime] : CentersExponentThree p := by
  intro t e ht hadm
  rcases ht with rfl | rfl
  · intro x hx
    exact sl3_center_pow_three hx
  · have hf : 1 ≤ e := hadm.2.1
    have hF := CFSG.LieType.Universal.card_galoisField_two_mul p e hf
    intro x hx
    revert x
    rw [modelUniv_PSU_eq hf]
    intro x hx
    exact su3_center_pow_three hF hadm.2.2.2 hx

end CFSG.ClassicalInvolution.RouteD.LieBridge
