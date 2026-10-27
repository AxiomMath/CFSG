module

public import CFSG.ClassicalInvolution.Asc77.AscT7MA
public import CFSG.ClassicalInvolution.Asc77.AscT7ME
import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4Model

public section

namespace CFSG.ClassicalInvolution.Asc77

set_option linter.unusedSectionVars false

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.ModelFacts.UnitaryAut
  CFSG.ClassicalInvolution.Phan

variable {p : ℕ} [Fact p.Prime] {e : ℕ}


theorem no_norm_one_sqrt_neg_one {K : Type} [Field K] (hK2 : (2 : K) ≠ 0) (q : ℕ)
    (hq : q % 4 = 1) (ι : K) (h1 : ι * ι = -1) (h2 : ι ^ q * ι = 1) : False := by
  obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 1 := ⟨q / 4, by omega⟩
  have h4 : ι ^ 4 = 1 := by
    have : ι ^ 4 = (ι * ι) * (ι * ι) := by ring
    rw [this, h1]
    norm_num
  have h5 : ι ^ q = ι := by
    rw [hk, pow_succ, pow_mul, h4, one_pow, one_mul]
  rw [h5, h1] at h2
  apply hK2
  linear_combination -h2

theorem twinSqAlpha_psu4_of_one (hp2 : p ≠ 2) (hq5 : 5 ≤ p ^ e) (hq : p ^ e % 4 = 1)
    (hadm : StatedLieAdmissible .PSU 4 p e) : TwinSqAlpha p e .PSU 4 := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq hq5
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have : Group.IsPerfect (modelUniv .PSU 4 p e Fact.out).K :=
    Group.isPerfect_def.2
      (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero .PSU 4 p e Fact.out trivial hadm).1.1
  have h2K : (2 : GaloisField p (2 * e)) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField (2 * e) hp2
  refine twinSqAlphaOn_of_autSq (t := .PSU) (modelUniv .PSU 4 p e Fact.out)
    ((QuotientGroup.mk' (Subgroup.center (Su (GaloisField p (2 * e)) p e 4))).comp
      φ.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp φ.surjective) ?_
    (fund_noncentral_modelUniv trivial hadm (by simp)) ?_
  · ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ x) : Su (GaloisField p (2 * e)) p e 4 ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ x
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc σ hσ hσ' hσ2
    exfalso
    have hne' : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
      hne (Subgroup.map_injective φ.injective h)
    have hc' : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
      have := (CFSG.ClassicalInvolution.ModelFacts.Orth15.mulEquiv_mem_center_iff φ (x' * x⁻¹)).mpr
        hc
      rwa [map_mul, map_inv] at this
    obtain ⟨ι, hι1, hι2⟩ := OuterU4.psu4_autSq hK hp2 hq5 ((hφ R).mp hR) ((hφ R').mp hR') hne'
      ⟨x, hxR, rfl⟩ (by rw [← map_mul, hx2, map_one])
      (fun h => hx1 (φ.injective (h.trans (map_one φ).symm))) ⟨x', hx'R', rfl⟩
      (by rw [← map_mul, hx'2, map_one])
      (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc' σ
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ r hr)
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ' r hr)
      (by rw [hσ2]; rfl)
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hι2
    exact no_norm_one_sqrt_neg_one h2K (p ^ e) hq ι hι1 hι2

end CFSG.ClassicalInvolution.Asc77
