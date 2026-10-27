module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterU4
public import CFSG.ClassicalInvolution.ModelFacts.Orth15OuterGen

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Asc77 CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.UnitaryAut CFSG.ClassicalInvolution.Phan

theorem mulEquiv_mem_center_iff {G H : Type} [Group G] [Group H] (e : G ≃* H) (x : G) :
    e x ∈ Subgroup.center H ↔ x ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h g
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e g)
  · intro h y
    obtain ⟨g, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, h g]

theorem twinOuterAlpha_psu4 {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {e : ℕ} (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .PSU 4 p e) : TwinOuterAlpha p e .PSU 4 := by
  have hf : 1 ≤ e := hadm.2.1
  have : NeZero (2 * e) := ⟨by omega⟩
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 := card_galoisField_two_mul_eq hq
  obtain ⟨φ, hφ⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have : Group.IsPerfect (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out).K :=
    Group.isPerfect_def.2 (modelClauseZero .PSU 4 p e Fact.out trivial hadm).1.1
  refine twinOuterAlphaOn_of_autVac (t := .PSU)
    (CFSG.ClassicalInvolution.Generic.modelUniv .PSU 4 p e Fact.out)
    ((QuotientGroup.mk' (Subgroup.center (Su (GaloisField p (2 * e)) p e 4))).comp
      φ.toMonoidHom)
    ((QuotientGroup.mk'_surjective _).comp φ.surjective) ?_ ?_
  · ext x
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk (φ x) : Su (GaloisField p (2 * e)) p e 4 ⧸ _) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact mulEquiv_mem_center_iff φ x
  · intro R R' x x' hR hR' hne _ hxR hx2 hx1 hx'R' hx'2 hx'1 hc σ hσ hσ' hσ4
    have hne' : R.map φ.toMonoidHom ≠ R'.map φ.toMonoidHom := fun h =>
      hne (Subgroup.map_injective φ.injective h)
    have hc' : φ x' * (φ x)⁻¹ ∈ Subgroup.center (Su (GaloisField p (2 * e)) p e 4) := by
      have := (mulEquiv_mem_center_iff φ (x' * x⁻¹)).mpr hc
      rwa [map_mul, map_inv] at this
    exact OuterU4.psu4_autVac hK hp2 hq ((hφ R).mp hR) ((hφ R').mp hR') hne' ⟨x, hxR, rfl⟩
      (by rw [← map_mul, hx2, map_one]) (fun h => hx1 (φ.injective (h.trans (map_one φ).symm)))
      ⟨x', hx'R', rfl⟩ (by rw [← map_mul, hx'2, map_one])
      (fun h => hx'1 (φ.injective (h.trans (map_one φ).symm))) hc' σ
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ r hr)
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hσ' r hr)
      hσ4

end CFSG.ClassicalInvolution.ModelFacts.Orth15
