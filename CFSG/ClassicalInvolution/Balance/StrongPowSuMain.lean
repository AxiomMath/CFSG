module

public import CFSG.ClassicalInvolution.Balance.StrongPowSu
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalancePow

public section

namespace CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Phan (Su)

theorem strongLocalTwoBalanceToralPowOn_PSU_two :
    StrongLocalTwoBalanceToralPowOn 2 .PSU (fun _ _ _ => True) := by
  intro n p e hp _ hfund hadm hp2 h5 X _ _ ψ hker hnorm F hcard hF2 hfaith htoral
  have : Fact p.Prime := ⟨hp⟩
  have hn : 3 ≤ n := hadm.2.2.1
  obtain ⟨e', -⟩ := CFSG.ClassicalInvolution.RouteD.psu_model_equiv hp2 hadm
  have hK : Nat.card (GaloisField p (2 * e)) = (p ^ e) ^ 2 :=
    CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.card_galoisField_two_mul_eq h5
  set ψ' : Su (GaloisField p (2 * e)) p e n →* X := ψ.comp e'.symm.toMonoidHom with hψ'
  have hker' : ψ'.ker ≤ Subgroup.center (Su (GaloisField p (2 * e)) p e n) := by
    intro x hx
    have h1 : e'.symm x ∈ Subgroup.center (modelUniv .PSU n p e hp).K :=
      hker (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hx))
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro y
    apply e'.symm.injective
    rw [map_mul, map_mul]
    exact h1 (e'.symm y)
  have hrange : ψ'.range = ψ.range := by
    rw [hψ', MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e'.symm.surjective,
      ← MonoidHom.range_eq_map]
  have hnorm' : ψ'.range.Normal := by
    rw [hrange]
    exact hnorm
  obtain ⟨P, hP, hact⟩ := htoral
  have hact' : ∀ f' ∈ F, ∃ x ∈ P.map e'.toMonoidHom, x * x = 1 ∧
      ∀ y, f' * ψ' y * f'⁻¹ = ψ' (x * y * x⁻¹) := by
    intro f' hf'
    obtain ⟨x, hxP, hx2, hxa⟩ := hact f' hf'
    refine ⟨e' x, ⟨x, hxP, rfl⟩, ?_, fun y => ?_⟩
    · rw [← map_mul, ← pow_two, hx2, map_one]
    · have := hxa (e'.symm y)
      simp only [hψ', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      rw [this]
      congr 1
      simp
  have hP' : ∀ x ∈ P.map e'.toMonoidHom, ∀ y ∈ P.map e'.toMonoidHom, x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hP x hx y hy]
  have := strongConclusion_su hK hp2 h5 hn ψ' hker' hnorm' hcard hF2 (P.map e'.toMonoidHom) hP'
    hact'
  rwa [hrange] at this

end CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
