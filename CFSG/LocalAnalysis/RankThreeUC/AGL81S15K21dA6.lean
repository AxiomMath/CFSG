module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dStmt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21a

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K21dA6Proof

theorem not_isSolvable_alt6 : ¬ Group.IsSolvable (alternatingGroup (Fin 6)) := by
  intro h
  refine Equiv.Perm.not_isSolvable (Fin 6) ?_ (Group.isSolvable_of_ker_le_range
    (alternatingGroup (Fin 6)).subtype (Equiv.Perm.sign (α := Fin 6)) fun σ hσ => ⟨⟨σ, hσ⟩, rfl⟩)
  rw [Cardinal.mk_fintype, ← Nat.card_eq_fintype_card]
  norm_num

end K21dA6Proof

theorem k21dGeomA6_holds : K21dGeomA6 := by
  intro S _ _ ⟨e⟩ U D E hU hUD hDs hED hE hE9 _
  exfalso
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card S = 360 := (Nat.card_congr e.toEquiv).trans K21aProof.card_alt6
  have hU8 : Nat.card U = 8 := by
    have h := hU.card_eq
    rw [Subgroup.card_top, hS, K21aProof.factorization_360] at h
    simpa using h
  have hD8 : 8 ∣ Nat.card D := hU8 ▸ Subgroup.card_dvd_of_le hUD
  have hD9 : 9 ∣ Nat.card D := hE9 ▸ Subgroup.card_dvd_of_le hED
  have h72 : 72 ∣ Nat.card D := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hD8 hD9
  have hD360 : Nat.card D ∣ 360 := hS ▸ Subgroup.card_subgroup_dvd_card D
  obtain ⟨k, hk⟩ := h72
  have hk5 : k ∣ 5 := by
    rw [hk] at hD360
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 72) (by simpa using hD360)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hk5 with h1 | h5
  · exact K21aProof.no72_of_mulEquiv e D (by omega)
  · have hDtop : D = ⊤ := by
      rw [← Subgroup.card_eq_iff_eq_top, hS]
      omega
    have hsolv : Group.IsSolvable S := by
      subst hDtop
      exact solvable_of_solvable_injective (f := (Subgroup.topEquiv (G := S)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := S)).symm.injective
    exact K21dA6Proof.not_isSolvable_alt6 (solvable_of_solvable_injective
      (f := e.symm.toMonoidHom) e.symm.injective)

end CFSG.LocalAnalysis.RankThreeUC.S15
