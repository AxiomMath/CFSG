module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4IBProj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open QuadraticMap

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem sec4I_exists_lift_pow7 {y : ProjOrth Q} (hy : y ^ 7 = 1) :
    ∃ g : OGroup Q, toProj Q g = y ∧ g ^ 7 = 1 := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (piGroup Q) y
  have hg : g ^ 7 ∈ piGroup Q := by
    apply (QuotientGroup.eq_one_iff (N := piGroup Q) (g ^ 7)).mp
    change toProj Q (g ^ 7) = 1
    rw [map_pow]
    exact hy
  rcases mem_piGroup_iff.mp hg with h1 | h1
  · exact ⟨g, rfl, h1⟩
  · have h2 : piOrth Q ^ 2 = 1 := by rw [pow_two, piOrth_mul_self]
    have hpi7 : piOrth Q ^ 7 = piOrth Q := by
      calc piOrth Q ^ 7 = (piOrth Q ^ 2) ^ 3 * piOrth Q := by group
        _ = piOrth Q := by rw [h2, one_pow, one_mul]
    have hc : Commute (piOrth Q) g :=
      (Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) g).symm
    refine ⟨piOrth Q * g, ?_, ?_⟩
    · change toProj Q (piOrth Q * g) = toProj Q g
      rw [map_mul, toProj_piOrth, one_mul]
    · rw [hc.mul_pow, hpi7, h1, piOrth_mul_self]

theorem sec4I_comm_T_of_comm_psi (hQ : Q.Nondegenerate) (fr : Sec4IFrame Q)
    (v : Fin 7 → ZMod 2) {g : OGroup Q}
    (h : toProj Q g * sec4IPsi fr v = sec4IPsi fr v * toProj Q g) :
    g * sec4IT fr v = sec4IT fr v * g := by
  have htt : sec4IT fr v * sec4IT fr v = 1 := sec4IT_mul_self fr v
  have hfin : Module.finrank (ZMod 3) V = 7 := by
    rw [Module.finrank_eq_card_basis fr.b]
    simp
  have hconj : toProj Q (g * sec4IT fr v * g⁻¹) = toProj Q (sec4IT fr v) := by
    have h' : toProj Q g * toProj Q (sec4IT fr v) = toProj Q (sec4IT fr v) * toProj Q g := h
    rw [map_mul, map_mul, map_inv, h']
    group
  have hmem : (sec4IT fr v)⁻¹ * (g * sec4IT fr v * g⁻¹) ∈ piGroup Q := by
    apply (QuotientGroup.eq_one_iff (N := piGroup Q) _).mp
    change toProj Q ((sec4IT fr v)⁻¹ * (g * sec4IT fr v * g⁻¹)) = 1
    rw [map_mul, map_inv, hconj, inv_mul_cancel]
  rcases mem_piGroup_iff.mp hmem with h1 | h1
  · have h2 : g * sec4IT fr v * g⁻¹ = sec4IT fr v := (inv_mul_eq_one.mp h1).symm
    calc g * sec4IT fr v = (g * sec4IT fr v * g⁻¹) * g := by group
      _ = sec4IT fr v * g := by rw [h2]
  · exfalso
    have h2 : g * sec4IT fr v * g⁻¹ = piOrth Q * sec4IT fr v := by
      have h3 : g * sec4IT fr v * g⁻¹ = sec4IT fr v * piOrth Q := by
        calc g * sec4IT fr v * g⁻¹
            = sec4IT fr v * ((sec4IT fr v)⁻¹ * (g * sec4IT fr v * g⁻¹)) := by group
          _ = sec4IT fr v * piOrth Q := by rw [h1]
      rw [h3]
      exact Subgroup.mem_center_iff.mp (piOrth_mem_center (Q := Q)) (sec4IT fr v)
    have htype := invType_conj hQ htt g
    rw [h2, invType_piOrth_mul hQ htt] at htype
    have h4 : Module.finrank (ZMod 3) V - invDim (sec4IT fr v) = invDim (sec4IT fr v) :=
      congrArg Prod.fst htype
    have h5 := invDim_le (sec4IT fr v)
    omega

end CFSG.OddStandard.SmallF3.Omega
