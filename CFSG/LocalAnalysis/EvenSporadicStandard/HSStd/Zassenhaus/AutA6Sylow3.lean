module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Three

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut
  AutA6Three

namespace AutA6Sylow3

theorem fix_check : ord3P.all (fun a => Core.autL.all fun y =>
    !((Core.cpslList a).all fun c => Core.cmul y c == Core.cmul c y) ||
      (Core.cpslList a).contains y) = true := by
  decide +kernel

end AutA6Sylow3

theorem mem_inner_of_fix_centralizer {x : alternatingGroup (Fin 6)} (hx : orderOf x = 3)
    (α : MulAut (alternatingGroup (Fin 6)))
    (hα : ∀ a ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6))), α a = a) :
    ∃ b ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6))), α = MulAut.conj b := by
  set w : ↥A6Models.psl29 := psiEquiv.symm x with hw
  set y : AutA6 := thetaEquiv.symm α with hy
  have hαy : thetaEquiv y = α := MulEquiv.apply_symm_apply _ _
  have hall : (Core.cpslList (code (w : P10))).all
      (fun c => Core.cmul (cd y) c == Core.cmul c (cd y)) = true := by
    rw [List.all_eq_true]
    intro c hc
    unfold Core.cpslList at hc
    rw [List.mem_filter] at hc
    obtain ⟨hc1, hc2⟩ := hc
    obtain ⟨p, hp, rfl⟩ := exists_psl29_of_code hc1
    simp only [beq_iff_eq] at hc2 ⊢
    have hpw : p * (w : P10) = (w : P10) * p :=
      code_injective (by rw [code_mul, code_mul]; exact hc2)
    set a : alternatingGroup (Fin 6) := psiEquiv ⟨p, hp⟩ with ha
    have haC : a ∈ Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 6))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      apply psiEquiv.symm.injective
      rw [map_mul, map_mul, ha, MulEquiv.symm_apply_apply]
      exact Subtype.ext hpw.symm
    have hfix := hα a haC
    have hpt : thetaEquiv (⟨p, psl29_le_autA6 hp⟩ : AutA6) = MulAut.conj a :=
      thetaEquiv_mk ⟨p, hp⟩
    have h1 : thetaEquiv (y * (⟨p, psl29_le_autA6 hp⟩ : AutA6) * y⁻¹) =
        thetaEquiv (⟨p, psl29_le_autA6 hp⟩ : AutA6) := by
      rw [map_mul, map_mul, map_inv, hαy, hpt, conj_thetaEquiv_apply, hfix]
    have h2 := thetaEquiv.injective h1
    rw [mul_inv_eq_iff_eq_mul] at h2
    have h3 := congrArg cd h2
    rw [cd_mul, cd_mul] at h3
    exact h3
  have hmem := List.all_eq_true.mp AutA6Sylow3.fix_check _ (code_mem_ord3P_of_orderOf hx)
  have h2 := List.all_eq_true.mp hmem (cd y) (cd_mem_autL y)
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · rw [hall] at h2
    exact absurd h2 (by simp)
  rw [List.contains_iff_mem] at h2
  unfold Core.cpslList at h2
  rw [List.mem_filter] at h2
  obtain ⟨hy1, hy2⟩ := h2
  simp only [beq_iff_eq] at hy2
  have hyP : (y : P10) ∈ A6Models.psl29 := (mem_psl29_iff _).2 hy1
  have hyw : (y : P10) * (w : P10) = (w : P10) * (y : P10) :=
    code_injective (by rw [code_mul, code_mul]; exact hy2)
  refine ⟨psiEquiv ⟨(y : P10), hyP⟩, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    apply psiEquiv.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply]
    exact Subtype.ext hyw.symm
  · rw [← hαy]
    exact thetaEquiv_psl y hyP

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
