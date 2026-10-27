module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutFactsBeta
public import Certificates.Certificate24803
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabElem

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.EvenSporadicStandard.M22Std.TabCheck CFSG.EvenSporadicStandard.M22Std.OutCheck
  CFSG.Blueprint.NativeSporadic CFSG.Sporadic.Schreier CFSG.Certificates
  CFSG.EvenSporadicStandard.M23Std


theorem tab_betaAut_apply (x : Carrier .M22) : tab (betaAut x) = centConj (tab x) := by
  have h1 : rho betaAut * rho betaAut = 1 := by
    rw [← map_mul, betaAut_sq, map_one]
  have h2 : (rho betaAut)⁻¹ = rho betaAut := inv_eq_of_mul_eq_one_right h1
  have h3 : toPerm (betaAut x) = rho betaAut * toPerm x * rho betaAut := by
    rw [toPerm_apply_rho, h2]
  have h4 : tabP (rho betaAut) = betaTab := autTab_betaAut
  rw [tab, h3, tabP_mul, tabP_mul, h4]
  rfl

theorem conjAt_tabP (y σ σ' : Equiv.Perm (Fin 22)) :
    conjAt y (tabP σ) (tabP σ') = true ↔ y * σ' = σ * y := by
  simp only [conjAt, List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq,
    getD_tabP, Equiv.ext_iff, Equiv.Perm.mul_apply]
  constructor
  · intro h i
    exact Fin.ext (by simpa using h i)
  · intro h i
    simpa using congrArg Fin.val (h i)

theorem centOuterOK_spec :
    ∀ y ∈ enumeration m22Certificate, (centXs.all fun x => conjAt y x (centConj x)) = false := by
  intro y hy
  have h := Certificates.certificate24803
  unfold centOuterOK at h
  rw [List.all_eq_true] at h
  simpa using h y hy

theorem aut_cent {F : Subgroup (Carrier .M22)}
    (hF : ∀ x, x ∈ F ↔ x = 1 ∨ x ∈ invs16 1) (hND : NData (⊤ : Subgroup (Carrier .M22)) F) :
    ∀ α : MulAut (Carrier .M22), (∀ x ∈ F, α x = x) → α ∈ innerImage (Carrier .M22) F := by
  intro α hα
  by_cases hin : α ∈ innerImage (Carrier .M22) ⊤
  · obtain ⟨y, -, rfl⟩ := hin
    refine ⟨y, hND.F_self y (Subgroup.mem_top _) fun f hf => ?_, rfl⟩
    have h := hα f hf
    rw [MulAut.conj_apply] at h
    exact mul_inv_eq_iff_eq_mul.1 h
  · exfalso
    have hab : α * betaAut⁻¹ ∈ innerImage (Carrier .M22) ⊤ := by
      rw [Subgroup.mul_mem_iff_of_index_two index_innerImage_top, inv_mem_iff]
      exact iff_of_false hin betaAut_not_inner
    obtain ⟨y, -, hy⟩ := hab
    have hαeq : α = MulAut.conj y * betaAut := by rw [hy]; group
    have hQ : ValidSchreier m22Certificate := m22Certificate_check
    have hy' : toPerm y ∈ enumeration m22Certificate :=
      (mem_enumeration_iff m22Certificate hQ _).2
        (by rw [m22Certificate_originalSubgroup]; exact y.2)
    have h3 := centOuterOK_spec _ hy'
    have h4 : (centXs.all fun x => conjAt (toPerm y) x (centConj x)) = true := by
      rw [List.all_eq_true]
      intro x hx
      have hx' : x ∈ elemTabs 1 := List.mem_of_mem_take hx
      rw [← tab_invs16] at hx'
      obtain ⟨x0, hx0, rfl⟩ := List.mem_map.1 hx'
      have hfix := hα x0 ((hF x0).2 (Or.inr hx0))
      rw [hαeq, MulAut.mul_apply, MulAut.conj_apply] at hfix
      have h5 : y * betaAut x0 = x0 * y := mul_inv_eq_iff_eq_mul.1 hfix
      have h6 := congrArg toPerm h5
      rw [map_mul, map_mul] at h6
      rw [← tab_betaAut_apply]
      exact (conjAt_tabP _ _ _).2 h6
    rw [h4] at h3
    exact Bool.noConfusion h3

end CFSG.EvenSporadicStandard.M22Std
