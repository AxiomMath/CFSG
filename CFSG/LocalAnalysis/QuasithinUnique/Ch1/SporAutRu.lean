module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutLocal
public import CFSG.Sporadic.Schreier.RuOuter
public import CFSG.Sporadic.Schreier.RuIso

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.Sporadic.RuSchreier

theorem ru_fixing_inner
    (α : MulAut ruP) (hα : ∀ s ∈ (ruSylow : Subgroup ruP), α s = s) :
    ∃ c : ruP, ∀ x, α x = c * x * c⁻¹ := by
  refine SporAut.exists_conj_of_local_pair ruSylow (ruC.subgroupOf ruP) ruCP_eq
    (ruK.subgroupOf ruP) (Subgroup.subgroupOf_mono _ ruK_leS) (ruN.subgroupOf ruP) ruNP_eq
    (ruJ.subgroupOf ruP) (isPGroup_ruJ.of_equiv (Subgroup.subgroupOfEquivOfLe ruJ_le).symm)
    (Subgroup.subgroupOf_mono _ ruJ_leS) (Subgroup.subgroupOf_mono _ ruJ_leC) ?_ ?_ ?_ ?_ ?_ α hα
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.subgroupOf_mono _ ruJ_leC)]
    intro h k hh hk
    rw [mem_subgroupOf_iff] at hh hk ⊢
    exact (Subgroup.normal_subgroupOf_iff ruJ_leC).1 ruJ_normal h k hh hk
  · intro x hx
    obtain ⟨hxC, hxJ⟩ := Subgroup.mem_inf.1 hx
    rw [centralizer_subgroupOf ruJ_le, mem_subgroupOf_iff] at hxJ
    rw [mem_subgroupOf_iff] at hxC ⊢
    exact ruCentralizer_J ⟨hxC, hxJ⟩
  · intro x hx
    obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.1 hx
    rw [centralizer_subgroupOf ruK_le, mem_subgroupOf_iff] at hxK
    rw [mem_subgroupOf_iff] at hxN ⊢
    exact ruCentralizer_K ⟨hxN, hxK⟩
  · rw [← Subgroup.subgroupOf_sup ruC_le ruN_le, ← ruP_eq_sup, Subgroup.subgroupOf_self]
  · exact Subgroup.subgroupOf_mono _ ruS_leN

theorem ruAutInner
    (K : Type) [Group K] [Finite K] (hK : Nonempty (K ≃* NativeSporadic.Ru))
    (β : K ≃* K) (hP : ∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) : IsInnerAut β := by
  obtain ⟨e⟩ := hK
  exact SporAut.isInnerAut_of_fixing_sylow (e.trans ruEquivP) ruSylow
    (fun α hα => ru_fixing_inner α hα) β hP

end CFSG.QuasithinUnique.Ch1
