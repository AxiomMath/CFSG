module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812Perm

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812

open Equiv Equiv.Perm Subgroup

private theorem isThreeCycle_c3 : IsThreeCycle c3 := by
  have h : c3 = swap 9 8 * swap 9 10 := by
    rw [c3, swap_comm 9 8]
  rw [h]
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private theorem cycleType_eq_three_of_mem_zpowers_c3 {w : Perm (Fin 11)} (hw : w ∈ zpowers c3)
    (hw1 : w ≠ 1) : w.cycleType = {3} := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  have hmod : c3 ^ k = c3 ^ (k % 3) := by
    have := zpow_mod_orderOf c3 k
    rw [orderOf_c3] at this
    simpa using this.symm
  rw [hmod] at hw1 ⊢
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · rw [h] at hw1
    exact (hw1 (zpow_zero c3)).elim
  · rw [h, zpow_one]
    exact isThreeCycle_c3.cycleType
  · rw [h, zpow_ofNat, pow_two]
    exact isThreeCycle_c3.isThreeCycle_sq.cycleType

theorem cycleType_eq_three_of_normalized {T V : Subgroup (Perm (Fin 11))}
    (hTA : T ≤ alternatingGroup (Fin 11)) (hT : Nat.card ↥T = 2 ^ 7)
    (hV : IsPGroup 3 ↥V) (hVA : V ≤ alternatingGroup (Fin 11)) (h1 : V ≠ ⊥)
    (hn : T ≤ normalizer (V : Set (Perm (Fin 11)))) :
    ∀ v ∈ V, v ≠ 1 → v.cycleType = {3} := by
  obtain ⟨T₀, hT₀⟩ := exists_sylData
  have hT₀A : T₀ ≤ alternatingGroup (Fin 11) := fun t ht =>
    Equiv.Perm.mem_alternatingGroup.2 (hT₀.even t ht)
  obtain ⟨c, hc⟩ := exists_conj_of_card hT₀A hTA hT₀.card hT
  have e1 := conjBy_eq_zpowers hT₀ c hc hV hVA h1 hn
  intro v hv hv1
  have hm : c⁻¹ * v * c ∈ conjBy c V := mem_conjBy.2 (by simpa [mul_assoc] using hv)
  rw [e1] at hm
  have hne : c⁻¹ * v * c ≠ 1 := by
    intro h
    apply hv1
    have := congrArg (fun z => c * z * c⁻¹) h
    simpa [mul_assoc] using this
  have hcyc : (c⁻¹ * v * c).cycleType = v.cycleType := by
    simpa using cycleType_conj (σ := v) (τ := c⁻¹)
  rw [← hcyc]
  exact cycleType_eq_three_of_mem_zpowers_c3 hm hne

end CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812
