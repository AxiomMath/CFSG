module

public import CFSG.GH74.Uniqueness.Bender.UnitaryAut
import CFSG.GH74.Uniqueness.Bender.SuzukiAut

public section

namespace CFSG.GH74.Uniqueness.Bender

variable {K : Type} [Group K] [Finite K]

theorem BenderType.exists_mem_eq_conj_of_sq_eq_conj {n i e : ℕ}
    (h : BenderType K n i e) (S : Sylow 2 K) {g : MulAut K}
    (hg : g ∈ autCentralizer (rootCenter (S : Subgroup K))) {z : K}
    (hz : z ∈ rootCenter (S : Subgroup K)) (hz1 : z ≠ 1) (hgz : g ^ 2 = MulAut.conj z) :
    ∃ s ∈ (S : Subgroup K), g = MulAut.conj s := by
  by_cases hi : i = 3
  · subst hi
    obtain ⟨hn, ⟨e₁⟩⟩ : 2 ≤ n ∧ Nonempty (K ≃* CFSG.Theory.Comparator.PSU3Model n) := by
      cases h with
      | unitary n hn e => exact ⟨hn, ⟨e⟩⟩
    obtain ⟨E, hE, hF, J, hJ, hcard, hfixed, ⟨e'⟩⟩ := exists_psu3_concrete hn
    obtain ⟨t, hc⟩ := h.exists_benderCore S
    obtain ⟨-, -, -, -, hsq, -⟩ :=
      CFSG.ProperTwoGeneratedCore.RootCenter.even_unitary_root_center_automorphisms_of_mulEquiv
        J n hn hcard hfixed hJ (e₁.trans e') S (rootCenter (S : Subgroup K))
        hc.omega₁_map_eq_rootCenter.symm
    rw [h.rootCenterAut_eq_autCentralizer S] at hsq
    rcases hsq g hg ⟨z, hz, hgz.symm⟩ with ⟨s, hs, hsg⟩ | h1
    · exact ⟨s, hs, hsg.symm⟩
    · exfalso
      apply hz1
      have hc1 : MulAut.conj z = 1 := hgz.symm.trans h1
      have hzZ : z ∈ Subgroup.center K := Subgroup.mem_center_iff.mpr fun x => by
        have hx := congrArg (fun φ : MulAut K => φ x) hc1
        simp only [MulAut.conj_apply, MulAut.one_apply] at hx
        calc x * z = z * x * z⁻¹ * z := by rw [hx]
          _ = z * x := by group
      rw [h.center_eq_bot, Subgroup.mem_bot] at hzZ
      exact hzZ
  · exact h.exists_eq_conj_of_centralizes_center_of_ne_three hi S g (mem_autCentralizer_iff.mp hg)

end CFSG.GH74.Uniqueness.Bender
