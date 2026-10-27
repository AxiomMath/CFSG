module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5QMirror
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5Base

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.OddStandard.Solomon75.AhatData

open scoped commutatorElement

namespace PairCtx

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z s : X} {A A' : Subgroup X}
  {M : AhatModel X n A} {M' : AhatModel X n A'}

theorem rcore_of_four [NeZero n] (h : PairCtx X n z s A A' M M') (hn11 : n ≤ 11)
    (hM : M.permX s = sig0 n) (hM' : M'.permX z = sig0 n) (hfc : FCAll n) : h.RCore := by
  obtain ⟨hfc2, hfcr, hfcb, hfco2⟩ := hfc
  obtain ⟨hσ2, hσ8, hσA⟩ := sig0_spec n h.hn hn11
  have hsN : s ∈ normalizer (A : Set X) := h.hNz h.s_mem_C
  have hσ8s : (M.permX s).support.card = 8 := by rw [hM]; exact hσ8
  have hσ8z : (M'.permX z).support.card = 8 := by rw [hM']; exact hσ8
  have hfc2' : FC2 n (M.permX s) := by rw [hM]; exact hfc2
  have hfcr' : FCR n (M.permX s) := by rw [hM]; exact hfcr
  have hfcb' : FCB n (M.permX s) := by rw [hM]; exact hfcb
  have hfco2' : FCO2 n (M'.permX z) := by rw [hM']; exact hfco2
  have hσσ : M.permX s * M.permX s = 1 := by rw [hM]; exact hσ2
  have hσord : orderOf (M.permX s) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime (by rw [sq]; exact hσσ) ?_
    intro h1
    rw [h1] at hσ8s
    simp at hσ8s
  intro x hx hxj
  obtain ⟨j, hj⟩ := hxj
  by_contra hcon
  push Not at hcon
  obtain ⟨hcon1, hcon2⟩ := hcon
  have hxz : x ∈ centralizer ({z} : Set X) := (h.mem_R_iff.1 hx).1
  have hxs : x ∈ centralizer ({s} : Set X) := (h.mem_R_iff.1 hx).2.1
  have hxN : x ∈ normalizer (A : Set X) := h.hNz hxz
  have hxc : M.permX x ∈ centralizer ({M.permX s} : Set (Perm (Fin n))) := by
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have : x * s = s * x := Subgroup.mem_centralizer_singleton_iff.1 hxs
    rw [← M.permX_mul h.hn hxN hsN, ← M.permX_mul h.hn hsN hxN, this]
  have hx2 : (M.permX x) ^ (2 ^ j) = 1 := by
    rw [← h.permX_pow hxN, hj, M.permX_one h.hn]
  have hx8 : M.permX x ^ 8 = 1 := hfc2' _ hxc ⟨j, hx2⟩
  have hxnot : M.permX x ∉ zpowers (M.permX s) := by
    intro hz
    rcases zpowers_eq_of_orderOf_two hσord _ hz with h1 | h1
    · exact hcon1 h1
    · exact hcon2 h1
  rcases hfcr' _ hxc hx8 hxnot with ⟨r, hr, hr2, hr1, hr4⟩ | ⟨S, hS, hgood⟩
  ·
    have hcl : Subgroup.closure (conjSet (H0 (M.permX s)) (M.permX x) ∪ {M.permX s}) ≤ h.Rbar := by
      rw [Subgroup.closure_le]
      rintro t (⟨g, hg, rfl⟩ | ht)
      · obtain ⟨u, hu, hsu, hug⟩ := h.H0_lift hσ8s g hg
        have hus : u ∈ centralizer ({s} : Set X) :=
          Subgroup.mem_centralizer_singleton_iff.2 hsu.symm
        refine h.mem_Rbar_iff.2 ⟨u * x * u⁻¹, h.R_conj (h.hAz hu) hus hx, ?_⟩
        rw [M.permX_conj h.hn (h.hNz (h.hAz hu)) hxN, hug]
      · rw [Set.mem_singleton_iff.1 ht]
        exact h.mem_Rbar_iff.2 ⟨s, h.s_mem_R, rfl⟩
    have := h.fixCount_le_of_involution_Rbar (hcl hr) hr2 hr1
    omega
  · have hΓ : ∀ y ∈ h.Y, M.permX y ∈ {g | g ∈ centralizer ({M.permX s} : Set (Perm (Fin n))) ∧
        ∀ t ∈ S, ⁅g, t⁆ ∈ Bn n} := fun y hy =>
      h.permX_Y_mem_Gamma hσ8s hfcb' hx hj hS hy
    rcases hgood with ⟨hn10, h8⟩ | ⟨hn11', hc⟩
    · exact h.false_of_small hn10 hσ8z hfco2' fun y hy => h8 _ (hΓ y hy)
    · refine h.false_of_eleven (by omega) hσ8z hfco2' fun y₁ hy₁ y₂ hy₂ y₃ hy₃ y₄ hy₄ => ?_
      exact hc _ (hΓ y₁ hy₁) _ (hΓ y₂ hy₂) _ (hΓ y₃ hy₃) _ (hΓ y₄ hy₄)

end PairCtx

end CFSG.OddStandard.Solomon75
