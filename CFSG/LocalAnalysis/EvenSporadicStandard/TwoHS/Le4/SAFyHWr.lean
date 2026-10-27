module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHAbs
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHWrCent

public section

namespace CFSG.EvenSporadicStandard.TwoHS

namespace SignWr

open Equiv Equiv.Perm Subgroup SignS9

variable {τ : Wr} {D S : Subgroup Wr} {eD : D ≃* DihedralGroup 4} {eS : S ≃* Perm (Fin 5)}

theorem tau_right_eq_one (h : LocalPair τ D S eD eS) : τ.right = 1 := by
  obtain ⟨hτ, he⟩ := h.tau_mem
  set x : D := eD.symm (DihedralGroup.r 1) with hx
  have hxx : x * x = ⟨τ, hτ⟩ := by
    apply eD.injective
    rw [map_mul, hx, MulEquiv.apply_symm_apply, DihedralGroup.r_mul_r, he]
    congr 1
  have hτxx : τ = (x : Wr) * (x : Wr) := (congrArg Subtype.val hxx).symm
  rw [hτxx, RegularWreathProduct.mul_right]
  rcases eq_one_or_eps (x : Wr).right with h1 | h1 <;> rw [h1] <;> simp [eps_mul_eps]

theorem wr_main_normal {a : Perm (Fin 5)} (ha : a ≠ 1) (ha' : sign a = 1)
    (h : LocalPair (mk a 1 1) D S eD eS) :
    (∀ d ∈ D, orderOf d = 4 → chi d = -1) ∧ (∀ s : S, sign (eS s) = -1 → chi s = -1) := by
  refine conclusion_of_retraction h (Fintype.card_fin 5) (secondCoord a ha) inSecond
    (inSecond_mem_centralizer a) ?_ ?_ chi ?_ ?_ ?_
  · intro u
    simp [secondCoord_apply, inSecond_apply]
  · intro u g hg
    rw [eq_inFirst_of_secondCoord_eq_one a ha hg, inSecond_apply, inFirst_apply, mk_mul_one,
      mk_mul_one]
    simp
  · intro u
    simp [inSecond_apply, chi_mk]
  · simp [chi_mk, ha']
  · intro g hg h4
    have hgc := eq_inFirst_of_secondCoord_eq_one a ha hg
    have hc4 : orderOf ((g : Wr).left 1) = 4 := by
      rw [← orderOf_injective inFirst inFirst_injective, ← hgc]
      exact h4
    rw [hgc, inFirst_apply, chi_mk,
      sign_eq_neg_one_of_orderOf_eq_four_of_card_le (by simp) hc4]
    simp

theorem wr_main (h : LocalPair τ D S eD eS) :
    (∀ d ∈ D, orderOf d = 4 → chi d = -1) ∧ (∀ s : S, sign (eS s) = -1 → chi s = -1) := by
  have hr := tau_right_eq_one h
  obtain ⟨a, b, rfl⟩ : ∃ a b, τ = mk a b 1 :=
    ⟨τ.left 1, τ.left eps, by have := mk_eta τ; rw [hr] at this; exact this.symm⟩
  have hsq := h.tau_sq
  rw [mk_mul_one, ← mk_one_one_one, mk_inj] at hsq
  obtain ⟨ha, hb, -⟩ := hsq
  rcases structure_of_card ha hb (tau_ne_one h) (card_centralizer h) with
    ⟨rfl, hb1, hsb⟩ | ⟨ha1, hsa, rfl⟩
  · have h2 := localPair_map h (MulAut.conj swapEl)
    have hτ2 : (MulAut.conj swapEl) (mk 1 b 1) = mk b 1 1 := by
      rw [MulAut.conj_apply, swapEl_conj]
    rw [hτ2] at h2
    have h4 := conclusion_of_map D S eS (MulAut.conj swapEl) chi (wr_main_normal hb1 hsb h2)
    simpa only [MulAut.conj_apply, chi_conj] using h4
  · exact wr_main_normal ha1 hsa h

end SignWr

end CFSG.EvenSporadicStandard.TwoHS
