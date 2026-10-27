module

public import CFSG.GH74.Uniqueness.Section128Count
public import CFSG.GH74.Uniqueness.Section128Arith

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open CFSG.ShultStronglyClosedTI.InvolutionCounting

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.lemma128
    (S : ZDSetup X Z M) (h124 : Lemma124Stmt Z M) (h127 : Lemma127Stmt Z M) :
    Lemma128Stmt Z M := by
  intro c n i h u huD hu2 m j e hB hq
  have huM : u ∈ M := (Subgroup.mem_inf.mp huD).1
  obtain ⟨hΩu, hCu⟩ := S.ncard_omegaFix_and_card_centralizer hu2 huM hB
  refine ⟨hΩu, ?_⟩
  have hz2 : orderOf c.z = 2 := S.invariant.1 c.z c.hz
  have huz : ¬ IsConj u c.z := fun hc =>
    Sec128.not_mem_Z S c.htM huD (S.invariant.isConj_mem c.hz hc)
  have hthom := card_eq_of_thompsonPairCount_support hu2 hz2 huz
    (fun w hw hwu hwz => Sec128.thompsonPairCount_eq_zero S h h127 huD hu2 hw hwu hwz)
  have hau : thompsonPairCount u c.z u =
      (2 ^ m - 1) * ((2 ^ m) ^ j + 1) * ((2 ^ m) ^ j * (2 ^ m - 1) + 1) := by
    rw [Sec128.thompsonPairCount_self S h h127 huD hu2 hB, hB.ncard_oddPairs]
  have hXM := S.prodDisc.ncard_omega_mul_card
  have hMz := Sec128.card_centralizer_z S h
  have hq2 : 2 ≤ 2 ^ m := Nat.one_lt_two_pow (by have := hB.bender.two_le.2; omega)
  by_cases hcent : u ∈ centralizer (zHull Z M : Set X)
  · left
    have hqn : qU Z M u = 2 ^ n := by
      unfold qU
      rw [inf_eq_right.mpr (fun x hx =>
        mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hcent x hx)), h.m_card]
    have hmn : m = n := Nat.pow_right_injective le_rfl (hq.symm.trans hqn)
    subst hmn
    refine ⟨hcent, rfl, ?_⟩
    have haz := Sec128.thompsonPairCount_z_eq_zero S h huD hu2 hcent
    exact Sec128.arith_a hq2 Nat.card_pos (by rw [hXM, hthom, haz, mul_zero, add_zero]) hMz hau
  · right
    obtain ⟨-, hb, -⟩ := h124 c n i h u huD hu2
    rcases hb with hcomm | ⟨-, k, -, hnk, hqk, -⟩
    · exact absurd (mem_centralizer_iff.mpr fun x hx => hcomm x (h.m_le hx)) hcent
    · have hkm : k = m := Nat.pow_right_injective le_rfl (hqk.symm.trans hq)
      rw [hkm] at hnk
      refine ⟨hcent, hnk, ?_⟩
      have haz := Sec128.thompsonPairCount_z S h huD hu2 hq hnk
      have hV := Sec128.ncard_V_mul S h huD hu2 hq
      have hUM := Sec128.ncard_conj_mul_card M u
      rw [hnk, pow_mul'] at hMz hV
      exact Sec128.arith_b hq2 Nat.card_pos (by rw [hXM, hthom]) hMz hCu hUM.symm
        (by rw [haz, mul_comm]) hV hau

end CFSG.GH74.Uniqueness
