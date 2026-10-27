module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1F3OQGen
public import CFSG.LieType.Ree.SuzukiReeOuterTwoPart
public import CFSG.GH74.KGroups.M11

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.F3FG

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem outNoA4_of_reeTitsModel_twistedG2
    {T : Type} [Group T] [Finite T] {p f : ℕ} (h : ReeTitsModel T .twistedG2 p f) :
    OutNoA4 T := by
  have h1 := (CFSG.LieType.Ree.SuzukiReeOuterTwoPart.small_Ree_case h).1
  have : Finite (MulAut T) :=
    Finite.of_injective (fun α : MulAut T => (α : T → T)) fun _ _ h => MulEquiv.ext (congrFun h)
  have h0 : Nat.card (Outer T) ≠ 0 := Nat.card_pos.ne'
  refine outNoA4_of_odd_card_outer (Nat.odd_iff.mpr ?_)
  rcases Nat.mod_two_eq_zero_or_one (Nat.card (Outer T)) with h2 | h2
  · have h3 := Nat.dvd_ordProj_of_dvd h0 Nat.prime_two (Nat.dvd_of_mod_eq_zero h2)
    rw [h1] at h3
    exact absurd h3 (by norm_num)
  · exact h2

theorem outNoA4_of_isSporadic_m11 {K : Type} [Group K]
    (h : NativeSporadic.IsSporadic K .M11) : OutNoA4 K := by
  obtain ⟨M, hP, hA⟩ := CFSG.GH74.KGroups.M11.autModel h
  refine outNoA4_of_forall_mem_inner fun φ => ?_
  obtain ⟨k, hk⟩ := M.inner_of_mem φ (by rw [hP, ← hA]; exact (M.Φ φ).2)
  exact MonoidHom.mem_range.mpr ⟨k, MulEquiv.ext fun x => by rw [MulAut.conj_apply, hk]⟩

end CFSG.ComponentClassification.HarrisLit.T1.F3FG
