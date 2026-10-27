module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoBigHall
public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Configuration
public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoDefs

public section

namespace CFSG.OddStandard.AltStdCycTwo

open Subgroup CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

theorem cycTwoBigFalse_of_fullPair_generic
    (h : CycTwoBigFullPairFalse)
    {G : Type} [Group G] [Finite G]
    {L : Subgroup G}
    (hS : StandardSetting G L)
    {n : ℕ} (hn : 9 ≤ n)
    (theta : Nonempty (L ≃* alternatingGroup (Fin n)))
    (S : Sylow 2 (centralizer (L : Set G)))
    (hcyc : IsCyclic (S : Subgroup (centralizer (L : Set G))))
    (h4 : 4 ≤ Nat.card S) : False := by
  by_cases hb : ∃ g : G, g ∉ normalizer (L : Set G) ∧ ∃ P : Subgroup G,
      P ≤ (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom ⊓ normalizer (L : Set G) ∧
        IsPGroup 2 P ∧ 4 ≤ Nat.card P
  ·
    obtain ⟨g, hg, P, hP, hPp, hP4⟩ := hb
    obtain ⟨g', hg', R, T, hRK, hR, hRcard, hTK, -, hT, hTcard, hRT⟩ :=
      exists_full_conj_centralized hS.standard S hcyc hg (hP.trans inf_le_left)
        (hP.trans inf_le_right) hPp hP4
    have hgi : g'⁻¹ ∉ normalizer (L : Set G) := fun hmem => hg' (by simpa using inv_mem hmem)
    have hTK' : T ≤ CFSG.conjugate (centralizer (L : Set G)) g'⁻¹ := by
      simpa [CFSG.conjugate] using hTK
    exact h G L hS n hn theta S hcyc h4 R T g'⁻¹ hRK hR hRcard hgi hTK' hT hTcard hRT
  ·
    refine cycTwoBigHallFalse_holds G L hS n hn theta S hcyc h4 fun g hg P hP hPp => ?_
    by_contra hlt
    push Not at hlt
    obtain ⟨j, hj⟩ := hPp.exists_card_eq
    have h4P : 4 ≤ Nat.card P := by
      rcases j with _ | _ | j
      · rw [hj] at hlt
        norm_num at hlt
      · rw [hj] at hlt
        norm_num at hlt
      · rw [hj]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact hb ⟨g, hg, P, hP, hPp, h4P⟩

theorem cycTwoBigFalse_of_fullPair (h : CycTwoBigFullPairFalse) : CycTwoBigFalse := by
  intro G _ _ L hS n _ hn theta _ S hcyc h4
  exact cycTwoBigFalse_of_fullPair_generic h hS hn ⟨theta⟩ S hcyc h4

end CFSG.OddStandard.AltStdCycTwo
