module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911Ly
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L128LyBridge
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L128Ly

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.Blueprint

theorem oddCore_eq_bot_of_quasisimple_center_two {Q : Type} [Group Q] [Finite Q]
    (hq : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (hZ : Nat.card (Subgroup.center Q) = 2)
    (h4 : 4 ∣ Nat.card Q) : CFSG.oddCore Q = ⊥ := by
  set A : Subgroup Q := CFSG.oddCore Q with hA
  have hodd : Odd (Nat.card A) := CFSG.ABGLocalTools.odd_card_oddCore
  have hn : (A.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (A.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · have hle : A ≤ Subgroup.center Q := by
      intro a ha
      have : QuotientGroup.mk' (Subgroup.center Q) a ∈
          A.map (QuotientGroup.mk' (Subgroup.center Q)) := Subgroup.mem_map_of_mem _ ha
      rw [h, Subgroup.mem_bot] at this
      exact (QuotientGroup.eq_one_iff a).mp this
    have hd : Nat.card A ∣ 2 := hZ ▸ Subgroup.card_dvd_of_le hle
    have h1 : Nat.card A = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact Subgroup.card_eq_one.mp h1
  · exfalso
    have hdvd : Nat.card (Q ⧸ Subgroup.center Q) ∣ Nat.card A := by
      rw [← Subgroup.card_top (G := Q ⧸ Subgroup.center Q), ← h]
      exact Subgroup.card_map_dvd _ _
    have hQ : Nat.card Q = Nat.card (Q ⧸ Subgroup.center Q) * Nat.card (Subgroup.center Q) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q))
    have hoddq : Odd (Nat.card (Q ⧸ Subgroup.center Q)) :=
      Odd.of_dvd_nat hodd hdvd
    rw [hZ] at hQ
    obtain ⟨m, hm⟩ := hoddq
    rw [hm] at hQ
    omega

section LyJ


theorem ly_invol_oddCore : LyInvolOddCore := by
  intro X _ _ hX w hw
  obtain ⟨e0⟩ := hX
  have e1 : X ≃* NativeSporadic.Ly := e0
  have e2 : L128.GrpEquiv X CFSG.Sporadic.Ly.J := e1.trans CFSG.Sporadic.Ly.lyEquivJ
  obtain ⟨hCK, hq, hzc, hcard⟩ := ClassicalInvolution.LyProof.K_facts
  obtain ⟨E⟩ := L128.centralizer_equiv_of_all_conj (X := X) (Y := ↥CFSG.Sporadic.Ly.J) e2
    ClassicalInvolution.LyProof.zJ ClassicalInvolution.LyProof.KJ hCK L128.all_involutions_conj hw
  have E' : L128.GrpEquiv ↥(centralizer ({w} : Set X)) ↥ClassicalInvolution.LyProof.KJ := E
  have h4 : 4 ∣ Nat.card ↥ClassicalInvolution.LyProof.KJ := by
    rw [hcard]
    norm_num
  have hKJ : CFSG.oddCore ↥ClassicalInvolution.LyProof.KJ = ⊥ :=
    oddCore_eq_bot_of_quasisimple_center_two hq.2 hzc h4
  exact CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog.oddCore_eq_bot_of_mulEquiv
    E'.symm hKJ

end LyJ

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
