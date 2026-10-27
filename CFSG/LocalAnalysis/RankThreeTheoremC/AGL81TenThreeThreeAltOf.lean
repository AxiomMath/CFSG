module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAltSmall
public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.D1EightTen
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.E0Sub.Corner

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree

open CFSG.Open CFSG.AGLEmbedding Subgroup Equiv
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.RichardWeiss.Coordinator (mk_mem_normalizer_barM
  exists_noncomm_quotient_center nonempty_quotient_center_equiv_alt five_le_of_quasisimple_alt
  card_quotient_pCore_le card_alternatingGroup_fin card_perm_prod)

theorem asc81bAltBlockAutNX_of_eightTen (h810 : Asc81bEightTen) :
    Asc81bAltBlockAutNX := by
  intro G _ _ M S L hK hA hL hX1 h678 X hX b hb hbS hbo hbL hW
  subst hX
  have hPL : barM M (normalizer (S : Set G) ⊓ L) ≤ barM M L := AGLEmbedding.barM_mono inf_le_right
  have hβL := mk_mem_normalizer_barM hb hbL
  have hβP := mk_mem_normalizer_barM hb
    (CFSG.HardMathSupport.RichardWeiss.Coordinator.mem_normalizer_inf
      (Subgroup.le_normalizer hbS) hbL)
  have hodd := odd_orderOf_bar hb hbo
  have large := fun (m : ℕ) (hm : 10 ≤ m) hdeg =>
    centralizes_large h810 hK hA hL hX1 (m := m) hm hdeg hb hbS hbo hbL hW
  have hq : CFSG.Open.IsQuasisimple ↥(barM M L) := hL.component.2.2
  rcases h678 with h6 | h7 | h8
  · obtain ⟨-, n, ⟨e⟩, ⟨eQ⟩⟩ := h6
    haveI : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hq.2
    have h5 : 5 ≤ 2 * n :=
      CFSG.HardMathSupport.RichardWeiss.Proving.five_le_of_isSimpleGroup_alt
        (exists_noncomm_quotient_center hq) e
    rcases Nat.lt_or_ge n 5 with hn | hn
    · have hn' : n = 3 ∨ n = 4 := by omega
      rcases hn' with rfl | rfl
      · exact centralizes_alt_six hq.1 e hPL eQ hβL hβP hodd hW
      · exact (CFSG.HardMathSupport.Cooperstein.Proving.not_nonempty_quotient_perm_four
          ⟨eQ⟩).elim
    · exact large (2 * n) (by omega) ⟨e⟩
  · obtain ⟨-, n, ⟨e⟩, ⟨eQ⟩⟩ := h7
    have h5 : 5 ≤ 4 * n := five_le_of_quasisimple_alt hq e
    have hn2 : n ≠ 2 := by
      rintro rfl
      exact CFSG.HardMathSupport.Cooperstein.Proving.not_nonempty_quotient_iso_of_pCore_ne_bot
        CFSG.HardMathSupport.Cooperstein.Proving.pCore_two_perm_two_ne_bot ⟨eQ⟩
    exact large (4 * n) (by omega) (nonempty_quotient_center_equiv_alt (by omega) e)
  · simp only [NineThreeEight] at h8
    obtain ⟨-, N, r, hNe, hr2, h0, h2, h4, ⟨e⟩, φ, -, -⟩ := h8
    have h5 : 5 ≤ N := five_le_of_quasisimple_alt hq e
    obtain ⟨k, hk⟩ := hNe
    have hs : 6 ≤ N - 2 * r := by omega
    rcases Nat.lt_or_ge N 10 with hN | hN
    · have hN' : N = 6 ∨ N = 8 := by omega
      rcases hN' with rfl | rfl
      · have hr : r = 0 := by omega
        subst hr
        have hcard : Nat.card (Equiv.Perm (Fin 0) × Equiv.Perm (Fin (6 - 2 * 0))) ≤
            Nat.factorial 6 / 2 := by
          rw [Nat.card_congr φ.toEquiv.symm, ← card_alternatingGroup_fin (by omega),
            ← Nat.card_congr e.toEquiv]
          exact card_quotient_pCore_le hPL
        rw [card_perm_prod] at hcard
        norm_num [Nat.factorial] at hcard
      · exact centralizes_alt_eight hPL e hs φ hβL hβP hodd hW
    · exact large N hN (nonempty_quotient_center_equiv_alt (by omega) e)

section Holds


theorem asc81bAltBlockAutNX_holds
    : Asc81bAltBlockAutNX :=
  asc81bAltBlockAutNX_of_eightTen
    (CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.asc81bEightTen_of_E0_hyc
      (e0NonShortNotHYcStatement_of_caseI E0Sub.e0NonShortNotCaseIStatement_holds))

end Holds

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
