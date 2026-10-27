module

public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.Small
public import CFSG.HardMathSupport.Meierfrankenfeld.LieOdd.SpOuter63
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.RouteA
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.LieOdd

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.Assembly.LowTwoRank TauCeti

section Group

variable {K : Type} [Field K] [Finite K]

theorem noIrrFFOffender_psp63 (hK : Nat.card K = 3) :
    NoIrrFFOffender (StatedProj (StatedSp 3 K)) := by
  have := Fintype.ofFinite K
  have hcard : Fintype.card K = 3 := by rw [← Nat.card_eq_fintype_card]; exact hK
  have hchar : CharP K 3 := charP_of_card_eq_prime_pow (f := 1) (by simpa using hcard)
  have h2 : (2 : K) ≠ 0 := two_ne_zero_char_three
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hneg : ¬ IsSquare (-1 : K) := by
    rintro ⟨y, hy⟩
    rcases eq_zero_or_one_or_neg_one hK y with h | h | h
    · rw [h] at hy; simp at hy
    · rw [h] at hy; exact h2 (by linear_combination -hy)
    · rw [h] at hy; exact h2 (by linear_combination -hy)
  have hcent := center_psp63_eq_bot hK
  have hSp : Nat.card (StatedSp 3 K) = 2 * Nat.card (StatedProj (StatedSp 3 K)) :=
    card_statedSp_eq_two_mul_card_proj h2 3
  have hcard2 : Nat.card (MulAut (StatedProj (StatedSp 3 K))) ≤
      2 * Nat.card (StatedProj (StatedSp 3 K)) := by
    have := card_mulAut_psp_le_card_sp_mul (K := K) (p := 3) (e := 1) (r := 3)
      (by norm_num) (by simpa using hK) (by norm_num)
    simpa [hSp] using this
  refine noIrrFFOffender_of_route_A (r := 4) (ρ := 6) (p := 3) (n := 1) hcent hcard2
    (by norm_num) (by norm_num) (by rw [orderOf_two_zmod_three]; norm_num)
    (fun B hc h2B => two_rank_psp63 h2 hK B hc h2B) ?_ ?_ (houter_psp63 hK)
  · intro L _ _ hq ⟨e⟩ hodd
    have := center_eq_bot_of_psp hq.1 hodd (K := K) (by norm_num) (Or.inr ⟨hK, le_rfl⟩)
      (by rw [hK]; decide) e
    rw [this, Subgroup.card_bot]
    norm_num
  · intro t ht2 ht1
    classical
    exact exists_heisCfg_of_involution (p := 3) (n := 1) (by norm_num) hneg t ht2 ht1

end Group

theorem noIrrFFOffender_smallPSp63 {q : PrimePower} (hv : (LieTypeIndex.C 3 q).Valid)
    (h3 : q.card = 3) : NoIrrFFOffender (CFSGIndex.lie ⟨.C 3 q, hv⟩).Group := by
  have := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField
    (⟨.C 3 q, hv⟩ : ValidLieTypeIndex)
  have hK : Nat.card ↥(ValidLieTypeIndex.fixedField (⟨.C 3 q, hv⟩ : ValidLieTypeIndex)) = 3 := by
    rw [ValidLieTypeIndex.card_fixedField]
    simpa [ValidLieTypeIndex.fieldOrder, PrimePower.card_def] using
      (PrimePower.card_def q).symm.trans h3
  exact FFSporadic.noIrrFFOffender_transfer (noIrrFFOffender_psp63 hK)
    ⟨(CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj 3 q hv).symm⟩

theorem smallPSp63 : SmallPSp63 := by
  intro d q hq hd
  obtain ⟨d, hv⟩ := d
  simp only at hd
  subst hd
  exact noFFModule_of_noIrrFFOffender (noIrrFFOffender_smallPSp63 hv hq)

end CFSG.HardMathSupport.Meierfrankenfeld.LieOdd
