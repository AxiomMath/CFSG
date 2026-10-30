module

public import CFSG.HardMathSupport.U4FF.Defs
public import CFSG.HardMathSupport.U4FF.Irr
public import CFSG.HardMathSupport.U4FF.OuterTransvection

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.LocalAnalysis.RankThreeUC CFSG.Quasithin CFSG.QuasithinUnique.Setup.Family

theorem u4FFNatural_of_dichotomy (hdich : U4RankDichotomy) : U4FFNatural := by
  intro S _ _ hS n L A hL hA hAN hnc hirr hoff
  have hS' : ∀ s : S, s * s = 1 := fun s => by simpa [sq] using hS s
  haveI : Fact (∀ s : S, s * s = 1) := ⟨hS'⟩
  have hirrL := isIrrOn_of_offender hS' hL hA hAN hirr hoff
  refine ⟨hirrL, ?_⟩
  have hn := one_le_of_isU4Group hL
  rcases hdich S n L hn hL hirrL with hnat | hrank
  · exact hnat
  · exfalso
    have hAE := card_le_two_mul_inf hS' hL hA hAN hirr
    by_cases hE : A ⊓ L = ⊥
    · obtain ⟨a, haA, l, hl, hal⟩ := hnc
      have ha1 : a ≠ 1 := fun h1 => hal (by rw [h1, one_mul, mul_one])
      have haL : a ∉ L := fun haL => ha1 (by
        have : a ∈ A ⊓ L := ⟨haA, haL⟩
        rw [hE] at this
        exact Subgroup.mem_bot.1 this)
      have hE1 : Nat.card ↥(A ⊓ L) = 1 := by rw [hE]; simp
      have hA2 : Nat.card A ≤ 2 := by omega
      have hdisp : 2 ^ disp a ≤ Nat.card A := two_pow_disp_le_card haA hoff
      have hdisp1 : disp a ≤ 1 := by
        by_contra h2
        push Not at h2
        have : 2 ^ 2 ≤ 2 ^ disp a := Nat.pow_le_pow_right (by norm_num) h2
        omega
      obtain ⟨t, htL, ht1, ht2, htd⟩ := exists_small_involution hL hA hAN hirr haA haL
      have h1 : 4 * n + 2 ≤ disp t := hrank t htL ht1 ht2
      omega
    · obtain ⟨t, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hE
      have htA : (t : MulAut S) ∈ A := t.2.1
      have htL : (t : MulAut S) ∈ L := t.2.2
      have ht2 : (t : MulAut S) * t = 1 := by simpa [sq] using hA.2 _ htA
      have ht1' : (t : MulAut S) ≠ 1 := fun h => ht1 (Subtype.ext h)
      have h1 : 4 * n + 2 ≤ disp (t : MulAut S) := hrank t htL ht1' ht2
      have h2 : 2 ^ disp (t : MulAut S) ≤ Nat.card A := two_pow_disp_le_card htA hoff
      have hE4 : Nat.card ↥(A ⊓ L) ≤ (2 ^ n) ^ 4 :=
        card_le_q4_of_elemAbelian hL ⟨fun a ha b hb => hA.1 a ha.1 b hb.1,
          fun a ha => hA.2 a ha.1⟩ inf_le_right
      have hpow : (2 ^ n) ^ 4 = 2 ^ (4 * n) := by rw [← pow_mul]; ring_nf
      have h3 : 2 ^ (4 * n + 2) ≤ 2 ^ disp (t : MulAut S) :=
        Nat.pow_le_pow_right (by norm_num) h1
      have h4 : Nat.card A ≤ 2 ^ (4 * n + 1) := by
        calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ L) := hAE
          _ ≤ 2 * (2 ^ n) ^ 4 := Nat.mul_le_mul_left _ hE4
          _ = 2 ^ (4 * n + 1) := by rw [hpow, pow_succ]; ring
      have h5 : 2 ^ (4 * n + 2) = 2 * 2 ^ (4 * n + 1) := by rw [pow_succ]; ring
      have h6 : 0 < 2 ^ (4 * n + 1) := by positivity
      omega

end CFSG.HardMathSupport.U4FF
