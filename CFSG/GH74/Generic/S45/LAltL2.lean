module

public import CFSG.GH74.GLS.Classes
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Order

public section

namespace CFSG.GH74.Generic.S45.LAlt

open CFSG CFSG.Blueprint CFSG.GH74.GLS CFSG.Assembly.LowTwoRank

theorem hasL2Model_data {L : Type} [Group L] (h : HasL2Model L Odd) :
    IsSimpleGroup L ∧ (∃ a b : L, a * b ≠ b * a) ∧ (∃ v : L, orderOf v = 2) ∧
      ∃ q : ℕ, 5 ≤ q ∧ Odd q ∧ Nat.card L * 2 = q * (q ^ 2 - 1) ∧
        ∀ P : ℕ → Prop, P q → HasL2Model L P := by
  obtain ⟨p, f, hp, hf, hodd, hL⟩ := h
  obtain ⟨⟨hp', hf', hn2, h22, h23⟩, F, hFfield, hFfin, hF, ⟨e⟩⟩ :=
    CFSG.GH74.Generic.stated_of_lieModel_PSL hL
  have hq3 : p ^ f ≠ 3 := fun h3 => h23 (by rw [h3])
  have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
  have hq5 : 5 ≤ p ^ f := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hQ5 : 5 ≤ Nat.card F := by rw [hF]; exact hq5
  have hsimple : IsSimpleGroup L := by
    have : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 F).symm).isSimpleGroup
  have hoddF : Odd (Nat.card F) := hF ▸ hodd
  have hcard : Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.ComponentClassification.CatFactsSp4.card_statedProj_statedSL_two_odd hoddF]
  have hcard2 : Nat.card L * 2 = Nat.card F * (Nat.card F ^ 2 - 1) := by
    have h2 : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) := by
      have h3 : Even (Nat.card F ^ 2 - 1) := Nat.Odd.sub_odd hoddF.pow odd_one
      exact even_iff_two_dvd.1 (h3.mul_left _)
    rw [hcard]
    exact Nat.div_mul_cancel h2
  have h4N : 4 ∣ Nat.card L := by
    obtain ⟨k, hk⟩ := hoddF
    obtain ⟨m, hm⟩ := Nat.even_mul_succ_self k
    have hk2 : Nat.card F ^ 2 - 1 = 4 * (k * (k + 1)) := by
      apply Nat.sub_eq_of_eq_add
      rw [hk]
      ring
    have h1 : Nat.card L * 2 = (4 * (Nat.card F * m)) * 2 := by
      rw [hcard2, hk2, hm]
      ring
    exact ⟨Nat.card F * m, Nat.eq_of_mul_eq_mul_right (by norm_num) h1⟩
  have hfin : Finite L := by
    have : Nat.card L ≠ 0 := by
      intro h0
      rw [h0] at hcard2
      have : 0 < Nat.card F * (Nat.card F ^ 2 - 1) := by
        apply Nat.mul_pos (by omega)
        have : 25 ≤ Nat.card F ^ 2 := by nlinarith
        omega
      omega
    exact Nat.finite_of_card_ne_zero this
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨hsimple, ?_, ?_, p ^ f, hq5, hodd, ?_, fun P hP => ⟨p, f, hp, hf, hP, hL⟩⟩
  · by_contra hcon
    push Not at hcon
    let _ : CommGroup L := { ‹Group L› with mul_comm := fun a b => hcon a b }
    have hprime := IsSimpleGroup.prime_card (α := L)
    rcases hprime.eq_one_or_self_of_dvd 4 h4N with h | h
    · omega
    · rw [← h] at hprime
      exact absurd hprime (by norm_num)
  · exact exists_prime_orderOf_dvd_card' 2 (dvd_trans (by norm_num) h4N)
  · rw [hcard2, hF]

end CFSG.GH74.Generic.S45.LAlt
