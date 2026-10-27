module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Base
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Lin
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Uni
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3G2
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3TriD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Exc
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3D4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3Sp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ClassExcLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ClassExcTorus
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3U4
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FieldLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3FieldSpGlue
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ClassExcSp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267P3ClassExcOrth

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.P3

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open TauCeti (LieTypeIndex PrimePower)

theorem three_dvd_sub_or_add {Q : PrimePower} (h : Q.p ≠ 3) :
    3 ∣ Q.card - 1 ∨ 3 ∣ Q.card + 1 := by
  have h3 : ¬ 3 ∣ Q.card := by
    rw [TauCeti.PrimePower.card_def]
    intro hd
    exact h ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Q.prime_p).1
      (Nat.prime_three.dvd_of_dvd_pow hd)).symm
  omega

theorem p3At_A56
    {n : ℕ} (hn : n = 5 ∨ n = 6) {Q : PrimePower}
    (hv : (LieTypeIndex.A n Q).Valid) (h3 : 3 ∣ Q.card + 1) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exact Or.inl (Lin.concA_of_A H hn (by simpa using hchar) hv e h3)

theorem p3At_twistedA56
    {n : ℕ} (hn : n = 5 ∨ n = 6) {Q : PrimePower}
    (hv : (LieTypeIndex.twistedA n Q).Valid) (h3 : 3 ∣ Q.card - 1) : P3At ⟨_, hv⟩ := by
  intro q Ω _ _ S B H hchar ⟨e⟩
  exact Or.inl (Uni.concA_of_twistedA H hn (by simpa using hchar) hv e h3)

structure P3Owed : Prop where
  twistedA_sub : ∀ {n : ℕ}, 3 ≤ n → n ≤ 4 → ∀ {Q : PrimePower}
    (hv : (LieTypeIndex.twistedA n Q).Valid), 3 ∣ Q.card - 1 → P3At ⟨_, hv⟩

theorem p3At_of_mod {d : TauCeti.ValidLieTypeIndex} {Q : PrimePower} (hd : d.1.characteristic = Q.p)
    (h₁ : 3 ∣ Q.card - 1 → P3At d) (h₂ : 3 ∣ Q.card + 1 → P3At d) : P3At d := by
  intro q Ω _ _ S B H hchar he
  have hQ : Q.p ≠ 3 := fun h => H.three (hchar.symm.trans (hd.trans h))
  rcases three_dvd_sub_or_add hQ with h3 | h3
  · exact h₁ h3 q Ω S B H hchar he
  · exact h₂ h3 q Ω S B H hchar he

theorem p3At_open (h : P3Owed) : ∀ d : TauCeti.ValidLieTypeIndex, ¬ P3Closed d.1 → P3At d := by
  rintro ⟨d, hv⟩ hcl
  have hr := (LieTypeIndex.inStandardRange_iff _).1 ((LieTypeIndex.valid_iff _).1 hv).1
  cases d with
  | A n Q =>
    have hc : (LieTypeIndex.A n Q).characteristic = Q.p := LieTypeIndex.characteristic_A n Q
    have hn1 : n ≠ 1 := by rintro rfl; exact hcl (Or.inl ⟨Q, rfl⟩)
    have hn2 : n ≠ 2 := by rintro rfl; exact hcl (Or.inr (Or.inl ⟨Q, rfl⟩))
    have hn : 3 ≤ n := by have := hr.1; omega
    refine p3At_of_mod (Q := Q) hc (fun h3 => ?_) (fun h3 => ?_)
    · rcases (by omega : n = 3 ∨ (4 ≤ n ∧ n ≤ 6) ∨ 7 ≤ n) with rfl | ⟨h4, h6⟩ | h7
      · exact L4.p3At_A_three_of_dvd_sub_one hv h3
      · exact p3At_A_of_dvd_sub_one h4 h6 hv h3
      · exact p3At_A_of_seven_le h7 hv
    · rcases (by omega : (3 ≤ n ∧ n ≤ 4) ∨ (n = 5 ∨ n = 6) ∨ 7 ≤ n) with ⟨h3', h4⟩ | h56 | h7
      · exact p3At_A_of_dvd_add_one h3' h4 hv h3
      · exact p3At_A56 h56 hv h3
      · exact p3At_A_of_seven_le h7 hv
  | twistedA n Q =>
    have hc : (LieTypeIndex.twistedA n Q).characteristic = Q.p :=
      LieTypeIndex.characteristic_twistedA n Q
    have hn2 : n ≠ 2 := by rintro rfl; exact hcl (Or.inr (Or.inr (Or.inl ⟨Q, rfl⟩)))
    have hn : 3 ≤ n := by have := hr.1; omega
    refine p3At_of_mod (Q := Q) hc (fun h3 => ?_) (fun h3 => ?_)
    · rcases (by omega : (3 ≤ n ∧ n ≤ 4) ∨ (n = 5 ∨ n = 6) ∨ 7 ≤ n) with ⟨h3', h4⟩ | h56 | h7
      · exact h.twistedA_sub h3' h4 hv h3
      · exact p3At_twistedA56 h56 hv h3
      · exact p3At_twistedA_of_seven_le h7 hv
    · rcases (by omega : n = 3 ∨ (4 ≤ n ∧ n ≤ 6) ∨ 7 ≤ n) with rfl | ⟨h4, h6⟩ | h7
      · exact U4.p3At_twistedA_three_of_dvd_add_one hv h3
      · exact p3At_twistedA_of_dvd_add_one h4 h6 hv h3
      · exact p3At_twistedA_of_seven_le h7 hv
  | B n Q =>
    rcases (by have := hr.1; omega : n = 2 ∨ n = 3 ∨ 4 ≤ n) with rfl | rfl | h4
    · exact p3At_B_two hv
    · exact p3At_B3 Q hv
    · exact p3At_B_of_four_le h4 hv
  | C n Q =>
    rcases (by have := hr.1; omega : n = 3 ∨ 4 ≤ n) with rfl | h4
    · exact Sp.p3At_C3 hv
    · exact p3At_C_of_four_le h4 hv
  | D n Q =>
    rcases (by have := hr; omega : n = 4 ∨ 5 ≤ n) with rfl | h5
    · exact p3At_D4 hv
    · exact p3At_D_of_five_le h5 hv
  | twistedD n Q =>
    rcases (by have := hr; omega : n = 4 ∨ 5 ≤ n) with rfl | h5
    · exact p3At_twistedD4 Q hv
    · exact p3At_twistedD_of_five_le h5 hv
  | E6 Q => exact p3At_E6 hv
  | E7 Q => exact p3At_E7 hv
  | E8 Q => exact p3At_E8 hv
  | F4 Q => exact p3At_F4 hv
  | G2 Q => exact p3At_G2 Q hv
  | twistedE6 Q => exact p3At_twistedE6 hv
  | trialityD4 Q => exact p3At_trialityD4 Q hv
  | suzuki m =>
    exact absurd (Or.inr (Or.inr (Or.inr (Or.inl (LieTypeIndex.characteristic_suzuki m))))) hcl
  | reeG2 m =>
    exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (LieTypeIndex.characteristic_reeG2 m))))) hcl
  | reeF4 m =>
    exact absurd (Or.inr (Or.inr (Or.inr (Or.inl (LieTypeIndex.characteristic_reeF4 m))))) hcl
  | tits => exact absurd (Or.inr (Or.inr (Or.inr (Or.inl LieTypeIndex.characteristic_tits)))) hcl

theorem s267FactP3_of_owed (h : P3Owed) : S267FactP3 :=
  s267FactP3_of_open (p3At_open h)

end CFSG.LocalAnalysis.GLTheoremA.S267.P3

end
