module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.JStarElimLieArith
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.Sp48Defs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

inductive LieListProfile (p N : ℕ) (d : TauCeti.ValidLieTypeIndex) : Prop
  | linTwo (m : ℕ) (hm : 1 ≤ m) (hd : IsLinTwoIndex p m d)
      (hN : N = p ^ m * (((p ^ m) ^ 2 - 1) / 2)) : LieListProfile p N d
  | unitary (a : ℕ) (ha : 1 ≤ a) (hd : IsUnitaryIndex p d) (hfe : d.1.fieldExponent = a)
      (hN : N = ordTwistedA 2 (p ^ a)) : LieListProfile p N d
  | ree (a : ℕ) (hp : p = 3) (ha : 3 ≤ a) (hd : IsReeGTwoIndex p d) (hfe : d.1.fieldExponent = a)
      (hN : N = (3 ^ a) ^ 3 * ((3 ^ a) ^ 3 + 1) * (3 ^ a - 1)) : LieListProfile p N d
  | spFour (hN : N = ordBC 2 p) : LieListProfile p N d
  | chevThree (hp : p = 3) (hN : N ∈ chevThreeOrders)
      (hD4 : N = 211341312 →
        ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .trialityD4 q)
      (hSp : N = 1056706560 → IsSpFourEightIndex d)
      (hE6 : N = 214841575522005575270400 →
        ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .E6 q) :
      LieListProfile p N d
  | reeFFive (hp : p = 5) (hN : N = reeFFiveOrder) : LieListProfile p N d

theorem LieListProfile.chevOther {p N : ℕ} {d : TauCeti.ValidLieTypeIndex} (hp : p = 3)
    (hN : N ∈ chevThreeOrders) (h1 : N ≠ 211341312) (h2 : N ≠ 1056706560)
    (h3 : N ≠ 214841575522005575270400) : LieListProfile p N d :=
  .chevThree hp hN (fun h => absurd h h1) (fun h => absurd h h2) (fun h => absurd h h3)

theorem lieListProfile (hRee : KFactReeOrder)
    

    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {d : TauCeti.ValidLieTypeIndex}
    (hd : P1ThreeLieList p d) {L₀ : Type} [Group L₀] [Finite L₀] (e : L₀ ≃* CatGroup d) :
    LieListProfile p (Nat.card L₀) d := by
  have : Finite (CatGroup d) := Finite.of_equiv L₀ e.toEquiv
  rw [Nat.card_congr e.toEquiv]
  rcases hd with ⟨m, hm⟩ | hU | hR | hS | hC
  ·
    have hm0 : m ≠ 0 := by obtain ⟨q, -, -, hqn⟩ := hm; exact hqn ▸ q.exponent_pos.ne'
    exact .linTwo m (Nat.one_le_iff_ne_zero.mpr hm0) hm (card_catGroup_linTwo hp2 hm0 hm)
  ·
    obtain ⟨q, hqp, hq⟩ := hU
    have hfe : d.1.fieldExponent = q.exponent := by rw [hq]; simp
    refine .unitary q.exponent q.exponent_pos ⟨q, hqp, hq⟩ hfe ?_
    rw [card_catGroup_twistedA hq, hqp]
  ·
    obtain ⟨hp3, m, hdm⟩ := hR
    exact .ree d.1.fieldExponent hp3 (IsReeGTwoIndex.three_le_fieldExponent ⟨hp3, m, hdm⟩)
      ⟨hp3, m, hdm⟩ rfl (hRee (CatGroup d) d ⟨rfl, m, hdm⟩ ⟨MulEquiv.refl _⟩)
  ·
    obtain ⟨q, ⟨hqp, hqe, h⟩ | ⟨hp3, hqp, hqe, h⟩⟩ := hS
    · refine .spFour ?_
      rw [card_catGroup_B2 h, hqp, hqe, pow_one]
    · refine .spFour ?_
      rw [card_catGroup_twistedA h, hqp, hqe, hp3]
      decide
  ·
    rcases hC with ⟨hp3, q, hq, hq1, h | h | h | h | h | h | h | h⟩ |
        ⟨hp3, q, hq, hq3, h | h | h | h⟩ | ⟨hp5, h⟩
    · have hN := ((card_catGroup_B_even (by norm_num) hq h).trans (by rw [hq1])).trans
        chev3_nums.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · have hN := ((card_catGroup_B_even (by norm_num) hq h).trans (by rw [hq1])).trans
        chev3_nums.2.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · have hN := ((card_catGroup_twistedA h).trans (by rw [hq, hq1])).trans chev3_nums.2.2.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · have hN := ((card_catGroup_twistedA h).trans (by rw [hq, hq1])).trans
        chev3_nums.2.2.2.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · have hN := ((card_catGroup_D_even hq h).trans (by rw [hq1])).trans
        chev3_nums.2.2.2.2.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · have hN := ((card_catGroup_F4_even hq h).trans (by rw [hq1])).trans
        chev3_nums.2.2.2.2.2.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · have hN := ((card_catGroup_E6_even hq h).trans (by rw [hq1])).trans
        chev3_nums.2.2.2.2.2.2.1
      exact .chevThree hp3 (by rw [hN]; decide) (fun h' => absurd (hN.symm.trans h') (by decide))
        (fun h' => absurd (hN.symm.trans h') (by decide)) (fun _ => ⟨q, hq, hq1, h⟩)
    · have hN := ((card_catGroup_trialityD4_even hq h).trans (by rw [hq1])).trans
        chev3_nums.2.2.2.2.2.2.2.1
      exact .chevThree hp3 (by rw [hN]; decide) (fun _ => ⟨q, hq, hq1, h⟩)
        (fun h' => absurd (hN.symm.trans h') (by decide))
        (fun h' => absurd (hN.symm.trans h') (by decide))
    · have hN := ((card_catGroup_B2 h).trans (by rw [hq, hq3])).trans
        chev3_nums.2.2.2.2.2.2.2.2.1
      exact .chevThree hp3 (by rw [hN]; decide) (fun h' => absurd (hN.symm.trans h') (by decide))
        (fun _ => ⟨q, hq, hq3, h⟩) (fun h' => absurd (hN.symm.trans h') (by decide))
    · have hN := ((card_catGroup_G2_even hq h).trans (by rw [hq3])).trans
        chev3_nums.2.2.2.2.2.2.2.2.2.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · have hN := ((card_catGroup_trialityD4_even hq h).trans (by rw [hq3])).trans
        chev3_nums.2.2.2.2.2.2.2.2.2.2.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · have hN := ((card_catGroup_twistedA h).trans (by rw [hq, hq3])).trans
        chev3_nums.2.2.2.2.2.2.2.2.2.2.2.1
      exact .chevOther hp3 (by rw [hN]; decide) (by rw [hN]; decide) (by rw [hN]; decide)
        (by rw [hN]; decide)
    · exact .reeFFive hp5
        ((card_catGroup_reeF4 (m := 2) h).trans chev3_nums.2.2.2.2.2.2.2.2.2.2.2.2)

end CFSG.AGLEmbedding
