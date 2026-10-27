module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BBabyRankCo2
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BBabyRankTwoA
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BBabyRankF4
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BBabyRankTwoD
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1016M5Crit
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.FieldBonusIso

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Blueprint CFSG.Monster.GMS Subgroup

private theorem twoRankLe_of_model_le {s : TauCeti.SporadicName} {p k : ℕ} (hp : 1 < p)
    {X : Type} [Group X] [Finite X] (hX : Nonempty (X ≃* (TauCeti.CFSGIndex.sporadic s).Group))
    (h : GLATwoLocalRank p X ≤ k) : H1017.TwoRankLe p s k := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := hX
  rw [← CFSG.HardMathSupport.Timmesfeld.Tables.Census.glaTwoLocalRank_congr hp (e.trans b.symm)]
  exact h

section Bounds


private theorem card_le_of_not_babyInv_zero {t : NativeSporadic.B} (ht : orderOf t = 2)
    (ht0 : ¬ BabyInv 0 t) (E : Subgroup NativeSporadic.B)
    (hEt : E ≤ centralizer ({t} : Set NativeSporadic.B)) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 3 ^ 4 := by
  obtain ⟨k, hk⟩ := CFSG.Monster.Existence.babyTableIII.1 t ht
  fin_cases k
  · exact absurd hk ht0
  · exact card_le_of_babyInv_one hk E hEt hE
  · exact card_le_of_babyInv_two hk E hEt hE
  · exact card_le_of_babyInv_three hk E hEt hE

theorem card_le_of_le_centralizer_four (F W : Subgroup NativeSporadic.B)
    (hF : IsElemAbelian 3 F) (hW : IsElemAbelian 2 W) (hW4 : 4 ≤ Nat.card W)
    (hFW : F ≤ centralizer (W : Set NativeSporadic.B)) : Nat.card F ≤ 3 ^ 4 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hFw : ∀ w ∈ W, F ≤ centralizer ({w} : Set NativeSporadic.B) := fun w hw =>
    hFW.trans (centralizer_le (Set.singleton_subset_iff.2 hw))
  have hinv : ∀ w ∈ W, w ≠ 1 → orderOf w = 2 := fun w hw hw1 => orderOf_eq_prime (hW.2 w hw) hw1
  obtain ⟨a, haW, ha1⟩ : ∃ a ∈ W, a ≠ 1 := by
    by_contra! h
    rw [(eq_bot_iff_forall W).2 h, card_bot] at hW4
    omega
  obtain ⟨b, hbW, hb1, hba⟩ : ∃ b ∈ W, b ≠ 1 ∧ b ≠ a := by
    by_contra! h
    have hle : W ≤ zpowers a := fun x hx => by
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem _
      · rw [h x hx hx1]
        exact mem_zpowers a
    have h2 := card_le_of_le hle
    rw [Nat.card_zpowers] at h2
    have := orderOf_le_of_pow_eq_one (by norm_num) (hW.2 a haW)
    omega
  by_cases ha0 : BabyInv 0 a
  · by_cases hb0 : BabyInv 0 b
    ·
      have habW := W.mul_mem haW hbW
      have hle2 : orderOf (a * b) ≤ 2 :=
        orderOf_le_of_pow_eq_one (by norm_num) (hW.2 _ habW)
      obtain ⟨k, hk⟩ := (CFSG.Monster.Existence.babyTableIV a ha0).1 b hb0 hba
      fin_cases k
      · exact card_le_of_babyInv_one hk F (hFw _ habW) hF
      · exact card_le_of_babyInv_three hk F (hFw _ habW) hF
      · have h3 : orderOf (a * b) = 3 := hk
        omega
      · obtain ⟨h4, -⟩ : orderOf (a * b) = 4 ∧ BabyInv 1 ((a * b) ^ 2) := hk
        omega
    · exact card_le_of_not_babyInv_zero (hinv b hbW hb1) hb0 F (hFw b hbW) hF
  · exact card_le_of_not_babyInv_zero (hinv a haW ha1) ha0 F (hFw a haW) hF

section Native


theorem card_le_of_involution_three_B {t : NativeSporadic.B} (ht : orderOf t = 2)
    (E : Subgroup NativeSporadic.B) (hEt : E ≤ centralizer ({t} : Set NativeSporadic.B))
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 ^ 5 := by
  by_cases ht0 : BabyInv 0 t
  · exact card_le_of_babyInv_zero ht0 E hEt hE
  · exact (card_le_of_not_babyInv_zero ht ht0 E hEt hE).trans (by norm_num)

theorem glaTwoLocalRank_three_B_le : GLATwoLocalRank 3 NativeSporadic.B ≤ 5 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  refine H1017.H1016M5.twoLocalRankCriterion_holds NativeSporadic.B 3 5 2 Nat.prime_three
    (by norm_num) (fun j hj0 hj2 => ?_) (fun t ht E hEt hE => card_le_of_involution_three_B ht E
      hEt hE) fun F W hF hFc hW hW4 hFW => ?_
  · interval_cases j
    decide +kernel
  · have h := card_le_of_le_centralizer_four F W hF hW (by simpa using hW4) hFW
    rw [hFc] at h
    exact absurd h (by norm_num)

section Catalogue


theorem twoRankLe_three_B : H1017.TwoRankLe 3 .B 5 := by
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  refine twoRankLe_of_model_le (X := NativeSporadic.B) (by norm_num) ?_ glaTwoLocalRank_three_B_le
  exact CFSG.Sporadic.Bridge.B.nonempty_mulEquiv

end Catalogue

end Native

end Bounds

end CFSG.LocalAnalysis.GLTheoremA.H301B
