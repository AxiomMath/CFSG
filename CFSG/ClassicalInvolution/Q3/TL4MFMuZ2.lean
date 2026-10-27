module

public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2L32
public import CFSG.ClassicalInvolution.Q3.TL3S8Zstar
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2B3

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Blueprint

theorem thirtyTwo_dvd_card_exc {G : Type} [Group G] {t : Assembly.LowTwoRank.StatedLieTag}
    {p f : ℕ} (ht : t = .G2 ∨ t = .trialityD4) (h : LieModel G t 0 p f) : 32 ∣ Nat.card G := by
  have hc : ChevalleyExceptionalModel G t p f := by
    rcases h with ⟨htc, -⟩ | ⟨-, -, h⟩ | ⟨-, htc, -⟩ | ⟨-, htc, -⟩
    · rcases ht with rfl | rfl <;> exact absurd htc (by decide)
    · exact h
    · rcases ht with rfl | rfl <;> exact absurd htc (by decide)
    · rcases ht with rfl | rfl <;> exact absurd htc (by decide)
  have hp : p.Prime := hc.1.1
  have hf : 1 ≤ f := hc.1.2.1
  by_cases hp2 : p = 2
  · subst hp2
    have h2 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hc
    rcases ht with rfl | rfl
    · rw [h2]
      exact thirtyTwo_dvd_ordG2_two hf
    · rw [h2]
      exact thirtyTwo_dvd_ordTrialityD4_two hf
  · have h2 := CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 hc
    have hodd : p ^ f % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2).pow
    rcases ht with rfl | rfl
    · rw [h2]
      exact thirtyTwo_dvd_ordG2_of_odd hodd
    · rw [h2]
      exact thirtyTwo_dvd_ordTrialityD4_of_odd hodd

theorem thirtyTwo_dvd_card_m12 {G : Type} [Group G] (h : NativeSporadic.IsSporadic G .M12) :
    32 ∣ Nat.card G := by
  obtain ⟨e⟩ := h
  have hc : Nat.card (NativeSporadic.Carrier .M12) = 95040 := CFSG.Sporadic.Mathieu.card_M12
  rw [Nat.card_congr e.toEquiv, hc]
  norm_num

variable {X : Type} [Group X] [Finite X] {R : Subgroup X} {S : Sylow 2 R} {z : X}

theorem l3_clause (hm : TL4.EdgelessMember3 R S z) [IsSimpleGroup ↥(genFittingFStar X)]
    (hnab : ∃ a b : genFittingFStar X, a * b ≠ b * a) (h32 : ¬ 32 ∣ Nat.card X) {p f : ℕ}
    (hL : LieModel (TL4.FStarQuot X) .PSL 3 p f) :
    IsSimpleGroup X ∧ LieModel X .PSL 3 p f := by
  by_cases hp2 : p = 2
  · subst hp2
    exfalso
    obtain ⟨-, hf, K, _, _, hK, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hL
    by_cases hf1 : f = 1
    · subst hf1
      exact false_of_l32 hm.cls.1 hnab hL
    · have h := thirtyTwo_dvd_psl3_of_two hK (by omega)
      exact h32 (((Nat.card_congr e.toEquiv).symm ▸ h).trans card_fstarQuot_dvd)
  · exact l3_clause_odd hm hnab h32 hp2 hL

theorem muZ2Table_body (hB3 : GoldschmidtB3Tmp)
    (hm : TL4.EdgelessMember3 R S z) (hmu : TL4.MuZ2Member R) [IsSimpleGroup ↥(genFittingFStar X)]
    (hidx : (genFittingFStar X).index ∣ 6) :
    (∀ p f : ℕ, LieModel (TL4.FStarQuot X) .PSL 3 p f →
      IsSimpleGroup X ∧ LieModel X .PSL 3 p f) ∧
    (∀ p f : ℕ, LieModel (TL4.FStarQuot X) .PSU 3 p f →
      IsSimpleGroup X ∧ LieModel X .PSU 3 p f ∧ p ^ f % 4 = 1) ∧
    (∀ p f : ℕ, ¬ LieModel (TL4.FStarQuot X) .G2 0 p f) ∧
    (∀ p f : ℕ, ¬ LieModel (TL4.FStarQuot X) .trialityD4 0 p f) ∧
    ¬ NativeSporadic.IsSporadic (TL4.FStarQuot X) .M12 := by
  have hnab := nonabelian_fstar hidx (eight_dvd_card hm.cls.1)
  have hz1 : z ≠ 1 := fun h => by
    have := hm.datum.order
    rw [h, orderOf_one] at this
    omega
  have h32 := not_thirtyTwo_dvd_card hB3 hm hmu (not_mem_center_of_fstar hnab hz1)
  refine ⟨fun p f hL => l3_clause hm hnab h32 hL, fun p f hL => u3_clause hm hnab h32 hL,
    fun p f hL => h32 ((thirtyTwo_dvd_card_exc (Or.inl rfl) hL).trans card_fstarQuot_dvd),
    fun p f hL => h32 ((thirtyTwo_dvd_card_exc (Or.inr rfl) hL).trans card_fstarQuot_dvd),
    fun hM => h32 ((thirtyTwo_dvd_card_m12 hM).trans card_fstarQuot_dvd)⟩

omit [Finite X] in
theorem index_dvd_six [Finite X] (h : (genFittingFStar X).index ≤ 2 ∨
    (genFittingFStar X).index ∣ 6) : (genFittingFStar X).index ∣ 6 := by
  rcases h with h | h
  · have h0 : (genFittingFStar X).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    rcases (by omega : (genFittingFStar X).index = 1 ∨ (genFittingFStar X).index = 2) with
      h1 | h1 <;> rw [h1] <;> norm_num
  · exact h

end CFSG.ClassicalInvolution.Q3.TL4.MFMuZ2

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Disconnected.AschTight

theorem muZ2Table_of_b3 (hB3 : GoldschmidtB3Tmp) : MuZ2Table := by
  intro X _ _ R S z hm hmu hs hidx
  exact MFMuZ2.muZ2Table_body hB3 hm hmu
    (MFMuZ2.index_dvd_six (by simp [hidx]))

end CFSG.ClassicalInvolution.Q3.TL4
