module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowU43
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowArith
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420SuzRowCent
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1420LyOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.K14SporRows1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1420

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem suzRow_spor_of_rows {z : ℕ} (hOrd : SporadicOrdersTable) (hOut : SporadicOuterLeTwo)
    (hCo3 : K14Spor.CardRow 3265920 .Co3) (hLy : K14Spor.CardRow 3265920 .Ly)
    (hTh : K14Spor.CardRow 3265920 .Th) (hFi23 : K14Spor.CardRow 3265920 .Fi23)
    (hFi24 : K14Spor.CardRow 3265920 .Fi24Prime) (hB : K14Spor.CardRow 3265920 .B)
    (hM : ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic .M).Group) → ∀ β : MulAut S, β ^ 3 = 1 →
        β ≠ 1 → ∀ J : Subgroup S,
          GLAPComponent 3 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup β) J →
            catalogIs (PSimple 3 J) (S8.isU4of 3) → False)
    (hFi22 : CentRow .Fi22 fun (T : Type) [Group T] => Subgroup.center T = ⊥)
    (hCo1 : CentRow .Co1 fun (T : Type) [Group T] =>
      Nat.card (Subgroup.center T) = 9 ∨ Nat.card T ≠ Nat.card (Subgroup.center T) * 3265920)
    {S : Type} [Group S] [Finite S] {t : TauCeti.SporadicName}
    (e : S ≃* (TauCeti.CFSGIndex.sporadic t).Group) {β : MulAut S} {J : Subgroup S}
    (hcore : I1420CoreP 3 (S8.isU4of 3) z β J) :
    t = .Suz ∨ (t = .Fi22 ∧ Subgroup.center (PQuot 3 J) = ⊥) ∨
      (t = .Co1 ∧ Nat.card (Subgroup.center (PQuot 3 J)) = 9) := by
  obtain ⟨hS, hnab, hβp, hβ1, -, hJ, hT, -⟩ := hcore
  have hcard : Nat.card (PSimple 3 J) = 3265920 := card_eq_of_isU4of_three hT
  have hdvd := prime_mul_card_pSimple_dvd_sporOrd hOrd hOut Nat.prime_three (by norm_num) e hS
    hnab hβp hβ1 hJ.1
  rw [hcard] at hdvd
  rcases eq_survivor_of_three_mul_u43_dvd t hdvd with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact absurd hcard (hCo3 S ⟨e⟩ β hβp hβ1 J hJ)
  · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    rcases hCo1 S ⟨e⟩ β hβp hβ1 J hJ with h | h
    · exact h
    · refine absurd ?_ h
      calc Nat.card (PQuot 3 J)
          = Nat.card (PSimple 3 J) * Nat.card (Subgroup.center (PQuot 3 J)) :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center (PQuot 3 J))
        _ = Nat.card (Subgroup.center (PQuot 3 J)) * 3265920 := by rw [hcard, mul_comm]
  · exact absurd hcard (hLy S ⟨e⟩ β hβp hβ1 J hJ)
  · exact absurd hcard (hTh S ⟨e⟩ β hβp hβ1 J hJ)
  · exact Or.inr (Or.inl ⟨rfl, hFi22 S ⟨e⟩ β hβp hβ1 J hJ⟩)
  · exact absurd hcard (hFi23 S ⟨e⟩ β hβp hβ1 J hJ)
  · exact absurd hcard (hFi24 S ⟨e⟩ β hβp hβ1 J hJ)
  · exact absurd hcard (hB S ⟨e⟩ β hβp hβ1 J hJ)
  · exact (hM S ⟨e⟩ β hβp hβ1 J hJ hT).elim

end CFSG.LocalAnalysis.GLTheoremA.H1420

end
