module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.DatumSup
public import CFSG.RankThree.PartOne.SPOR.OuterM
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankFive
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanD2PRankThree
import CFSG.Sporadic.Bridge.Y322Central
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.Monster.Existence.TwoB

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Blueprint CFSG.Monster CFSG.Monster.Visible CFSG.Monster.Generated CFSG.SectionRank

theorem pRank_visQuot_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Finite Gvis] :
    Open.pRank p (⊤ : Subgroup (Gvis ⧸ rhoQvis)) = Open.pRank p (⊤ : Subgroup Gvis) := by
  have : Fact p.Prime := ⟨hp⟩
  refine pRank_quotient_eq rhoQvis ?_
  rw [CFSG.Monster.Existence.natCard_rhoQvis]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem pRank_Gvis_le_Gmat {p : ℕ} (hp : p.Prime) [Finite Gmat] [Finite Gvis] :
    Open.pRank p (⊤ : Subgroup Gvis) ≤ Open.pRank p (⊤ : Subgroup Gmat) :=
  pRank_top_le_of_injective hp.one_lt (Subgroup.inclusion Hmat_le_Gmat)
    (Subgroup.inclusion_injective _)

section Co1


theorem three_le_pRank_Gmat_of_Co1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [Finite Gmat]
    [Finite (NativeSporadic.Carrier .Co1)]
    (h : 3 ≤ Open.pRank p (⊤ : Subgroup (NativeSporadic.Carrier .Co1))) :
    3 ≤ Open.pRank p (⊤ : Subgroup Gmat) := by
  have : Finite Gvis :=
    Finite.of_injective (Subgroup.inclusion Hmat_le_Gmat) (Subgroup.inclusion_injective _)
  have e : Gvis ⧸ rhoQvis ≃* NativeSporadic.Carrier .Co1 :=
    CFSG.Monster.Existence.Co1Bridge.visQuotEquivCo1
  rw [← pRank_top_eq_of_mulEquiv hp.one_lt e, pRank_visQuot_eq hp hp2] at h
  exact h.trans (pRank_Gvis_le_Gmat hp)

end Co1

section Free


theorem d2FreeCaseAt_M_of_datum {Pp : ℕ → Prop}
    (h : ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L],
      Nonempty (L ≃* NativeSporadic.Carrier .M) → ∀ p, p.Prime → p ≠ 2 → Pp p →
        D2IndexDatum L p) :
    D2FreeCaseAt (.sporadic .M) Pp := by
  intro X _ _ p hpc R A X₀ K hK ⟨e⟩
  have hq : IsSimpleGroup (K ⧸ Subgroup.center K) := hK.component.2.2.2
  have : IsSimpleGroup K :=
    ((QuotientGroup.quotientMulEquivOfEq hK.center_eq_bot).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  obtain ⟨f⟩ := CFSG.Sporadic.Bridge.Y443.nonempty_mulEquiv
  exact hK.false_of_datum (h K ⟨e.trans f.symm⟩ p hK.prime hK.ne_two hpc)

end Free

section Simple


theorem three_le_pRank_of_mulEquiv_Carrier_M {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [Finite (NativeSporadic.Carrier .Co1)]
    (h : 3 ≤ Open.pRank p (⊤ : Subgroup (NativeSporadic.Carrier .Co1)))
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (e : L ≃* NativeSporadic.Carrier .M) :
    3 ≤ Open.pRank p (⊤ : Subgroup L) := by
  obtain ⟨ε⟩ := CFSG.RankThree.PartOne.SPOR.mulEquiv_Gmat_of_simple e
  have : Finite Gmat := Finite.of_equiv L ε.toEquiv
  rw [pRank_top_eq_of_mulEquiv hp.one_lt ε]
  exact three_le_pRank_Gmat_of_Co1 hp hp2 h

theorem d2IndexDatum_M_of_pRank_Co1 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    [Finite (NativeSporadic.Carrier .Co1)]
    (h : 3 ≤ Open.pRank p (⊤ : Subgroup (NativeSporadic.Carrier .Co1)))
    {L : Type} [Group L] [Finite L] [IsSimpleGroup L] (e : L ≃* NativeSporadic.Carrier .M) :
    D2IndexDatum L p := by
  refine ⟨?_, Or.inr (Or.inl (three_le_pRank_of_mulEquiv_Carrier_M hp hp2 h e))⟩
  rw [CFSG.RankThree.PartOne.SPOR.card_outer_M_of_simple e]
  exact hp.not_dvd_one

theorem d2IndexDatum_M_three :
    ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L],
      Nonempty (L ≃* NativeSporadic.Carrier .M) → D2IndexDatum L 3 := by
  intro L _ _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Co1) := (CFSG.Sporadic.Co1.fam_co1_simplicity).1
  exact d2IndexDatum_M_of_pRank_Co1 Nat.prime_three (by norm_num) three_le_pRank_Co1_three e

theorem d2IndexDatum_M_five :
    ∀ (L : Type) [Group L] [Finite L] [IsSimpleGroup L],
      Nonempty (L ≃* NativeSporadic.Carrier .M) → D2IndexDatum L 5 := by
  intro L _ _ _ ⟨e⟩
  have : Finite (NativeSporadic.Carrier .Co1) := (CFSG.Sporadic.Co1.fam_co1_simplicity).1
  exact d2IndexDatum_M_of_pRank_Co1 Nat.prime_five (by norm_num) three_le_pRank_Co1_five e

theorem d2FreeCaseAt_M_three_five :
    D2FreeCaseAt (.sporadic .M) fun p => p = 3 ∨ p = 5 := by
  refine d2FreeCaseAt_M_of_datum fun L _ _ _ he p _ _ hp => ?_
  rcases hp with rfl | rfl
  · exact d2IndexDatum_M_three L he
  · exact d2IndexDatum_M_five L he

theorem d2IndexCaseAt_M_three_five :
    D2IndexCaseAt (.sporadic .M) fun p => p = 3 ∨ p = 5 :=
  d2FreeCaseAt_M_three_five.indexCaseAt

end Simple

end CFSG.AGLEmbeddingD2
