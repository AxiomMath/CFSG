module

public import CFSG.LocalAnalysis.SectionRank.QTK.Interface
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankThree46F2
public import CFSG.RankThree.PartTwo.Census.Sporadic.RankThree46Odd
public import CFSG.RankThree.PartTwo.Census.Sporadic.Co1
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi22
public import CFSG.RankThree.PartTwo.Census.Sporadic.Fi23
public import CFSG.RankThree.PartTwo.Census.Sporadic.B
public import CFSG.RankThree.PartTwo.Census.Sporadic.Klein
public import CFSG.RankThree.ThetaFree.Sporadic
public import CFSG.Sporadic.Bridge.Y443Split
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.CoxeterM

public section

namespace CFSG.SectionRank.QTK

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.PartTwo.Census
open CFSG.QuasithinUnique.SQTK TauCeti.Sporadic

theorem y443_coxeter_pow (i j : Fin 12) :
    (PresentedGroup.of i * PresentedGroup.of j : Y443) ^ Monster.coxeterMatrix i j = 1 := by
  have key : ∀ i j : Fin 12, i ≠ j → (((i, j) ∈ Monster.edges ∨ (j, i) ∈ Monster.edges) ↔
      CFSG.Sporadic.Bridge.Y443.adjB i j = true) := by
    rw [Monster.edges_def]
    decide +kernel
  rw [Monster.coxeterMatrix_apply]
  split_ifs with hij hadj
  · subst hij
    rw [pow_one]
    exact CFSG.Sporadic.Bridge.Y443.x_mul_self _
  · exact CFSG.Sporadic.Bridge.Y443.x_adj hij
      ((CFSG.Sporadic.Bridge.Y443.adjacent_iff_adjB i j).2 ((key i j hij).1 hadj))
  · exact CFSG.Sporadic.Bridge.Y443.x_nadj hij fun h =>
      hadj ((key i j hij).2 ((CFSG.Sporadic.Bridge.Y443.adjacent_iff_adjB i j).1 h))

theorem four_le_localRank_three_of_mulEquiv_nativeM {G : Type} [Group G] [Finite G]
    (e : G ≃* NativeSporadic.M) (hG : ∃ g h : G, g * h ≠ h * g) : 4 ≤ localRank 3 G := by
  refine four_le_localRank_three_of_coxeter monsterEdges Monster.coxeterMatrix (fun i j => ?_)
    (Coxeter.edgeGraph_connected 0 (by decide +kernel) (by decide +kernel))
    (Coxeter.edgeGraph_cliqueFree_three (by decide +kernel))
    (PresentedGroup.of (rels := y443Relations)) (PresentedGroup.closure_range_of _)
    y443_coxeter_pow (K := commutator Y443) le_rfl e hG ![1, 3, 7, 10] ![0, 4, 8, 11]
    (by decide +kernel) (by decide +kernel) 5 2 (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
  rw [Monster.coxeterMatrix_apply, Monster.edges_def]
  rfl


theorem qt_sporadic_restriction
    {S : Type} [Group S] [Finite S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (hQT : CFSG.Open.evenRank S ≤ 2)
    (s : TauCeti.SporadicName) (e : S ≃* Carrier s) : s ∈ qtkSporadicNames := by
  have hloc : ∀ {T : Type} [Group T] {k : ℕ}, S ≃* T → 3 ≤ k →
      (∀ [Finite T], k ≤ localRank 3 T) → False := fun e' hk h =>
    not_evenRank_le_two_of_localRank e' Nat.prime_three (by norm_num) (le_trans hk h) hQT
  cases s with
  | M11 | M12 | M22 | M23 | M24 | J1 | J2 | J3 | J4 | HS | He | Ru | McL =>
    simp [qtkSporadicNames]
  | Co1 => exact (hloc (T := NativeSporadic.Co1) e (by norm_num) four_le_localRank_three_Co1).elim
  | Co2 => exact (hloc (T := NativeSporadic.Co2) e le_rfl three_le_localRank_nativeCo2).elim
  | Co3 => exact (hloc (T := NativeSporadic.Co3) e le_rfl three_le_localRank_nativeCo3).elim
  | Fi22 =>
    exact (hloc (T := NativeSporadic.Fi22) e (by norm_num) four_le_localRank_three_Fi22).elim
  | Fi23 =>
    exact (hloc (T := NativeSporadic.Fi23) e (by norm_num) four_le_localRank_three_Fi23).elim
  | Suz => exact (hloc (T := NativeSporadic.Suz) e le_rfl three_le_localRank_nativeSuz).elim
  | ONan => exact (hloc (T := NativeSporadic.ON) e le_rfl three_le_localRank_nativeON).elim
  | HN => exact (hloc (T := NativeSporadic.HN) e le_rfl three_le_localRank_nativeHN).elim
  | Ly => exact (hloc (T := NativeSporadic.Ly) e le_rfl three_le_localRank_nativeLy).elim
  | Th => exact (hloc (T := NativeSporadic.Th) e le_rfl three_le_localRank_nativeTh).elim
  | B => exact (hloc (T := NativeSporadic.B) e (by norm_num) four_le_localRank_three_B).elim
  | M =>
    exact (hloc (MulEquiv.refl S) (by norm_num)
      (four_le_localRank_three_of_mulEquiv_nativeM e hnonab)).elim
  | Fi24Prime =>
    have h4 : 4 ≤ CFSG.Assembly.evenRank S :=
      (CFSG.RankThree.ThetaFree.sectionsForceEvenRankFour_fi23_fi24prime').2 S ⊤ ⊥
        ⟨(QuotientGroup.quotientBot.trans Subgroup.topEquiv).trans e⟩
    have : CFSG.Open.evenRank S = CFSG.Assembly.evenRank S := rfl
    omega

theorem qtSporadicRestriction_holds
    : QTSporadicRestriction :=
  fun _ _ _ hnonab hQT s ⟨e⟩ => qt_sporadic_restriction hnonab hQT s e

end CFSG.SectionRank.QTK
