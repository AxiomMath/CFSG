module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LOmega
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LNG
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Y2LInst
public import CFSG.CGT.PushingUpLit.CGT6.EmbG23.Model

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1 CFSG.OddStandard.HigherRank
  CFSG.RankThree.PartTwo.Census.Carrier.G2Three

theorem y2l_two_part_G23 : 2 ^ (4245696 : ℕ).factorization 2 = 64 := by
  rw [show (4245696 : ℕ) = 2 ^ 6 * 66339 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 66339)]
  norm_num

theorem y2l_sylow_of_elts1 {K Q : Type} [Group K] [Group Q]
    [Finite K] (e : K ≃* Q) (hK : Nat.card K = 4245696) (x : Fin 5 → K)
    (hrel : ∀ y ∈ rels26 1 true, FreeGroup.lift x y = 1)
    (h7 : ∀ y ∈ y2l_ws7 1, FreeGroup.lift x (FreeGroup.mk y) ≠ 1)
    {P : Type} [Group P] {u v w r s : P} (hP : IsPres26 1 true P u v w r s) (S : Sylow 2 Q) :
    Nonempty (P ≃* S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : (![x 0, x 1, x 2, x 3, x 4] : Fin 5 → K) = x := by
    funext i
    fin_cases i <;> rfl
  obtain ⟨hH, hcard⟩ := y2l_isPres26_one (u := x 0) (v := x 1) (w := x 2) (r := x 3)
    (s := x 4) (by rw [hx]; exact hrel) (by rw [hx]; exact h7)
  haveI : Finite Q := Finite.of_equiv _ e.toEquiv
  haveI : Finite (Sylow 2 Q) :=
    Finite.of_injective (fun T : Sylow 2 Q => (T : Set Q)) SetLike.coe_injective
  set H := Subgroup.closure ({x 0, x 1, x 2, x 3, x 4} : Set K)
  have hQ : Nat.card (H.map (e : K →* Q)) = 2 ^ (Nat.card Q).factorization 2 := by
    rw [← Nat.card_congr (e.subgroupMap H).toEquiv, hcard, ← Nat.card_congr e.toEquiv, hK,
      y2l_two_part_G23]
  obtain ⟨f⟩ := y2l_pres_equiv hP hH
  exact ⟨f.trans ((e.subgroupMap H).trans (Sylow.equiv (Sylow.ofCard _ hQ) S))⟩

section G23


theorem y2l_equiv_R3 {Q : Type} [Group Q] (hQ : HRG23 Q) : Nonempty (Q ≃* ↥R3) := by
  obtain ⟨ε⟩ := CFSG.CGT.PushingUpLit.CGT6.EmbG23.exists_equiv_g23
    (CFSG.Blueprint.LieModel.chevalleyExceptionalModel hQ (by decide))
  exact ⟨ε.trans adjointEquivR3⟩

theorem y2l_isG23Type_of_pres
    {Y : Type} [Group Y] {u v w r s : Y} (hY : IsPres26 1 true Y u v w r s) : IsG23Type Y := by
  intro Q _ hQ S
  obtain ⟨e⟩ := y2l_equiv_R3 hQ
  obtain ⟨hrel, h7⟩ := y2l_ng_rels
  have hfin : Finite ↥R3 := Nat.finite_of_card_ne_zero (by rw [card_R3]; norm_num)
  have h := @y2l_sylow_of_elts1 ↥R3 Q _ _ hfin e.symm card_R3 y2l_ngElt hrel h7
  exact h hY S

theorem lemma27G23_holds :
    Lemma27G23 := by
  intro P _ _ u v w r s hP
  haveI hN := y2l_omega1_subgroupOf_normal hP
  exact ⟨hN, y2l_isG23Type_of_pres (y2l_quot_pres _ hP rfl)⟩

end G23

end CFSG.OddStandard.HigherRank.G2Three.Sec2
