module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.LeavesR
public import CFSG.LocalAnalysis.OddStandard.SmallF3.HypA2.Phase2Inputs

public section

namespace CFSG.OddStandard.SmallF3.HypA2

open Subgroup CFSG.Blueprint CFSG.Open CFSG.ComponentClassification

private theorem ordA_two_four : ordA 2 (2 ^ 2) = 20160 := by decide

private theorem factorial_div_two_ne_orders (n : ℕ) (hn : 8 ≤ n) :
    n.factorial / 2 ≠ 4030387200 ∧ n.factorial / 2 ≠ 95040 ∧ n.factorial / 2 ≠ 604800 := by
  have hfac : ∀ m : ℕ, 8 ≤ m → m ≤ 14 → m.factorial / 2 ≠ 4030387200 ∧
      m.factorial / 2 ≠ 95040 ∧ m.factorial / 2 ≠ 604800 := by
    intro m hm1 hm2
    interval_cases m <;> decide
  refine ⟨?_, ?_, ?_⟩
  · intro h
    by_cases h15 : 15 ≤ n
    · have hmono : 653837184000 ≤ n.factorial / 2 := by
        calc 653837184000 = Nat.factorial 15 / 2 := by decide
          _ ≤ n.factorial / 2 := Nat.div_le_div_right (Nat.factorial_le h15)
      omega
    · exact (hfac n hn (by omega)).1 h
  · intro h
    by_cases h11 : 11 ≤ n
    · have hmono : 19958400 ≤ n.factorial / 2 := by
        calc 19958400 = Nat.factorial 11 / 2 := by decide
          _ ≤ n.factorial / 2 := Nat.div_le_div_right (Nat.factorial_le h11)
      omega
    · exact (hfac n hn (by omega)).2.1 h
  · intro h
    by_cases h11 : 11 ≤ n
    · have hmono : 19958400 ≤ n.factorial / 2 := by
        calc 19958400 = Nat.factorial 11 / 2 := by decide
          _ ≤ n.factorial / 2 := Nat.div_le_div_right (Nat.factorial_le h11)
      omega
    · exact (hfac n hn (by omega)).2.2 h

private theorem inSA_of_order {S : Type} [Group S] [Finite S]
    (hO : SporadicOrders) (hcat : Catalog S) {N : ℕ} (hord : N = Nat.card S)
    (hN : 20160 < N)
    (hN2 : N ≠ 4030387200 ∧ N ≠ 95040 ∧ N ≠ 604800)
    (hodd : ∀ r : ℕ, r.Prime → r ≠ 2 → HarrisLit.IsSimpleChevalleyOver r S → False) :
    InSA S := by
  refine ⟨hcat, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr hr2 hChev
    exact hodd r hr hr2 hChev
  · intro h34
    have hc := GH74.card_of_lieModel_PSL (G := S) (n := 3) (p := 2) (f := 2) (by norm_num) h34
    rw [ordA_two_four] at hc
    omega
  · intro hHe
    exact hN2.1 (hord.trans ((hO S).1 hHe))
  · intro hM12
    exact hN2.2.1 (hord.trans ((hO S).2.1 hM12))
  · intro hJ2
    exact hN2.2.2 (hord.trans ((hO S).2.2.1 hJ2))

theorem inSA_of_alternating (hL : ResidualNotChevOdd) (hA8 : A8NotL34) (hO : SporadicOrders)
    {S : Type} [Group S] [Finite S] {n : ℕ} (hn : 8 ≤ n) (e : S ≃* alternatingGroup (Fin n)) :
    InSA S := by
  haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hcard : Nat.card S = n.factorial / 2 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  obtain ⟨hHe, hM12, hJ2⟩ := factorial_div_two_ne_orders n hn
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inr (Or.inl ⟨n, by omega, ⟨e⟩⟩)
  · rw [hcard]
    have h8 : Nat.factorial 8 / 2 ≤ n.factorial / 2 :=
      Nat.div_le_div_right (Nat.factorial_le hn)
    have hv : Nat.factorial 8 / 2 = 20160 := by decide
    rw [hv] at h8
    exact h8
  · intro r hr hr2 hChev
    exact hL S r hr hr2 hChev (Or.inl ⟨n, hn, ⟨e⟩⟩)
  · intro h34
    exact (hA8 S h34 n (by omega)).false e
  · intro hs
    exact hHe (by rw [← hcard]; exact (hO S).1 hs)
  · intro hs
    exact hM12 (by rw [← hcard]; exact (hO S).2.1 hs)
  · intro hs
    exact hJ2 (by rw [← hcard]; exact (hO S).2.2.1 hs)

theorem inSA_of_hs (hL : ResidualNotChevOdd) (hO : SporadicOrders) {S : Type} [Group S]
    [Finite S] (h : NativeSporadic.IsSporadic S .HS) : InSA S := by
  refine inSA_of_order hO (GH74.catalog_of_isSporadic h) (N := 44352000) ?_ (by norm_num)
    (by norm_num) ?_
  · exact ((hO S).2.2.2 h).symm
  · intro r hr hr2 hChev
    exact hL S r hr hr2 hChev (Or.inr (Or.inl h))

theorem inSA_of_evenLie (hL : ResidualNotChevOdd) (hO : SporadicOrders) (hG : G2FourOrder)
    {S : Type} [Group S] [Finite S]
    (h : LieModel S .PSp 2 2 2 ∨ LieModel S .PSL 5 2 1 ∨ LieModel S .PSU 5 2 1 ∨
      LieModel S .G2 0 2 2 ∨ LieModel S .PSL 4 2 2) : InSA S := by
  rcases h with hSp | hPSL5 | hPSU5 | hG2 | hPSL4
  · refine inSA_of_order hO (GH74.catalog_of_lieModel hSp) (N := 979200) ?_ (by norm_num)
      (by norm_num) ?_
    · have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
        (GH74.statedClassicalModel_of_lieModel (G := S) (n := 2) (p := 2) (f := 2)
          (by norm_num) hSp)).2.2.1 rfl
      rw [hc]
      decide
    · intro r hr hr2 hChev
      exact hL S r hr hr2 hChev (Or.inr (Or.inr (Or.inl hSp)))
  · refine inSA_of_order hO (GH74.catalog_of_lieModel hPSL5) (N := 9999360) ?_ (by norm_num)
      (by norm_num) ?_
    · rw [GH74.card_of_lieModel_PSL (G := S) (n := 5) (p := 2) (f := 1) (by norm_num) hPSL5]
      decide
    · intro r hr hr2 hChev
      exact hL S r hr hr2 hChev (Or.inr (Or.inr (Or.inr (Or.inl hPSL5))))
  · refine inSA_of_order hO (GH74.catalog_of_lieModel hPSU5) (N := 13685760) ?_ (by norm_num)
      (by norm_num) ?_
    · have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two
        (GH74.statedClassicalModel_of_lieModel (G := S) (n := 5) (p := 2) (f := 1)
          (by norm_num) hPSU5)).2.1 rfl
      rw [hc]
      decide
    · intro r hr hr2 hChev
      exact hL S r hr hr2 hChev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hPSU5)))))
  · refine inSA_of_order hO (GH74.catalog_of_lieModel hG2) (N := 251596800) ?_ (by norm_num)
      (by norm_num) ?_
    · exact (hG S hG2).symm
    · intro r hr hr2 hChev
      exact hL S r hr hr2 hChev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hG2))))))
  · refine inSA_of_order hO (GH74.catalog_of_lieModel hPSL4) (N := 987033600) ?_ (by norm_num)
      (by norm_num) ?_
    · rw [GH74.card_of_lieModel_PSL (G := S) (n := 4) (p := 2) (f := 2) (by norm_num) hPSL4]
      decide
    · intro r hr hr2 hChev
      exact hL S r hr hr2 hChev (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hPSL4))))))

end CFSG.OddStandard.SmallF3.HypA2
