module

public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2G4OB
public import CFSG.ClassicalInvolution.Q3.TL4Mdl264OB
public import CFSG.ClassicalInvolution.RouteD.TwinSmallWitt

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.Orthogonal
  CFSG.RankThree.Classical2 CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Model1520Aux CFSG.LieType.Universal.Spin
  QuadraticMap

theorem noFourPairs_coordinateQuadMinus {K : Type} [Field K] [Finite K] (hK : Nat.card K = 3)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hn : 1 ≤ 4) :
    ∀ P : Fin 4 → HypPair (coordinateQuadMinus 4 K hn b c),
      (∀ i j, i ≠ j → (P i).Orth (P j)) → False := by
  intro P hP
  set ι := (coordinateMinusIsometry 4 K hn b c).symm with hι
  have hpol : ∀ u v, polar (quadMinus 4 K b c) (ι u) (ι v) =
      polar (coordinateQuadMinus 4 K hn b c) u v := fun u v => by
    have hadd : ι (u + v) = ι u + ι v := ι.toLinearEquiv.map_add u v
    rw [polar, polar, ← hadd, ι.map_app, ι.map_app, ι.map_app]
  let P' : Fin 4 → HypPair (quadMinus 4 K b c) := fun i =>
    { e := ι (P i).e
      f := ι (P i).f
      Q_e := by rw [ι.map_app]; exact (P i).Q_e
      Q_f := by rw [ι.map_app]; exact (P i).Q_f
      polar_ef := by rw [hpol]; exact (P i).polar_ef }
  refine CFSG.ClassicalInvolution.RouteD.TwinSmall.false_of_pairs_minus hirr
    (by rw [hK]; decide) (by norm_num) P' (fun i j hij => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hP i j hij
  exact ⟨by rw [hpol]; exact h1, by rw [hpol]; exact h2, by rw [hpol]; exact h3,
    by rw [hpol]; exact h4⟩

theorem false_of_sPHyp_POmegaOdd {S : Type} [Group S] {n : ℕ} (hn : 3 ≤ n)
    (hS : LieModel S .POmegaOdd n 3 1) {A B : Subgroup S} {r : S} {x : MulAut S}
    (h : SPHyp A B r x) : False := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨-, -, hC⟩ : StatedLieTag.POmegaOdd ∈ classicalTags ∧
      StatedClassicalModel S .POmegaOdd n 3 1 := by
    rcases hS with h | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 hn0
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hC
  have hK3 : Nat.card K = 3 := by simpa using hK
  obtain ⟨θ, hθ, hker⟩ := TL4.O264.exists_theta (e.trans (oddProjEquiv n (by omega)))
  have hQ := (regular_coordinateQuadOdd n K (two_ne_zero_of_card_eq_three hK3) hn).1
  refine false_of_sPHyp_orth' (V := Fin (2 * n + 1) → K) hK3 hQ ?_ (Or.inl ?_) hθ hker h
  · rw [Module.finrank_fin_fun]
    omega
  · rw [Module.finrank_fin_fun]
    exact odd_two_mul_add_one n

theorem false_of_sPHyp_POmegaMinus4 {S : Type} [Group S] (hS : LieModel S .POmegaMinus 4 3 1)
    {A B : Subgroup S} {r : S} {x : MulAut S} (h : SPHyp A B r x) : False := by
  obtain ⟨-, -, hC⟩ : StatedLieTag.POmegaMinus ∈ classicalTags ∧
      StatedClassicalModel S .POmegaMinus 4 3 1 := by
    rcases hS with h | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · exact h
    all_goals exact absurd h0 (by norm_num)
  obtain ⟨K, _, _, hK, b, c, hirr, ⟨e⟩⟩ := hC
  have hK3 : Nat.card K = 3 := by simpa using hK
  obtain ⟨θ, hθ, hker⟩ :=
    TL4.O264.exists_theta (e.trans (minusProjEquiv 4 (by omega) b c (by omega)))
  have hQ := (regular_coordinateQuadMinus 4 K b c le_rfl hirr).1
  refine false_of_sPHyp_orth' (V := Fin (2 * 4) → K) hK3 hQ ?_
    (Or.inr ⟨?_, noFourPairs_coordinateQuadMinus hK3 hirr _⟩) hθ hker h
  · rw [Module.finrank_fin_fun]
    omega
  · rw [Module.finrank_fin_fun]

end CFSG.ClassicalInvolution.Q3.TL4.Z2W.G4
