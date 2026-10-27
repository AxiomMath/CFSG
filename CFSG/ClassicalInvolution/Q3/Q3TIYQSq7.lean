module

public import CFSG.ClassicalInvolution.Q3.Q3TIYQGlue
public import CFSG.ClassicalInvolution.Q3.Q3TIYPMinSq
public import CFSG.ClassicalInvolution.Q3.Q3TIYRk4
public import CFSG.ClassicalInvolution.Q3.Q3TIYPOutGlue
public import CFSG.ClassicalInvolution.Q3.Q3TLKOdd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD.TWZ
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.ClassicalInvolution.Q3.Q3TLK
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Exotic CFSG.ClassicalInvolution.ModelFacts.OrthAut
  CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.Q3 (CompData)

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups


theorem framesPlus3_zero : framesPlus 3 0 = 1152 := by norm_num [framesPlus]

theorem framesOdd3_zero : framesOdd 3 0 = 51840 := by norm_num [framesOdd]

theorem sqCntLe_odd3 : SqCntLe (CompData.model .POmegaOdd 3) 90 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn3 : 3 ≤ 3 := le_rfl
  have he : 1 ≤ 1 := le_rfl
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, hn3, by norm_num⟩
  have hdim : Module.finrank (GaloisField 3 1) (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField 3 1) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have hctx := spinCtx3_odd (n := 3) hn3
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField 3 1))) := hctx.perfect
  have hY := Q3W.yData3_odd (m := 3) hn3 hadm
  have hcard : Nat.card (GaloisField 3 1) = 3 := Q3W.card_gf3
  obtain ⟨Z', cq⟩ := hctx.cq
  show SqCntLe ⟨spinGroup (quadOdd 3 (GaloisField 3 1)),
    GFund .POmegaOdd (oddDatum 3 (GaloisField 3 1))⟩ 90
  intro X _ θ hθs hθk R R' hR hR' hne x x' hx hx2 hx1 hx' hx'2 hx'1 hxx' α hα4 hαR hαR'
  rcases spin_sq_count3 hctx.hodd hcard hctx.hQ hctx.hrange hctx.hZ hY.cop (by omega) (by omega)
      hctx.hproj hθs hθk (liftSim_quadOdd hp2 hn3 he θ hθk) cq hR hR' hne
      hx hx2 hx1 hx' hx'2 hx'1 hxx' α hα4 hαR hαR' with h | h | ⟨X', hnd, hdimX, hN⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  refine Or.inr (Or.inr ?_)
  have hO : Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := GaloisField 3 1))) =
      framesPlus 3 0 := by
    rw [NonClassical.card_o4, hcard]
    rfl
  have hnd' := nondegenerate_polarBilin_restrict hnd
  have hX5 : Module.finrank (GaloisField 3 1) X' = 2 * (0 + 2) + 1 := by omega
  have hf := card_frame_regular_odd Q3W.odd_gf3 hnd' hX5
  rw [hO, hf, hcard, framesPlus3_zero, framesOdd3_zero] at hN
  have h90 : Nat.card {S : Subgroup (spinGroup (quadOdd 3 (GaloisField 3 1))) //
      S ∈ GFund .POmegaOdd (oddDatum 3 (GaloisField 3 1)) ∧
        ∀ r ∈ S, (α * α) (θ r) = θ r} ≤ 90 := by omega
  exact h90

end CFSG.ClassicalInvolution.Q3.Q3TIY
