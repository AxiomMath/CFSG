module

public import CFSG.ClassicalInvolution.Q3.Q3TLKSq
public import CFSG.ClassicalInvolution.Q3.Q3WALoc
public import CFSG.ClassicalInvolution.Q3.Q3TWY1
public import CFSG.ClassicalInvolution.RouteD.TWZSpinModel
public import CFSG.ClassicalInvolution.Q3.Q3VF4Row
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TLK

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TWZ CFSG.ClassicalInvolution.ModelFacts
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Q3.Q3TWY
open CFSG.ClassicalInvolution.Q3 (CompData)


theorem fundNoncentral_model3 {t : StatedLieTag} {n : ℕ} (hft : ModelFacts.IsFundTag t)
    (hadm : StatedLieAdmissible t n 3 1) (hne : ¬ (t = .PSL ∧ n = 2)) :
    ∀ R ∈ (CompData.model t n).fund, ∀ r ∈ R, r ∈ Subgroup.center (CompData.model t n).G →
      r = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro R hR r hr hrc
  refine ModelFacts.fundNoncentral_generic 3 t n 1 hft hadm hne R hR r hr fun y => ?_
  have h1 := Subgroup.mem_center_iff.mp hrc y
  have e : r * y * r⁻¹ * y⁻¹ = 1 := by
    calc r * y * r⁻¹ * y⁻¹ = y * r * r⁻¹ * y⁻¹ := by rw [h1]
      _ = 1 := by group
  rw [e]
  exact one_mem _

theorem sqTrichotomy3_odd :
    SqTrichotomyOn .POmegaOdd (Generic.modelUniv .POmegaOdd 3 3 1 Nat.prime_three) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hn3 : 3 ≤ 3 := le_rfl
  have he : 1 ≤ 1 := le_rfl
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hdim : Module.finrank (GaloisField 3 1)
      (Fin 3 ⊕ Fin 3 ⊕ Unit → GaloisField 3 1) = 7 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
  have : Group.IsPerfect (spinGroup (quadOdd 3 (GaloisField 3 1))) :=
    isPerfect_spinGroup_quadOdd h2 hn3
  have cq := centralQuot3_odd (m := 3) le_rfl
  have hadm : StatedLieAdmissible .POmegaOdd 3 3 1 :=
    ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩
  have hZ3 : ∀ c ∈ Subgroup.center (spinGroup (quadOdd 3 (GaloisField 3 1))),
      ¬ 3 ∣ orderOf c :=
    (powCop3_model (t := .POmegaOdd) (n := 3) trivial hadm (by decide) (by decide)).cop
  show SqTrichotomyOn .POmegaOdd ⟨spinGroup (quadOdd 3 (GaloisField 3 1)),
    oddDatum 3 (GaloisField 3 1)⟩
  intro X _ θ hθs hθk R R' R₂ hR hR' hR₂ hne x x' x₂ hx hx2 hx1 hx' hx'2 hx'1 hxx' hx₂ hx₂2 hx₂1
    α hα4 hαR hαR' hαR₂
  exact spin_sq_trichotomy3 odd_gf3 card_gf3 (nondegenerate_polarBilin_quadOdd 3 _ h2)
    (range_spinAction_quadOdd h2 hn3) (centerScalar_quadOdd h2 hn3) hZ3 (by omega)
    (fun F₁ F₂ h => by
      have := Asc77.finrank_eq_eight_of_proj hodd F₁ F₂ h
      omega)
    (fun F₀ F₁ h => by
      have h1 := Submodule.finrank_mono h
      have h3 := finrank_perp_add_four F₀
      rw [Frame.finrank_span] at h1
      omega)
    hθs hθk (Asc77.liftSim_quadOdd hp2 hn3 he θ hθk) (fun e => cq.map_inj hR hR' e)
    (cq.map_mem R hR) (cq.map_mem R' hR') (cq.inj R hR) (cq.inj R' hR') hne hx hx2 hx1 hx' hx'2
    hx'1 hxx'
    (cq.pow3 R₂ hR₂) (cq.map_mem R₂ hR₂) (cq.inj R₂ hR₂) hx₂ hx₂2 hx₂1 α hα4 hαR hαR' hαR₂

end CFSG.ClassicalInvolution.Q3.Q3TLK
