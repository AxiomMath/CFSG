module

public import CFSG.ClassicalInvolution.Q3.Q3TCD4Clique
public import CFSG.ClassicalInvolution.RouteD.ExoticD4TwinModel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TP

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.RouteD.NonClassical CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Asc77.T3CII
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)


theorem eq_of_map_eq_fund3
    (hpow : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 4 (GaloisField 3 1) (by norm_num)), Pow3 R)
    (hker2 : ∀ x ∈ (spinAction (quadPlus 4 (GaloisField 3 1))).ker, x * x = 1)
    {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1)))}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)))
    (h : R.map (spinAction (quadPlus 4 (GaloisField 3 1))) =
      R'.map (spinAction (quadPlus 4 (GaloisField 3 1)))) : R = R' :=
  eq_of_map_eq_of_pow3 (spinAction (quadPlus 4 (GaloisField 3 1)))
    (ker_spinAction_le_center _)
    (fun z hz h3 =>
      absurd (h3.trans (orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hker2 z hz)))
        (by norm_num))
    (hpow R hR) (hpow R' hR') h

section Partner

variable (hodd : Odd (Nat.card (GaloisField 3 1)))
  (hpow : ∀ R ∈ fundamentalSubgroups .POmegaPlus
    (plusDatum 4 (GaloisField 3 1) (by norm_num)), Pow3 R)
  (hker2 : ∀ x ∈ (spinAction (quadPlus 4 (GaloisField 3 1))).ker, x * x = 1)

include hodd hpow hker2

theorem eq_node_two_or_three3
    {X : Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1)))}
    (hX : X ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)))
    (hX' : IsFundSpin X ((d4Frame (GaloisField 3 1) 2).La (-1))) :
    X = d4Node (GaloisField 3 1) 2 ∨ X = d4Node (GaloisField 3 1) 3 := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨fr', hfr', hi'⟩ := hX'
  rcases Frame.La_range_eq_or_eq_swap h2 hi'.symm with h | h
  · exact Or.inl (eq_of_map_eq_fund3 hpow hker2 hX (d4Node_mem 2)
      (hfr'.trans (h.trans (map_rankOne_d4 (GaloisField 3 1) 2).symm)))
  · refine Or.inr (eq_of_map_eq_fund3 hpow hker2 hX (d4Node_mem 3) (hfr'.trans (h.trans ?_)))
    rw [map_rankOne_d4, d4Frame_three]

theorem eq_node_three_of_twin3
    {X : Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1)))}
    (hX : X ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)))
    {i : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1] (Fin 4 ⊕ Fin 4 → GaloisField 3 1)}
    (h : IsFundSpin (d4Node (GaloisField 3 1) 2) i) (hX' : IsFundSpin X i)
    (hne : X ≠ d4Node (GaloisField 3 1) 2) : X = d4Node (GaloisField 3 1) 3 := by
  obtain rfl := eq_La_neg_one_of_node hodd 2 h
  exact (eq_node_two_or_three3 hodd hpow hker2 hX hX').resolve_left hne

theorem eq_node_two_or_three_of_opp3
    {X : Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1)))}
    (hX : X ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)))
    {i i' : (Fin 4 ⊕ Fin 4 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 4 ⊕ Fin 4 → GaloisField 3 1)}
    (h : IsFundSpin (d4Node (GaloisField 3 1) 0) i) (hX' : IsFundSpin X i')
    (hprod : i * i' = LinearEquiv.neg (GaloisField 3 1)) :
    X = d4Node (GaloisField 3 1) 2 ∨ X = d4Node (GaloisField 3 1) 3 := by
  have h2 : (2 : GaloisField 3 1) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain rfl := eq_La_neg_one_of_node hodd 0 h
  obtain rfl : i' = (d4Frame (GaloisField 3 1) 2).La (-1) :=
    mul_left_cancel (hprod.trans (d4Frame_zero_mul_two (GaloisField 3 1) h2).symm)
  exact eq_node_two_or_three3 hodd hpow hker2 hX hX'

theorem twin_partner_spin_plus3
    (hsingle : FundamentalSingleClass .POmegaPlus
      (plusDatum 4 (GaloisField 3 1) (by norm_num)))
    (hlong : ∀ k : Fin 4,
      IsLongestRoot (plusDatum 4 (GaloisField 3 1) (by norm_num)) (Pi.single k 1))
    {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField 3 1)))}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 (GaloisField 3 1) (by norm_num)))
    (hne : R ≠ R') (hcomm : Commutes R R') : HasLinearPartner (GaloisField 3 1) R R' := by
  obtain ⟨i, i', hi, hi', hdich⟩ := exists_inv_of_commutes hodd hsingle hlong hR hR' hcomm
  have hcon : ∀ (k : Fin 4) (g : spinGroup (quadPlus 4 (GaloisField 3 1))),
      R = conjSub g (d4Node (GaloisField 3 1) k) →
      conjSub g⁻¹ R = d4Node (GaloisField 3 1) k := fun k g hg => by
    rw [hg, conjSub_inv_conjSub]
  have hback : ∀ (g : spinGroup (quadPlus 4 (GaloisField 3 1))) (k : Fin 4),
      conjSub g⁻¹ R' = d4Node (GaloisField 3 1) k →
      R' = conjSub g (d4Node (GaloisField 3 1) k) := fun g k h => by
    rw [← h, conjSub_conjSub_inv]
  rcases hdich with heq | hopp
  · obtain ⟨g, hg⟩ := hsingle _ (d4Node_mem 2) R hR
    have hRc := hi.conj g⁻¹
    have hR'c := hi'.conj g⁻¹
    rw [hcon 2 g hg] at hRc
    rw [heq] at hR'c
    have hne' : conjSub g⁻¹ R' ≠ d4Node (GaloisField 3 1) 2 := by
      intro h
      apply hne
      have := congrArg (conjSub g) (h.trans (hcon 2 g hg).symm)
      rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
      exact this.symm
    have h3 := eq_node_three_of_twin3 hodd hpow hker2
      (RouteD.conjSub_mem_fundamentalSubgroups hR' g⁻¹) hRc hR'c hne'
    rw [hg, hback g 3 h3]
    exact hasLinearPartner_two_three.conj g
  · obtain ⟨g, hg⟩ := hsingle _ (d4Node_mem 0) R hR
    have hRc := hi.conj g⁻¹
    have hR'c := hi'.conj g⁻¹
    rw [hcon 0 g hg] at hRc
    have hprod : (spinAction (quadPlus 4 (GaloisField 3 1)) g⁻¹ * i *
        (spinAction (quadPlus 4 (GaloisField 3 1)) g⁻¹)⁻¹) *
        (spinAction (quadPlus 4 (GaloisField 3 1)) g⁻¹ * i' *
          (spinAction (quadPlus 4 (GaloisField 3 1)) g⁻¹)⁻¹) =
          LinearEquiv.neg (GaloisField 3 1) := by
      calc _ = spinAction (quadPlus 4 (GaloisField 3 1)) g⁻¹ * (i * i') *
              (spinAction (quadPlus 4 (GaloisField 3 1)) g⁻¹)⁻¹ := by
            group
        _ = _ := by rw [hopp]; exact conj_linearEquiv_neg _
    rcases eq_node_two_or_three_of_opp3 hodd hpow hker2
      (RouteD.conjSub_mem_fundamentalSubgroups hR' g⁻¹) hRc hR'c hprod with h | h
    · rw [hg, hback g 2 h]
      exact hasLinearPartner_zero_two.conj g
    · rw [hg, hback g 3 h]
      exact hasLinearPartner_zero_three.conj g

end Partner


theorem twinPartnerFactTwin3 :
    ∀ R ∈ fundamentalSubgroups .POmegaPlus
        (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
      ∀ R' ∈ fundamentalSubgroups .POmegaPlus
          (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D, R ≠ R' → Commutes R R' →
        ∃ R'' ∈ fundamentalSubgroups .POmegaPlus
            (Generic.modelUniv .POmegaPlus 4 3 1 Nat.prime_three).D,
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R'') ∧
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R'' R' := by
  obtain ⟨hn3, hsingle, hlong, -⟩ := plus4_data3
  have hp : Nat.Prime 3 := Nat.prime_three
  have S := ModelFacts.spinCtx3_pOmegaPlus (p := 3) (n := 4) (e := 1) (by norm_num) (by norm_num)
  have hM : Generic.modelUniv .POmegaPlus 4 3 1 hp =
      ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ :=
    (rfl : Generic.modelUniv .POmegaPlus 4 3 1 hp =
      ModelFacts.modelUniv .POmegaPlus 4 3 1 hp).trans (ModelFacts.modelUniv_POmegaPlus hn3)
  have hpow : ∀ R ∈ fundamentalSubgroups .POmegaPlus
      (Generic.modelUniv .POmegaPlus 4 3 1 hp).D, Pow3 R :=
    (powCop3_model (t := .POmegaPlus) (n := 4) trivial statedLieAdmissible_plus4_three
      (by decide) (by decide)).pow3
  have key : ∀ M : LieUniversal,
      M = ⟨spinGroup (quadPlus 4 (GaloisField 3 1)), plusDatum 4 (GaloisField 3 1) hn3⟩ →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, Pow3 R) →
      ∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ R' ∈ fundamentalSubgroups .POmegaPlus M.D,
        R ≠ R' → Commutes R R' →
        ∃ R'' ∈ fundamentalSubgroups .POmegaPlus M.D,
          (∃ W, LinearBlockStandardPair (GaloisField 3 1) W R R'') ∧
          ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R'' R' := by
    rintro M rfl hpow R hR R' hR' hne hcomm
    exact twin_partner_spin_plus3 S.odd_card hpow S.hker2 hsingle hlong hR hR' hne hcomm
  exact key _ hM hpow

end CFSG.ClassicalInvolution.Q3.Q3TP
