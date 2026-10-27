module

public import CFSG.ClassicalInvolution.RouteD.ExoticD4FourModel
public import CFSG.ClassicalInvolution.RouteD.TypeDModel
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6TwinFact
import CFSG.ClassicalInvolution.ModelFacts.FundPerfectMain
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.RouteD.NonClassicalShape
public import CFSG.ClassicalInvolution.RouteD.NonClassicalTwin
public import CFSG.ClassicalInvolution.RouteD.TypeEModel

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.Timmesfeld (edgeD)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Nodes

variable (F : Type) [Field F]

@[expose] noncomputable def d4Frame (k : Fin 4) : OFrame (quadPlus 4 F) :=
  (plusFrame 4 F (by norm_num)).toFrame (rootIdxD_ne 4 (by omega) k) true (rootSignD 4 k)

noncomputable abbrev d4Node (k : Fin 4) : Subgroup (spinGroup (quadPlus 4 F)) :=
  rankOne (plusDatum 4 F (by norm_num)).rootGroup k

theorem map_rankOne_d4 (k : Fin 4) :
    (d4Node F k).map (spinAction (quadPlus 4 F)) = (d4Frame F k).La.range :=
  map_rankOne_plus (by norm_num) k

theorem d4Frame_three : d4Frame F 3 = (d4Frame F 2).swap := rfl

theorem polar_d4Frame_zero_two (X Y : Matrix (Fin 2) (Fin 2) F) :
    polar (quadPlus 4 F) ((d4Frame F 0).incl X) ((d4Frame F 2).incl Y) = 0 :=
  polar_incl_toFrame_of_disjoint (plusFrame 4 F (by norm_num)) _ _ (by decide) (by decide)
    (by decide) (by decide) _ _ _ _ X Y

theorem d4Frame_zero_mul_two (h2 : (2 : F) ≠ 0) :
    (d4Frame F 0).La (-1) * (d4Frame F 2).La (-1) = LinearEquiv.neg F :=
  Exotic.La_neg_one_mul_of_orth h2
    (by rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin])
    (polar_d4Frame_zero_two F)

end Nodes

section Involutions

variable {F : Type} [Field F]

@[expose] def IsFundSpin (R : Subgroup (spinGroup (quadPlus 4 F)))
    (i : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)) : Prop :=
  IsFundamental (quadPlus 4 F) (R.map (spinAction (quadPlus 4 F))) i

theorem IsFundSpin.conj {R : Subgroup (spinGroup (quadPlus 4 F))}
    {i : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)} (h : IsFundSpin R i)
    (g : spinGroup (quadPlus 4 F)) :
    IsFundSpin (conjSub g R)
      (spinAction (quadPlus 4 F) g * i * (spinAction (quadPlus 4 F) g)⁻¹) := by
  have hθ : spinAction (quadPlus 4 F) g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 4 F) :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr (map_spinAction _ g)
  have := IsFundamental.conj hθ h
  unfold IsFundSpin
  rw [conjSub, CFSG.ClassicalInvolution.ModelFacts.map_conj_map]
  exact this

theorem d4Node_mem (k : Fin 4) :
    d4Node F k ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)) :=
  rankOne_mem_fundamentalSubgroups_plusDatum (by norm_num) k

@[expose] def HasLinearPartner (F : Type) [Field F] (R R' : Subgroup (spinGroup (quadPlus 4 F))) :
    Prop :=
  ∃ R'' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)),
    (∃ W, LinearBlockStandardPair F W R R'') ∧ ∃ W, LinearBlockStandardPair F W R'' R'

theorem HasLinearPartner.conj {R R' : Subgroup (spinGroup (quadPlus 4 F))}
    (h : HasLinearPartner F R R') (g : spinGroup (quadPlus 4 F)) :
    HasLinearPartner F (conjSub g R) (conjSub g R') := by
  obtain ⟨R'', hR'', ⟨W₁, h₁⟩, ⟨W₂, h₂⟩⟩ := h
  exact ⟨conjSub g R'', conjSub_mem_fundamentalSubgroups hR'' g,
    ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj h₁ g⟩,
    ⟨_, CFSG.ClassicalInvolution.ModelFacts.linearBlockStandardPair_map_conj h₂ g⟩⟩

theorem eq_of_map_eq_fund
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)), ⁅R, R⁆ = R)
    {R R' : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    (h : R.map (spinAction (quadPlus 4 F)) = R'.map (spinAction (quadPlus 4 F))) : R = R' :=
  Gaps.eq_of_map_eq_of_central _ (ker_spinAction_le_center _) (hperf R hR).ge (hperf R' hR').ge h

theorem conj_linearEquiv_neg {V : Type} [AddCommGroup V] [Module F V] (g : V ≃ₗ[F] V) :
    g * LinearEquiv.neg F * g⁻¹ = LinearEquiv.neg F :=
  LinearEquiv.ext fun v => by simp

variable [Finite F]

theorem eq_La_neg_one_of_node (hodd : Odd (Nat.card F)) (k : Fin 4)
    {i : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)}
    (h : IsFundSpin (d4Node F k) i) : i = (d4Frame F k).La (-1) := by
  unfold IsFundSpin at h
  rw [map_rankOne_d4] at h
  exact IsFundamental.involution_unique hodd (IsFundamental.of_frame _) h |>.symm

theorem exists_inv_of_commutes (hodd : Odd (Nat.card F))
    (hsingle : FundamentalSingleClass .POmegaPlus (plusDatum 4 F (by norm_num)))
    (hlong : ∀ k : Fin 4, IsLongestRoot (plusDatum 4 F (by norm_num)) (Pi.single k 1))
    {R R' : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    (hcomm : Commutes R R') :
    ∃ i i', IsFundSpin R i ∧ IsFundSpin R' i' ∧ (i' = i ∨ i * i' = LinearEquiv.neg F) := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨fr, hfr⟩ := exists_frame_of_mem_fund_plus (by norm_num) hsingle hlong hR
  obtain ⟨fr', hfr'⟩ := exists_frame_of_mem_fund_plus (by norm_num) hsingle hlong hR'
  have hcommθ : ∀ a ∈ R.map (spinAction (quadPlus 4 F)), ∀ b ∈ R'.map (spinAction (quadPlus 4 F)),
      a * b = b * a := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨r', hr', rfl⟩
    rw [← map_mul, ← map_mul, hcomm r hr r' hr']
  have hmem : ∀ A : SL(2, F), fr.La A ∈ R.map (spinAction (quadPlus 4 F)) := fun A =>
    hfr ▸ ⟨A, rfl⟩
  have hmem' : fr'.La (-1) ∈ R'.map (spinAction (quadPlus 4 F)) := hfr' ▸ ⟨-1, rfl⟩
  have hc : fr'.La (-1) * fr.La (-1) = fr.La (-1) * fr'.La (-1) :=
    (hcommθ _ (hmem (-1)) _ hmem').symm
  have hcent : ∀ A : SL(2, F), fr'.La (-1) * fr.La A = fr.La A * fr'.La (-1) := fun A =>
    (hcommθ _ (hmem A) _ hmem').symm
  refine ⟨fr.La (-1), fr'.La (-1), ⟨fr, hfr, rfl⟩, ⟨fr', hfr', rfl⟩, ?_⟩
  rcases Frame.orth_or_eq h2 hc hcent with horth | heq
  · refine Or.inr (Exotic.La_neg_one_mul_of_orth h2 ?_ horth)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  · exact Or.inl heq

end Involutions

section Partner

variable {F : Type} [Field F] [Finite F]

theorem standardPair_d4Node_one_zero :
    ∃ W, LinearBlockStandardPair F W (d4Node F 0) (d4Node F 1) :=
  standardPair_plusDatum_edge (by norm_num) (i := 0) (j := 1) (by unfold edgeD; decide)

theorem standardPair_d4Node_one_two :
    ∃ W, LinearBlockStandardPair F W (d4Node F 1) (d4Node F 2) :=
  standardPair_plusDatum_edge (by norm_num) (i := 1) (j := 2) (by unfold edgeD; decide)

theorem standardPair_d4Node_one_three :
    ∃ W, LinearBlockStandardPair F W (d4Node F 1) (d4Node F 3) :=
  standardPair_plusDatum_edge (by norm_num) (i := 1) (j := 3) (by unfold edgeD; decide)

theorem hasLinearPartner_zero_two : HasLinearPartner F (d4Node F 0) (d4Node F 2) :=
  ⟨d4Node F 1, d4Node_mem 1, standardPair_d4Node_one_zero, standardPair_d4Node_one_two⟩

theorem hasLinearPartner_zero_three : HasLinearPartner F (d4Node F 0) (d4Node F 3) :=
  ⟨d4Node F 1, d4Node_mem 1, standardPair_d4Node_one_zero, standardPair_d4Node_one_three⟩

theorem hasLinearPartner_two_three : HasLinearPartner F (d4Node F 2) (d4Node F 3) := by
  obtain ⟨W, hW⟩ := standardPair_d4Node_one_two (F := F)
  exact ⟨d4Node F 1, d4Node_mem 1, ⟨W, linearBlockStandardPair_symm hW⟩,
    standardPair_d4Node_one_three⟩

theorem eq_node_two_or_three (hodd : Odd (Nat.card F))
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)), ⁅R, R⁆ = R)
    {X : Subgroup (spinGroup (quadPlus 4 F))}
    (hX : X ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    (hX' : IsFundSpin X ((d4Frame F 2).La (-1))) : X = d4Node F 2 ∨ X = d4Node F 3 := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨fr', hfr', hi'⟩ := hX'
  rcases Frame.La_range_eq_or_eq_swap h2 hi'.symm with h | h
  · exact Or.inl (eq_of_map_eq_fund hperf hX (d4Node_mem 2)
      (hfr'.trans (h.trans (map_rankOne_d4 F 2).symm)))
  · refine Or.inr (eq_of_map_eq_fund hperf hX (d4Node_mem 3) (hfr'.trans (h.trans ?_)))
    rw [map_rankOne_d4, d4Frame_three]

theorem eq_node_three_of_twin (hodd : Odd (Nat.card F))
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)), ⁅R, R⁆ = R)
    {X : Subgroup (spinGroup (quadPlus 4 F))}
    (hX : X ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    {i : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)} (h : IsFundSpin (d4Node F 2) i)
    (hX' : IsFundSpin X i) (hne : X ≠ d4Node F 2) : X = d4Node F 3 := by
  obtain rfl := eq_La_neg_one_of_node hodd 2 h
  exact (eq_node_two_or_three hodd hperf hX hX').resolve_left hne

theorem eq_node_two_or_three_of_opp (hodd : Odd (Nat.card F))
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)), ⁅R, R⁆ = R)
    {X : Subgroup (spinGroup (quadPlus 4 F))}
    (hX : X ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    {i i' : (Fin 4 ⊕ Fin 4 → F) ≃ₗ[F] (Fin 4 ⊕ Fin 4 → F)} (h : IsFundSpin (d4Node F 0) i)
    (hX' : IsFundSpin X i') (hprod : i * i' = LinearEquiv.neg F) :
    X = d4Node F 2 ∨ X = d4Node F 3 := by
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  obtain rfl := eq_La_neg_one_of_node hodd 0 h
  obtain rfl : i' = (d4Frame F 2).La (-1) :=
    mul_left_cancel (hprod.trans (d4Frame_zero_mul_two F h2).symm)
  exact eq_node_two_or_three hodd hperf hX hX'

theorem twin_partner_spin_plus (hodd : Odd (Nat.card F))
    (hsingle : FundamentalSingleClass .POmegaPlus (plusDatum 4 F (by norm_num)))
    (hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)), ⁅R, R⁆ = R)
    (hlong : ∀ k : Fin 4, IsLongestRoot (plusDatum 4 F (by norm_num)) (Pi.single k 1))
    {R R' : Subgroup (spinGroup (quadPlus 4 F))}
    (hR : R ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    (hR' : R' ∈ fundamentalSubgroups .POmegaPlus (plusDatum 4 F (by norm_num)))
    (hne : R ≠ R') (hcomm : Commutes R R') : HasLinearPartner F R R' := by
  obtain ⟨i, i', hi, hi', hdich⟩ := exists_inv_of_commutes hodd hsingle hlong hR hR' hcomm
  have hcon : ∀ (k : Fin 4) (g : spinGroup (quadPlus 4 F)), R = conjSub g (d4Node F k) →
      conjSub g⁻¹ R = d4Node F k := fun k g hg => by rw [hg, conjSub_inv_conjSub]
  have hback : ∀ (g : spinGroup (quadPlus 4 F)) (k : Fin 4), conjSub g⁻¹ R' = d4Node F k →
      R' = conjSub g (d4Node F k) := fun g k h => by rw [← h, conjSub_conjSub_inv]
  rcases hdich with heq | hopp
  · obtain ⟨g, hg⟩ := hsingle _ (d4Node_mem 2) R hR
    have hRc := hi.conj g⁻¹
    have hR'c := hi'.conj g⁻¹
    rw [hcon 2 g hg] at hRc
    rw [heq] at hR'c
    have hne' : conjSub g⁻¹ R' ≠ d4Node F 2 := by
      intro h
      apply hne
      have := congrArg (conjSub g) (h.trans (hcon 2 g hg).symm)
      rw [conjSub_conjSub_inv, conjSub_conjSub_inv] at this
      exact this.symm
    have h3 := eq_node_three_of_twin hodd hperf (conjSub_mem_fundamentalSubgroups hR' g⁻¹) hRc hR'c
      hne'
    rw [hg, hback g 3 h3]
    exact hasLinearPartner_two_three.conj g
  · obtain ⟨g, hg⟩ := hsingle _ (d4Node_mem 0) R hR
    have hRc := hi.conj g⁻¹
    have hR'c := hi'.conj g⁻¹
    rw [hcon 0 g hg] at hRc
    have hprod : (spinAction (quadPlus 4 F) g⁻¹ * i * (spinAction (quadPlus 4 F) g⁻¹)⁻¹) *
        (spinAction (quadPlus 4 F) g⁻¹ * i' * (spinAction (quadPlus 4 F) g⁻¹)⁻¹) =
          LinearEquiv.neg F := by
      calc _ = spinAction (quadPlus 4 F) g⁻¹ * (i * i') * (spinAction (quadPlus 4 F) g⁻¹)⁻¹ := by
            group
        _ = _ := by rw [hopp]; exact conj_linearEquiv_neg _
    rcases eq_node_two_or_three_of_opp hodd hperf (conjSub_mem_fundamentalSubgroups hR' g⁻¹) hRc
      hR'c hprod with h | h
    · rw [hg, hback g 2 h]
      exact hasLinearPartner_zero_two.conj g
    · rw [hg, hback g 3 h]
      exact hasLinearPartner_zero_three.conj g

end Partner

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem twinPartnerFactTwin_pOmegaPlus_four (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) :
    TwinPartnerFactTwin p f .POmegaPlus 4 f := by
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  have hn3 : 3 ≤ 4 := by norm_num
  have hadm : StatedLieAdmissible .POmegaPlus 4 p f := ⟨Fact.out, hf, le_rfl⟩
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hM : modelUniv .POmegaPlus 4 p f Fact.out =
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn3⟩ :=
    (rfl : modelUniv .POmegaPlus 4 p f Fact.out =
      CFSG.ClassicalInvolution.ModelFacts.modelUniv .POmegaPlus 4 p f Fact.out).trans
        (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus hn3)
  have hsingle : FundamentalSingleClass .POmegaPlus (modelUniv .POmegaPlus 4 p f Fact.out).D :=
    CFSG.ClassicalInvolution.ModelFacts.fundamentalSingleClass .POmegaPlus 4 p f Fact.out trivial
      hadm (by decide) (by decide)
  have hperf : ∀ R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 4 p f Fact.out).D,
      ⁅R, R⁆ = R := fun R hR =>
    le_antisymm (Subgroup.commutator_le.mpr fun _ hx _ hy =>
      R.mul_mem (R.mul_mem (R.mul_mem hx hy) (R.inv_mem hx)) (R.inv_mem hy))
      (CFSG.ClassicalInvolution.ModelFacts.fundPerfect_core .POmegaPlus 4 p f hp2 trivial hadm
        (by omega) R hR)
  have hlong : ∀ k : Fin (modelUniv .POmegaPlus 4 p f Fact.out).D.rank,
      IsLongestRoot (modelUniv .POmegaPlus 4 p f Fact.out).D (Pi.single k 1) := fun k =>
    CFSG.ClassicalInvolution.ModelFacts.isLongestRoot_single .POmegaPlus 4 p f Fact.out trivial
      hadm k trivial
  have key : ∀ M : LieUniversal,
      M = ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) hn3⟩ →
      FundamentalSingleClass .POmegaPlus M.D →
      (∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ⁅R, R⁆ = R) →
      (∀ k : Fin M.D.rank, IsLongestRoot M.D (Pi.single k 1)) →
      ∀ R ∈ fundamentalSubgroups .POmegaPlus M.D, ∀ R' ∈ fundamentalSubgroups .POmegaPlus M.D,
        R ≠ R' → Commutes R R' →
        ∃ R'' ∈ fundamentalSubgroups .POmegaPlus M.D,
          (∃ W, LinearBlockStandardPair (GaloisField p f) W R R'') ∧
          ∃ W, LinearBlockStandardPair (GaloisField p f) W R'' R' := by
    intro M hM hsingle hperf hlong R hR R' hR' hne hcomm
    subst hM
    exact twin_partner_spin_plus hodd hsingle hperf hlong hR hR' hne hcomm
  intro R hR R' hR' hne hcomm _
  exact key _ hM hsingle hperf hlong R hR R' hR' hne hcomm

end Main

end CFSG.ClassicalInvolution.RouteD.NonClassical
