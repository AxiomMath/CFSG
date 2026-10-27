module

public import CFSG.ClassicalInvolution.Asc77.AscC22G13
public import CFSG.ClassicalInvolution.Q3.Q3T6LinEquiv
public import CFSG.ClassicalInvolution.Asc77.AscR10D3a
public import CFSG.ClassicalInvolution.Asc77.AscT3UG2D4
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G

open CFSG
open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Asc77.C22G CFSG.ClassicalInvolution.Disconnected
open CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.ClassicalInvolution.Asc77.T3CII
open scoped MatrixGroups commutatorElement


variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem admissible_psu4_three : StatedLieAdmissible .PSU 4 3 1 :=
  ⟨Fact.out, Nat.one_pos, by norm_num, by simp⟩

theorem PSULayer.injOn_fund3 (P : PSULayer 3 1 Φ)
    {R : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D) :
    ∀ x ∈ R, P.ψ x = 1 → x = 1 := fun x hx hψ =>
  fund_noncentral_modelUniv (p := 3) (e := 1) (t := .PSU) (n := 4) (by trivial)
    admissible_psu4_three (by rintro ⟨h, -⟩; cases h) R hR x hx
    (P.ker_le (MonoidHom.mem_ker.mpr hψ))

theorem PSULayer.oddCoreOf_fund3 [Finite X] (P : PSULayer 3 1 Φ) {L : Subgroup X}
    {R : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
    (hR : R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    (hLR : L = R.map P.ψ) : oddCoreOf L = ⊥ := by
  have have_fin : Finite (modelUniv .PSU 4 3 1 Fact.out).K :=
    ModelFacts.finite_modelUniv (by norm_num) Fact.out (by trivial) admissible_psu4_three
  obtain ⟨eR⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (by norm_num)
    (t := .PSU) (n := 4) (by trivial) admissible_psu4_three (by decide) (by decide) hR
  have hF : Nat.card (GaloisField 3 1) = 3 := by simpa using GaloisField.card 3 1 one_ne_zero
  have hodd : Odd (Nat.card (GaloisField 3 1)) := by rw [hF]; decide
  have hx : P.ψ (sl2Inv eR) ∈ R.map P.ψ := Subgroup.mem_map_of_mem _ (sl2Inv_mem eR)
  have hx2 : orderOf (P.ψ (sl2Inv eR)) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, sq, sl2Inv_mul_self hodd eR, map_one]
    · intro h
      exact sl2Inv_ne_one hodd eR (PSULayer.injOn_fund3 P hR _ (sl2Inv_mem eR) h)
  have hbot := Q3T6.classicalInvolutionOddCore_map_eq_bot_of_card_three hF P.ψ eR ⟨_, hx, hx2⟩
  unfold oddCoreOf
  rw [hLR, hbot, Subgroup.map_bot]

structure PsuLayerApi3 : Prop where
  pair : ∀ {X : Type} [Group X] {Φ : Set (Subgroup X)} (P : PSULayer 3 1 Φ)
      {K K' L : Subgroup X}
      {RK RK' RL : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
      (_ : RK ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
      (_ : RL ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
      (_ : K = RK.map P.ψ) (_ : K' = RK'.map P.ψ) (_ : L = RL.map P.ψ) {z t e a b : X}
      (_ : IsUniqueInvolution K z) (_ : IsUniqueInvolution L t) (_ : a ∈ K) (_ : b ∈ K')
      (_ : a * a = z) (_ : Commutes K K') (_ : e ∈ omegaGen Φ)
      (_ : ∀ y ∈ omegaGen Φ, e * y = y * e) (_ : t = a * b * e) (_ : K ≠ L)
      (_ : ¬ Commutes K L),
      (∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W RK RL) ∧
        ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W K L
  sup : ∀ {X : Type} [Group X] {Φ : Set (Subgroup X)} (P : PSULayer 3 1 Φ)
      {K J J' : Subgroup X}
      {RK RJ RJ' : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
      (_ : RJ' ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
      (_ : K = RK.map P.ψ) (_ : J = RJ.map P.ψ) (_ : J' = RJ'.map P.ψ)
      (_ : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W RJ' RK)
      (_ : ∃ W, Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W RK RJ)
      (_ : Commutes J J'), J' ⊔ K ⊔ J = omegaGen Φ

theorem PSULayer.sup_eq_of_chain3 (api : PsuLayerApi3) (P : PSULayer 3 1 Φ)
    {K K' L L' : Subgroup X}
    {RK RK' RL RL' : Subgroup (modelUniv .PSU 4 3 1 Fact.out).K}
    (hRK : RK ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    (hRL : RL ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    (hRL' : RL' ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Fact.out).D)
    (hKR : K = RK.map P.ψ) (hKR' : K' = RK'.map P.ψ) (hLR : L = RL.map P.ψ)
    (hL'R : L' = RL'.map P.ψ) {z t e a b : X} (hzK : IsUniqueInvolution K z)
    (htL : IsUniqueInvolution L t) (htL' : IsUniqueInvolution L' t) (ha : a ∈ K) (hb : b ∈ K')
    (haa : a * a = z) (hcomm : Commutes K K') (hcomm' : Commutes L L')
    (he : e ∈ omegaGen Φ) (hec : ∀ y ∈ omegaGen Φ, e * y = y * e) (htab : t = a * b * e)
    (hne : K ≠ L) (hnc : ¬ Commutes K L) (hne' : K ≠ L') (hnc' : ¬ Commutes K L') :
    L' ⊔ K ⊔ L = omegaGen Φ := by
  obtain ⟨h1, -⟩ := api.pair P hRK hRL hKR hKR' hLR hzK htL ha hb haa hcomm he hec htab hne hnc
  obtain ⟨⟨W₁, hW₁⟩, -⟩ := api.pair P hRK hRL' hKR hKR' hL'R hzK htL' ha hb haa hcomm he hec htab
    hne' hnc'
  exact api.sup P hRL' hKR hLR hL'R ⟨W₁, Generic.unitaryBlockStandardPair_symm hW₁⟩ h1 hcomm'

open CFSG.ClassicalInvolution.Models (suMat det_suMat) in
theorem UnitaryBlockStandardPair.eq_one_of_centralizes3 {W U V : Subgroup X}
    (h : Phan.UnitaryBlockStandardPair (GaloisField 3 2) 3 1 W U V) {x : X} (hx : x ∈ U)
    (hc : ∀ y ∈ V, x * y = y * x) : x = 1 := by
  have hK : Nat.card (GaloisField 3 2) = (3 ^ 1) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 3 1 le_rfl
  obtain ⟨θ, -, hker, hU, hV⟩ := Phan.pair_normalize h
  rw [← hU] at hx
  obtain ⟨b, hb, rfl⟩ := hx
  have hcen : Subgroup.center (Phan.Su (GaloisField 3 2) 3 1 3) = ⊥ :=
    center_su3_eq_bot (p := 3) (f := 1) hK (by norm_num)
  have hcomm : ∀ g ∈ Phan.B23 (GaloisField 3 2) 3 1, b * g = g * b := by
    intro g hg
    have hmem : b * g * b⁻¹ * g⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker]
      have := hc (θ g) (hV ▸ Subgroup.mem_map_of_mem θ hg)
      simp only [map_mul, map_inv]
      rw [this]
      group
    have h1 := hker hmem
    rw [hcen, Subgroup.mem_bot] at h1
    calc b * g = (b * g * b⁻¹ * g⁻¹) * (g * b) := by group
      _ = g * b := by rw [h1, one_mul]
  obtain ⟨A, rfl⟩ := hb
  have hr : embSUid (unitaryInvolution (GaloisField 3 2) 3 1) 0
      (Phan.rotSU (unitaryInvolution (GaloisField 3 2) 3 1)) ∈ Phan.B23 (GaloisField 3 2) 3 1 :=
    ⟨_, rfl⟩
  have h1 := congrArg suMat (hcomm _ hr)
  simp only [Models.suMat_mul] at h1
  have hA : suMat A = 1 := embPair_two_eq_one_of_commute_rot _ (det_suMat A) h1
  have : A = 1 := Models.suMat_injective (by rw [hA, Models.suMat_one])
  rw [this, map_one, map_one]

theorem not_three_dvd_card_center_of_oddCore_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hY : classicalInvolutionOddCore Y = ⊥) : ¬ 3 ∣ Nat.card (Subgroup.center Y) := by
  intro h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center Y)) 3 h3
  have hgY : (g : Y) ∈ Subgroup.center Y := g.2
  have hN : (Subgroup.zpowers (g : Y)).Normal := ⟨fun n hn x => by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
    have hc : Commute x (g : Y) := Subgroup.mem_center_iff.mp hgY x
    rw [(hc.zpow_right m).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) m⟩
  have hodd : Odd (Nat.card (Subgroup.zpowers (g : Y))) := by
    rw [Nat.card_zpowers]
    have : orderOf (g : Y) = 3 := by rw [← hg]; exact (Subgroup.orderOf_coe g)
    rw [this]
    decide
  have hle : Subgroup.zpowers (g : Y) ≤ classicalInvolutionOddCore Y := le_sSup ⟨hN, hodd⟩
  rw [hY, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  have : orderOf (g : Y) = 1 := by rw [hle, orderOf_one]
  have h3' : orderOf (g : Y) = 3 := by rw [← hg]; exact (Subgroup.orderOf_coe g)
  omega

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.C22G
